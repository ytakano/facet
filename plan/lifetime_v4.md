# v4: 再借用フリーズチェック（Re-borrow Freeze Checks）

## 概要

v3 で実装した `PDeref` place と再借用操作に、**フリーズ検査**を追加する。

v3 の既知の制限（soundness hole）:

> `EDeref (EVar r)` で `r` に active mutable re-borrow がある場合の読み取りを遮断していない。
> `EReplace/EAssign (PDeref (PVar r))` で `r` に active re-borrow がある場合の書き込みを遮断していない。

具体的には以下が現在ブロックされない（すべき）操作:

| 状況 | 操作 | 期待 | v3 の振る舞い |
|------|------|------|--------------|
| `BEMut r ∈ BS` (r が `&mut *r` で再借用中) | `*r` (EDeref) | エラー（凍結） | 許可 ← **soundness hole** |
| `BEMut r ∈ BS` | `replace *r e` | エラー | 許可 ← **soundness hole** |
| `BEMut r ∈ BS` | `*r = e` | エラー | 許可 ← **soundness hole** |
| `BEShared r ∈ BS` (r が `&*r` で再借用中) | `replace *r e` | エラー | 許可 ← **soundness hole** |
| `BEShared r ∈ BS` | `*r = e` | エラー | 許可 ← **soundness hole** |
| `BEShared r ∈ BS` | `*r` (EDeref, read) | 許可 | 許可 ✓ |

---

## 設計方針

### 追加する述語

**`bs_has_mut`** (Prop レベル, TypingRules.v):
```coq
Definition bs_has_mut (x : ident) (BS : borrow_state) : Prop :=
  In (BEMut x) BS.
```

**`bs_has_mut_b`** (Bool レベル, TypeChecker.v):
```coq
Definition bs_has_mut_b (x : ident) (BS : borrow_state) : bool :=
  existsb (fun e => match e with BEMut y => ident_eqb y x | _ => false end) BS.
```

**`bs_has_shared_b`** (Bool レベル, TypeChecker.v):
```coq
Definition bs_has_shared_b (x : ident) (BS : borrow_state) : bool :=
  existsb (fun e => match e with BEShared y => ident_eqb y x | _ => false end) BS.
```

**`borrow_ok_deref_check`** (BO_Deref の前提, TypingRules.v):
```coq
(* EDeref e が安全: e = EVar r のとき BEMut r が BS にないこと *)
Definition borrow_ok_deref_check (BS : borrow_state) (e : expr) : Prop :=
  match e with
  | EVar r => ~ In (BEMut r) BS
  | _      => True
  end.
```

### TypingRules.v の変更

**`BO_Deref` を強化**（フリーズ前提を追加）:
```coq
(* 変更前 *)
| BO_Deref : forall BS BS' Γ e,
    borrow_ok fenv BS Γ e BS' ->
    borrow_ok fenv BS Γ (EDeref e) BS'

(* 変更後 *)
| BO_Deref : forall BS BS' Γ e,
    borrow_ok_deref_check BS e ->        (* NEW: r が BEMut されていないこと *)
    borrow_ok fenv BS Γ e BS' ->
    borrow_ok fenv BS Γ (EDeref e) BS'
```

**`BO_Replace_Deref` を強化**（書き込みフリーズ前提を追加）:
```coq
(* 変更後 *)
| BO_Replace_Deref : forall BS BS' Γ r e_new,
    bs_can_mut r BS ->                   (* NEW: r に active re-borrow がない *)
    borrow_ok fenv BS Γ e_new BS' ->
    borrow_ok fenv BS Γ (EReplace (PDeref (PVar r)) e_new) BS'
```

**`BO_Assign_Deref` を強化**（同上）:
```coq
(* 変更後 *)
| BO_Assign_Deref : forall BS BS' Γ r e_new,
    bs_can_mut r BS ->                   (* NEW *)
    borrow_ok fenv BS Γ e_new BS' ->
    borrow_ok fenv BS Γ (EAssign (PDeref (PVar r)) e_new) BS'
```

> 注: `bs_can_mut r BS = ~ In (BEShared r) BS ∧ ~ In (BEMut r) BS` — shared/mut どちらの再借用も書き込みをブロックする。

### TypeChecker.v の変更

**`borrow_check` の `EDeref` case を分割**:
```coq
| EDeref inner =>
    match inner with
    | EVar r =>
        if bs_has_mut_b r BS then infer_err ErrBorrowConflict
        else infer_ok BS           (* inner の評価は typing 側で保証 *)
    | _ => borrow_check fenv BS Γ inner
    end
```

**`EReplace (PDeref (PVar r))` case に書き込みチェックを追加**:
```coq
| EReplace (PDeref (PVar r)) e_new =>
    if bs_has_mut_b r BS || bs_has_shared_b r BS
    then infer_err ErrBorrowConflict
    else borrow_check fenv BS Γ e_new
```

**`EAssign (PDeref (PVar r))` case も同様**。

---

## 変更ファイル一覧

| ファイル | 変更量 | 内容 |
|----------|--------|------|
| `rocq/theories/TypeSystem/TypingRules.v` | 小 | `bs_has_mut`, `borrow_ok_deref_check` 定義; `BO_Deref`/`BO_Replace_Deref`/`BO_Assign_Deref` 強化 |
| `rocq/theories/TypeSystem/TypeChecker.v` | 小 | `bs_has_mut_b`, `bs_has_shared_b` 定義; `borrow_check EDeref`/`EReplace(PDeref)`/`EAssign(PDeref)` 更新 |
| `rocq/theories/TypeSystem/BorrowCheckSoundness.v` | 中 | 新規前提の sound/complete 証明; `bs_has_mut_b_spec` 補題 |
| `ocaml/` | なし（既存の OCaml コードへの影響なし） | — |
| `tests/` | 小 | フリーズチェックの valid/invalid テスト追加 |

**変更しないファイル**: `Syntax.v`, `OperationalSemantics.v`, `AlphaRenaming.v`, `CheckerSoundness.v`, `CheckerUsageSoundness.v`, `WFType.v`

---

## 詳細実装手順

### 1. TypingRules.v

1. `bs_has_mut` を `bs_can_shared` / `bs_can_mut` の近くに追加
2. `borrow_ok_deref_check` を定義（関数: `expr -> borrow_state -> Prop`）
3. `BO_Deref` に `borrow_ok_deref_check BS e` 前提を追加
4. `BO_Replace_Deref` に `bs_can_mut r BS` 前提を追加
5. `BO_Assign_Deref` に `bs_can_mut r BS` 前提を追加

### 2. TypeChecker.v

1. `bs_has_mut_b` / `bs_has_shared_b` を `bs_can_mut_b` の近くに追加
2. `bs_has_mut_b_spec` 補題（`bs_has_mut_b r BS = true <-> In (BEMut r) BS`）を証明
3. `bs_has_shared_b_spec` 補題を証明
4. `borrow_check` の `EDeref` case を変更（EVar r 内側での BEMut チェック）
5. `borrow_check` の `EReplace (PDeref (PVar r))` case に追加チェック
6. `borrow_check` の `EAssign (PDeref (PVar r))` case に追加チェック

### 3. BorrowCheckSoundness.v

`borrow_check_sound` (`borrow_check → borrow_ok`) と `borrow_check_complete` (`borrow_ok → borrow_check`) を更新:

- `BO_Deref` case: `borrow_ok_deref_check` の証明が必要
  - `e = EVar r` のとき: `~ In (BEMut r) BS` を `bs_has_mut_b r BS = false` から導く
  - `e ≠ EVar r` のとき: `borrow_ok_deref_check BS e = True` は自明
- `BO_Replace_Deref` case: `bs_can_mut r BS` の証明
  - `bs_can_mut_b_spec` (既存) を使用して `bs_has_mut_b r BS = false ∧ bs_has_shared_b r BS = false` から導く
- `BO_Assign_Deref` case: 同上

---

## テスト追加

### valid（フリーズが解除された後に使用）

`tests/valid/reborrow/reborrow_then_use_orig.facet`:
```facet
fn f(mut x: unrestricted isize) -> unrestricted isize {
    let mut r: unrestricted &mut unrestricted isize = (&mut x) in
    let r2: unrestricted &mut unrestricted isize = (&mut *r) in
    let _: unrestricted () = (*r2 = 42) in
    (* r2 is out of scope here; BEMut r is released *)
    (* This is the return of r2's let, so r is now free *)
    x
}
```

> 注: v4 時点で let スコープによるフリーズ解除が適切に動作することを確認。

### invalid（フリーズ中のアクセス）

`tests/invalid/reborrow/deref_while_reborrowed_mut.facet`:
```facet
fn f(mut x: unrestricted isize) -> unrestricted isize {
    let mut r: unrestricted &mut unrestricted isize = (&mut x) in
    let mut r2: unrestricted &mut unrestricted isize = (&mut *r) in
    let v: unrestricted isize = (*r) in   (* ERROR: r is frozen by r2 *)
    let _: unrestricted () = (*r2 = 42) in
    v
}
```

`tests/invalid/reborrow/write_while_shared_reborrowed.facet`:
```facet
fn f(mut x: unrestricted isize) -> unrestricted () {
    let mut r: unrestricted &mut unrestricted isize = (&mut x) in
    let _r2: unrestricted &unrestricted isize = (&*r) in
    let _: unrestricted isize = (replace *r 99) in   (* ERROR: shared re-borrow active *)
    ()
}
```

`tests/invalid/reborrow/assign_while_mut_reborrowed.facet`:
```facet
fn f(mut x: unrestricted isize) -> unrestricted () {
    let mut r: unrestricted &mut unrestricted isize = (&mut x) in
    let mut _r2: unrestricted &mut unrestricted isize = (&mut *r) in
    let _: unrestricted () = (*r = 42) in   (* ERROR: mutable re-borrow active *)
    ()
}
```

---

## 既知の制限（v5 に持ち越し）

- **`EDeref (EDeref ...)` チェーン**: `*(*r)` のような二重 deref 時のフリーズチェックは非対応
  → deref chain の起源変数を追跡するには alias map が必要（v5）
- **`EVar r` 自体の使用制限**: re-borrow 中に `r` を別変数にコピーする操作（`let s = r`）はブロックしない
  → `r : unrestricted &mut T` は `unrestricted` なのでコピー可能だが、コピーした参照から書き込むとエイリアスが生じる（v5 で対処）
- **`PDeref (PDeref ...)` depth ≥ 2**: v3 同様 `ErrNotImplemented`
- **`wf_type` との統合**: `WFType.v` は存在するが typing judgment には未組み込み（別 issue）
- **関数引数の参照と dangling reference**: 下記参照

---

## 関数引数の参照と lifetime（dangling reference 問題）

### 現状の soundness hole

現在、以下のプログラムは型チェックを**通過してしまう**:

```facet
fn make_ref(mut x: unrestricted isize) -> unrestricted &unrestricted isize {
    (&x)   (* ローカルパラメータへの参照を返す *)
}
fn g() -> unrestricted isize {
    let r: unrestricted &unrestricted isize = (make_ref 42) in
    (*r)   (* r は make_ref の x を指すが、x は store から削除済み *)
}
```

`Eval_Call` の `store_remove_params` で **パラメータは関数リターン時に store から削除される**。
よって `(*r)` はランタイムで dangling reference となる。

### なぜ LStatic だけでは不十分か

`EBorrow (PVar x)` の result type は現在すべて `TRef LStatic ...` に固定されている。
「`LStatic` = 参照先は常に有効」という意味だが、ローカルパラメータへの参照は
関数リターン後に無効になるため、`LStatic` の意味と矛盾する。

### 正しい設計（v5 の実装目標）

`fn_def` に **lifetime パラメータ数** を追加し、`typed` 判断に **region context** を組み込む:

```coq
Record fn_def : Type := {
  fn_name      : ident;
  fn_lifetimes : nat;        (* lifetime パラメータ数。'a, 'b, ... = LVar 0, LVar 1, ... *)
  fn_params    : list param; (* 型中に LVar n を使える *)
  fn_ret       : Ty;
  fn_body      : expr;
}.

(* typed 判断に region_ctx を追加 *)
typed fenv Δ Γ e T Γ' : Prop
```

`EBorrow (PVar x)` でのライフタイム割り当て:
- **パラメータの変数への borrow** → 対応する lifetime パラメータ `LVar i` を使う
- **ローカル変数 (ELet で束縛) への borrow** → スコープに閉じた新しい `LVar k` を生成

`wf_type Δ T` の強制: return type に含まれるすべての `TRef l ...` の `l` は `Δ` に属さなければならない。
→ `(&x)` を返す関数は `wf_type` 違反（`x` のライフタイムは関数スコープの LVar で Δ 外）として弾かれる。

### 関数シグネチャの例（v5 後の形式）

| ソース | lifetime パラメータ | param 型 | return 型 |
|--------|-------------------|----------|-----------|
| `fn f<'a>(r: &'a T) -> &'a T` | `fn_lifetimes = 1` | `TRef (LVar 0) RShared T` | `TRef (LVar 0) RShared T` |
| `fn f<'a,'b>(r: &'a T, s: &'b T) -> &'a T` | `fn_lifetimes = 2` | … | `TRef (LVar 0) ...` |
| `fn f(mut x: T) -> &T` | 0 | — | REJECTED: local LVar not in Δ |

### v4 への影響

v4 の freeze checks は borrow_state の検査のみで lifetime には依存しない。
**v4 の実装計画は変更不要**。

> **v4 での注記**: `fn f(mut x: T) -> &T { (&x) }` は引き続き型チェックを通過する（soundness hole）。
> 本問題は v5 の lifetime パラメータ導入で対処する。

---

## 正確なフリーズ意味論（参考）

再借用のフリーズルール（Rust の NLL を単純化）:

```
r : &'a rk T

BEShared r ∈ BS の間:
  ✓ *r (EDeref, read) — 読み取り可
  ✗ replace *r e     — 書き込み不可
  ✗ *r = e           — 書き込み不可
  ✓ &*r (shared re-borrow) — 追加の shared re-borrow は可
  ✗ &mut *r          — mutable re-borrow 不可（bs_can_mut で既にブロック済）

BEMut r ∈ BS の間:
  ✗ *r (EDeref)      — 読み取り不可（完全凍結）
  ✗ replace *r e     — 書き込み不可
  ✗ *r = e           — 書き込み不可
  ✗ &*r              — shared re-borrow 不可（bs_can_shared で既にブロック済）
  ✗ &mut *r          — mutable re-borrow 不可（bs_can_mut で既にブロック済）
```

v3 でブロック済みの操作（再確認):
- `&*r` when `BEMut r ∈ BS` → `BO_ReBorrowShared` の `bs_can_shared r BS` でブロック ✓
- `&mut *r` when `BEShared r ∈ BS` or `BEMut r ∈ BS` → `BO_ReBorrowMut` の `bs_can_mut r BS` でブロック ✓

v4 で新たにブロックする操作:
- `*r` (EDeref) when `BEMut r ∈ BS` → `BO_Deref` の `borrow_ok_deref_check` ✦ **NEW**
- `replace *r e` when `BEShared r ∈ BS` or `BEMut r ∈ BS` → `BO_Replace_Deref` の `bs_can_mut r BS` ✦ **NEW**
- `*r = e` when `BEShared r ∈ BS` or `BEMut r ∈ BS` → `BO_Assign_Deref` の `bs_can_mut r BS` ✦ **NEW**
