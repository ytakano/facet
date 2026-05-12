# v3: Alias Tracking と Re-borrow 実装要件

## 概要

v2 で実装した BorrowState の競合チェックを拡張し、**参照の再借用（Re-borrow）** と
**参照経由の書き込み（Write-through-reference）** を型システムに組み込む。

### 要件

| 機能 | 説明 |
|------|------|
| `&*r` | `r: &'a rk T` から shared re-borrow を生成（downgrade） |
| `&mut *r` | `r: &'a mut T` から mutable re-borrow を生成（same-kind） |
| `replace(*r, e)` | `r: &mut T` を通じて値を置換（write-through） |
| `*r = e` (assign) | `r: &mut T` を通じて値を代入（write-through） |

### Alias tracking の方針

- **v3 では alias map を導入しない**（参照変数からの起源変数への逆引き追跡は v4）
- 代わりに `borrow_state` の既存仕組みを活用:
  - `EBorrow RShared (PDeref (PVar r))` → `BEShared r` を追加（r に shared reborrow が掛かっている）
  - `EBorrow RUnique (PDeref (PVar r))` → `BEMut r` を追加（r に mutable reborrow が掛かっている）
- `let` 脱出時の `bs_remove_all (bs_new_entries ...)` が reborrow を自動解放する（v2 の仕組みを流用）

### 既知の制限（v4 に持ち越し）

- `EDeref (EVar r)` で `r` に active reborrow がある場合の読み取りチェックを行わない  
  → `r` を通じた読み取りは reborrow 中も unrestricted 参照なら可能と見なす（sound hole）
- `PDeref (PDeref ...)` 深さ 2 以上の place は型規則なし（構文上は許可するが typing されない）

---

## アーキテクチャ方針

### 設計選択: `place` 型に `PDeref` を追加

`Syntax.v` の `place` を拡張する：

```coq
Inductive place : Type :=
| PVar   : ident -> place
| PDeref : place -> place.   (* NEW: *p を place として使う *)
```

これにより以下が表現可能になる：
- `EBorrow rk (PDeref (PVar r))` — re-borrow（`&*r`, `&mut *r`）
- `EReplace (PDeref (PVar r)) e` — write-through replace（`replace(*r, e)`）
- `EAssign (PDeref (PVar r)) e` — write-through assign（`*r = e`）

---

## 変更が必要なファイル一覧

| ファイル | 変更量 | 内容 |
|----------|--------|------|
| `rocq/theories/TypeSystem/Syntax.v` | 小 | `PDeref` 追加 |
| `rocq/theories/TypeSystem/OperationalSemantics.v` | 中 | `PDeref` eval rules |
| `rocq/theories/TypeSystem/TypingRules.v` | 中 | re-borrow typing rules, borrow_ok rules |
| `rocq/theories/TypeSystem/TypeChecker.v` | 中 | `infer_core`, `borrow_check` の新 case |
| `rocq/theories/TypeSystem/AlphaRenaming.v` | 大 | `expr_alpha` に PDeref case, 各 lemma に case 追加 |
| `rocq/theories/TypeSystem/CheckerSoundness.v` | 中 | 新型規則の soundness |
| `rocq/theories/TypeSystem/BorrowCheckSoundness.v` | 中 | 新 borrow_ok の soundness/completeness |
| `rocq/_CoqProject` | 変更なし | |
| `ocaml/parser.mly` | 小 | `&*r`, `&mut *r` 構文 |
| `ocaml/debruijn.ml` | 小 | `PDeref` の de Bruijn 変換 |
| `ocaml/fir.ml` | 小 | FIR lowering への case 追加 |

---

## 1. Syntax.v の変更

```coq
Inductive place : Type :=
| PVar   : ident -> place
| PDeref : place -> place.
```

`place` に関わる既存の pattern match はすべて `PDeref` case を追加するか、
適切な wildcard で処理する。

---

## 2. OperationalSemantics.v の変更

`place` を評価して変数名を引くヘルパーが必要（または inline で記述）。

### 補助関数 `eval_place`

```coq
(* 評価済み store から place が指す store entry を引く *)
Fixpoint lookup_place (s : store) (p : place) : option store_entry :=
  match p with
  | PVar x   => store_lookup x s
  | PDeref q =>
      match lookup_place s q with
      | Some se =>
          (* se の値が VRef y ならば y の store entry を引く *)
          match se_val se with
          | VRef y => store_lookup y s
          | _      => None
          end
      | None => None
      end
  end.
```

### 新 eval ルール

```coq
(* replace(*r, e_new): r に VRef y が入っている store entry を更新 *)
| Eval_Replace_Deref : forall fenv s s1 s2 r_ident y old_v v_new,
    store_lookup r_ident s = Some (MkStoreEntry r_ident _ (VRef y) false) ->
    eval fenv s1 e_new s2 v_new ->
    store_update y v_new s2 = Some s3 ->
    eval fenv s (EReplace (PDeref (PVar r_ident)) e_new) s3 old_v

(* assign(*r, e_new): 同様 *)
| Eval_Assign_Deref : ...
```

---

## 3. TypingRules.v の変更

### 3-1. 既存規則の PDeref 対応

`T_Replace` と `T_Assign` は現在 `PVar x` のみ。
`PDeref` case は新規規則 `T_Replace_Deref` / `T_Assign_Deref` として追加する。

### 3-2. 新型規則

```coq
(* Shared re-borrow: &*r
   r には任意の参照型を持てる（shared でも mut でも）
   結果型は unrestricted &'static (ty_inner r) *)
| T_ReBorrowShared : forall Γ Γ' r la rk T u_r,
    typed fenv Γ r (MkTy u_r (TRef la rk T)) Γ' ->
    ty_usage T <> ULinear ->
    typed fenv Γ (EBorrow RShared (PDeref (PVar r)))
      (MkTy UUnrestricted (TRef LStatic RShared T)) Γ'

(* Mutable re-borrow: &mut *r
   r は mutable 参照でなければならない *)
| T_ReBorrowMut : forall Γ Γ' r la T u_r,
    typed fenv Γ r (MkTy u_r (TRef la RUnique T)) Γ' ->
    ty_usage T <> ULinear ->
    typed fenv Γ (EBorrow RUnique (PDeref (PVar r)))
      (MkTy UUnrestricted (TRef LStatic RUnique T)) Γ'

(* Replace through mutable reference: replace(*r, e_new)
   r: unrestricted &mut T （r は消費されない）
   結果: 旧値 T を返す *)
| T_Replace_Deref : forall Γ Γ' r T T_new e_new la u_r,
    ctx_lookup r Γ = Some (MkTy u_r (TRef la RUnique T), false) ->
    typed fenv Γ e_new T_new Γ' ->
    ty_core T_new = ty_core T ->
    usage_sub (ty_usage T_new) (ty_usage T) ->
    typed fenv Γ (EReplace (PDeref (PVar r)) e_new) T Γ'

(* Assign through mutable reference: *r = e_new
   T must not be linear (assign discards old value) *)
| T_Assign_Deref : forall Γ Γ' r T T_new e_new la u_r,
    ctx_lookup r Γ = Some (MkTy u_r (TRef la RUnique T), false) ->
    ty_usage T <> ULinear ->
    typed fenv Γ e_new T_new Γ' ->
    ty_core T_new = ty_core T ->
    usage_sub (ty_usage T_new) (ty_usage T) ->
    typed fenv Γ (EAssign (PDeref (PVar r)) e_new) (MkTy UUnrestricted TUnits) Γ'
```

### 3-3. borrow_ok 新規則

```coq
(* Shared re-borrow: &*r — r 自体に mut borrow なし *)
| BO_ReBorrowShared : forall BS Γ r,
    bs_can_shared r BS ->
    borrow_ok fenv BS Γ (EBorrow RShared (PDeref (PVar r))) (BEShared r :: BS)

(* Mutable re-borrow: &mut *r — r に一切の borrow なし *)
| BO_ReBorrowMut : forall BS Γ r,
    bs_can_mut r BS ->
    borrow_ok fenv BS Γ (EBorrow RUnique (PDeref (PVar r))) (BEMut r :: BS)

(* Replace/Assign through reference — r に active reborrow なし *)
| BO_Replace_Deref : forall BS BS' Γ r e_new,
    bs_can_mut r BS ->          (* r が reborrow されていない *)
    borrow_ok fenv BS Γ e_new BS' ->
    borrow_ok fenv BS Γ (EReplace (PDeref (PVar r)) e_new) BS'

| BO_Assign_Deref : forall BS BS' Γ r e_new,
    bs_can_mut r BS ->
    borrow_ok fenv BS Γ e_new BS' ->
    borrow_ok fenv BS Γ (EAssign (PDeref (PVar r)) e_new) BS'
```

---

## 4. TypeChecker.v の変更

### 4-1. `infer_core` への追加

```coq
(* Shared re-borrow: &*r *)
| EBorrow RShared (PDeref (PVar r)) =>
    match ctx_lookup_b r Γ with
    | None => infer_err (ErrUnknownVar r)
    | Some (T, _) =>
        match ty_core T with
        | TRef la rk T_inner =>
            if usage_eqb (ty_usage T_inner) ULinear
            then infer_err (ErrUsageMismatch ULinear ULinear)  (* linear は借用不可 *)
            else infer_ok (Γ, MkTy UUnrestricted (TRef LStatic RShared T_inner))
        | _ => infer_err (ErrNotAReference (ty_core T))
        end
    end

(* Mutable re-borrow: &mut *r *)
| EBorrow RUnique (PDeref (PVar r)) =>
    match ctx_lookup_b r Γ with
    | None => infer_err (ErrUnknownVar r)
    | Some (T, _) =>
        match ty_core T with
        | TRef la RUnique T_inner =>
            if usage_eqb (ty_usage T_inner) ULinear
            then infer_err (ErrUsageMismatch ULinear ULinear)
            else infer_ok (Γ, MkTy UUnrestricted (TRef LStatic RUnique T_inner))
        | TRef la RShared _ => infer_err (ErrImmutableBorrow r)  (* shared は &mut *r 不可 *)
        | _ => infer_err (ErrNotAReference (ty_core T))
        end
    end

(* Replace/Assign through reference *)
| EReplace (PDeref (PVar r)) e_new =>
    match ctx_lookup_b r Γ with
    | None => infer_err (ErrUnknownVar r)
    | Some (T, _) =>
        match ty_core T with
        | TRef _ RUnique T_inner =>
            match infer_core fenv Γ e_new with
            | infer_err err => infer_err err
            | infer_ok (Γ', T_new) =>
                if ty_core_eqb (ty_core T_new) (ty_core T_inner) then
                  if usage_leb (ty_usage T_new) (ty_usage T_inner) then
                    infer_ok (Γ', T_inner)
                  else infer_err (ErrUsageMismatch ...)
                else infer_err (ErrTypeMismatch ...)
            end
        | TRef _ RShared _ => infer_err (ErrImmutableBorrow r)
        | _ => infer_err (ErrNotAReference (ty_core T))
        end
    end

(* Assign through reference は EReplace と同様、返却型は unit *)
| EAssign (PDeref (PVar r)) e_new => ...
```

### 4-2. `borrow_check` への追加

```coq
| EBorrow RShared (PDeref (PVar r)) =>
    if bs_has_mut r BS
    then infer_err (ErrBorrowConflict r)
    else infer_ok (BEShared r :: BS)

| EBorrow RUnique (PDeref (PVar r)) =>
    if bs_has_any r BS
    then infer_err (ErrBorrowConflict r)
    else infer_ok (BEMut r :: BS)

| EReplace (PDeref (PVar r)) e_new
| EAssign  (PDeref (PVar r)) e_new =>
    if bs_has_any r BS
    then infer_err (ErrBorrowConflict r)
    else borrow_check fenv BS Γ e_new
```

---

## 5. AlphaRenaming.v の変更

`expr_alpha` に `PDeref` の case を追加（ネストしない v3 では深さ 1 のみ）：

```coq
| EA_ReBorrowShared : forall ρ r,
    expr_alpha ρ (EBorrow RShared (PDeref (PVar r)))
               (EBorrow RShared (PDeref (PVar (lookup_rename r ρ))))

| EA_ReBorrowMut : forall ρ r,
    expr_alpha ρ (EBorrow RUnique (PDeref (PVar r)))
               (EBorrow RUnique (PDeref (PVar (lookup_rename r ρ))))

| EA_ReplaceDeref : forall ρ r e er,
    expr_alpha ρ e er ->
    expr_alpha ρ (EReplace (PDeref (PVar r)) e)
               (EReplace (PDeref (PVar (lookup_rename r ρ))) er)

| EA_AssignDeref : forall ρ r e er,
    expr_alpha ρ e er ->
    expr_alpha ρ (EAssign (PDeref (PVar r)) e)
               (EAssign (PDeref (PVar (lookup_rename r ρ))) er)
```

各 lemma（`alpha_typed`, `alpha_borrow_ok`, `alpha_eval`, etc.）に PDeref case を追加。

---

## 6. CheckerSoundness.v の変更

新型規則（`T_ReBorrowShared`, `T_ReBorrowMut`, `T_Replace_Deref`, `T_Assign_Deref`）の
soundness / completeness 証明 case を追加。

`infer_core` の新 case は構造上 `T_BorrowShared` / `T_BorrowMut` / `T_Replace` の類似パターンなので
既存証明を参考に証明可能。

---

## 7. BorrowCheckSoundness.v の変更

`borrow_check_sound` / `borrow_check_complete` に新 case を追加:

- `(* EBorrow PDeref RShared *)` ← BO_ReBorrowShared と同様のパターン
- `(* EBorrow PDeref RUnique *)` ← BO_ReBorrowMut
- `(* EReplace PDeref *)` ← BO_Replace_Deref
- `(* EAssign PDeref *)` ← BO_Assign_Deref

また `borrow_check_call_go` の PDeref 処理（call の引数に reborrow が来る場合）も確認。

---

## 8. OCaml フロントエンド変更

### 8-1. `ocaml/ast.ml`

```ocaml
type named_place =
  | NPVar   of string
  | NPDeref of named_place   (* NEW *)
```

### 8-2. `ocaml/parser.mly`

```
(* re-borrow を EBorrow として parse *)
| AMP STAR expr           { EBorrow (RShared, PDeref ...) }
| AMP MUT STAR expr       { EBorrow (RUnique, PDeref ...) }

(* write-through を EReplace/EAssign として parse *)
| REPLACE LPAREN STAR expr COMMA expr RPAREN  { EReplace (PDeref ...) ... }
| STAR expr ASSIGN expr                        { EAssign  (PDeref ...) ... }
```

### 8-3. `ocaml/debruijn.ml`

`convert_place` に `NPDeref p -> PDeref (convert_place p)` を追加。

### 8-4. `ocaml/fir.ml`

FIR lowering に `EReBorrow` / `EWriteDeref` 相当の instruction 追加（省略可）。

---

## 9. テスト追加

### valid/

| ファイル | 内容 |
|----------|------|
| `tests/valid/borrow/reborrow_shared_from_mut.facet` | `let r2 = &*r_mut in` (downgrade) |
| `tests/valid/borrow/reborrow_mut.facet` | `let r2 = &mut *r_mut in` |
| `tests/valid/borrow/write_through_ref.facet` | `replace(*r, new_val)` |
| `tests/valid/borrow/assign_through_ref.facet` | `*r = new_val` |

### invalid/borrow_conflict/

| ファイル | 内容 |
|----------|------|
| `tests/invalid/borrow_conflict/reborrow_mut_blocked_by_shared.facet` | shared reborrow 中に `&mut *r` |
| `tests/invalid/borrow_conflict/double_mut_reborrow.facet` | `&mut *r` が 2 つ |
| `tests/invalid/borrow_conflict/write_through_reborrowed.facet` | reborrow 中に `replace(*r, ...)` |

---

## 実装順序（推奨）

1. `Syntax.v`: `PDeref` 追加（他がコンパイルできるよう先に）
2. `OperationalSemantics.v`: PDeref eval rules
3. `TypingRules.v`: 新型規則 + borrow_ok 新規則
4. `TypeChecker.v`: `infer_core` + `borrow_check` の新 case
5. `AlphaRenaming.v`: `expr_alpha` 新 case + 各 lemma の case 追加（最大の作業）
6. `CheckerSoundness.v`: 新型規則の証明
7. `BorrowCheckSoundness.v`: 新 borrow_ok の証明
8. OCaml フロントエンド更新
9. テスト追加・実行

### リスク

- `AlphaRenaming.v` が最大の作業。現在 ~1400 行あり、lemma ごとに新 case が必要。
- `CheckerSoundness.v` は証明スタイルが複雑（`infer_core` の結果を analysis する分岐が多い）。
- `PDeref` の導入で `Eval_Replace_Deref` の operational semantics が複雑になる  
  （`VRef y` を介して store を 2 段階辿る）。

---

## Soundness holes の整理

| 問題 | 深刻度 | 対応 |
|------|--------|------|
| `EDeref (EVar r)` で r に active mut reborrow があっても読み取れる | 中 | v4 で `borrow_check` に型情報を渡す |
| `EBorrow rk (PDeref (PDeref ...))` (深さ2以上) は型規則なし | 低 | v4 で対応 |
| `EBorrow rk (PDeref _)` の `_` が `PVar` 以外 | 低 | v3 では `PDeref (PVar r)` のみ対象 |
