# Borrow 式 v1 実装要件

## 概要

v0 で確立した lifetime 基盤の上に、借用式の**構文・型付け・実行意味論**を追加する。
BorrowState（借用競合チェック）は v2 のスコープ。

---

## Goal

- `EBorrow` / `EDeref` を `Syntax.v` に追加
- `VRef` を `OperationalSemantics.v` に追加し、実行時の参照値を表現する
- `T_Borrow` / `T_Deref` を `TypingRules.v` に追加
- `TypeChecker.v` に対応する推論ケースを追加
- `AlphaRenaming.v` / `CheckerSoundness.v` を更新
- OCaml パーサーに `&x` / `&mut x` / `(*e)` の構文を追加

## Non-goals（スコープ外）

- BorrowState による借用競合チェック（v2）
- lifetime 変数（`LVar n`）の推論・割り当て（全参照は `LStatic` を使用）
- Re-borrow（v3）
- safety theorem（v4）
- `&*r`（re-borrow / 参照の dereference して borrow）

---

## 設計上の決定事項

### Lifetime の扱い
v1 では全ての borrowing に `LStatic` を使う。
`LVar n` の割り当ては lifetime inference が確立してから追加する。

### Borrow は変数を消費しない
`T_Borrow` は `x` を消費しない（`consumed` フラグを変えない）。
これは borrow の基本的な意味論（参照を作っても所有権は移らない）と一致する。

### VRef の表現
参照は実行時に「参照先の変数名（`ident`）」を保持する `VRef` として表現する。
ストアは今後も値を直接保持するため、`VRef x` は「ストア中の `x` の現在の値を指す」という意味になる。

### Deref の返す usage（Rust 意味論に準拠）

Rust では `*r` で inner type が affine/linear でも所有権は**移らない**。
参照を通して値を move out することはできず、`mem::replace` 等の代替手段が必要。

よって Facet でも同様とする：

- `EDeref` は **`UUnrestricted`（コピー可能）な inner type にのみ適用可能**
- `T_Deref` には `ty_usage T = UUnrestricted` の前提を追加する
- affine/linear 値への参照を deref して値を取り出すことは禁止
- affine/linear 値を参照越しに操作するには `EReplace`（`*r = new_val`）を使う
- `Eval_Deref_Consume` ケースは**不要**（inner type が必ず unrestricted のため）
- BorrowState がない v1 では競合チェックなし。型だけ正しくする。

---

## 実装コンポーネント

### 1. `Syntax.v` 修正

#### 1.1 EBorrow の追加

```coq
(* &x / &mut x — takes a reference to a place *)
| EBorrow : ref_kind -> place -> expr

(* *e — dereference a reference *)
| EDeref : expr -> expr
```

追加場所：`EAssign` の後、`EDrop` の前。

#### 1.2 place の現状

`place = PVar : ident -> place` のまま。v1 では変数名のみを借用対象とする。
`PDeref`（`*r.field` のような複合 place）はスコープ外。

---

### 2. `OperationalSemantics.v` 修正

#### 2.1 VRef の追加

```coq
Inductive value : Type :=
| VUnit  : value
| VInt   : Z -> value
| VFloat : string -> value
| VBool  : bool -> value
| VRef   : ident -> value.   (* 参照先の変数名を保持 *)
```

#### 2.2 Eval_Borrow の追加

```coq
(* &x または &mut x: x がストアに存在することを確認し、VRef x を返す。
   ストアは変化しない（借用は所有権を移さない）。 *)
| Eval_Borrow : forall s x e rk,
    store_lookup x s = Some e ->
    eval fenv s (EBorrow rk (PVar x)) s (VRef x)
```

#### 2.3 Eval_Deref の追加

```coq
(* *r: inner type が UUnrestricted の場合のみ許可（Rust 同様、move out 不可）。
   r が VRef x に評価され、ストアから x の現在の値を読む（コピー）。
   ストアは変化しない（unrestricted = コピーセマンティクス）。 *)
| Eval_Deref : forall s s_r r x e,
    eval fenv s r s_r (VRef x) ->
    store_lookup x s_r = Some e ->
    ty_usage (se_ty e) = UUnrestricted ->
    eval fenv s (EDeref r) s_r (se_val e)
```

設計メモ：
- affine/linear な inner type への deref は型チェッカーが弾く（T_Deref の UUnrestricted 制約）
- `Eval_Deref_Consume` ケースは不要（inner type が必ず unrestricted）
- ストアは変化しない（元の変数 x は intact のまま）

---

### 3. `TypingRules.v` 修正

`Lifetime` を import する。

#### 3.1 T_Borrow の追加

```coq
(* &x — 共有借用
   - x が文脈に存在し未消費
   - x の usage は unrestricted か affine に限定（linear は借用禁止）
   - immutable でも mutable でも shared borrow は可能
   - 返す型は &'static T（v1 では lifetime 推論なし）
   - x は消費しない *)
| T_BorrowShared : forall Γ x T,
    ctx_lookup x Γ = Some (T, false) ->
    ty_usage T <> ULinear ->
    typed fenv Γ (EBorrow RShared (PVar x))
      (MkTy UUnrestricted (TRef LStatic RShared T)) Γ

(* &mut x — 可変借用
   - x が文脈に存在し未消費
   - x の usage は unrestricted か affine に限定（linear は借用禁止）
   - x は mutable として宣言されていなければならない
     （Rust 同様: let a = 10; let r = &mut a; はエラー）
   - 返す型は &'static mut T（v1 では lifetime 推論なし）
   - x は消費しない *)
| T_BorrowMut : forall Γ x T,
    ctx_lookup x Γ = Some (T, false) ->
    ty_usage T <> ULinear ->
    ctx_lookup_mut x Γ = Some MMutable ->
    typed fenv Γ (EBorrow RUnique (PVar x))
      (MkTy UUnrestricted (TRef LStatic RUnique T)) Γ
```

設計メモ：
- `T_BorrowShared` と `T_BorrowMut` に分けることで `rk` による条件分岐を避ける（Rocq で扱いやすい）
- 借用の結果型の usage は `UUnrestricted`（参照自体は自由にコピー・共有できる）
- `LStatic` は v1 の暫定値
- linear 変数を借用禁止とする理由：must-consume 義務を持ったまま参照だけ作ると、参照消滅後に誰も drop できなくなる
- `&mut` は mutable 変数にのみ許可（`ctx_lookup_mut` は既に T_Replace で使用実績あり）

#### 3.2 T_Deref の追加

```coq
(* *r: r が &'a rk T 型で、T が UUnrestricted ならば T を返す。
   Rust 同様、参照越しに affine/linear 値を move out することは禁止。
   参照自体の usage u_r は問わない（linear 参照を deref すれば r が消費されるだけ）。 *)
| T_Deref : forall Γ Γ' r la rk T u_r,
    ty_usage T = UUnrestricted ->
    typed fenv Γ r (MkTy u_r (TRef la rk T)) Γ' ->
    typed fenv Γ (EDeref r) T Γ'
```

設計メモ：
- `ty_usage T = UUnrestricted` 制約により、affine/linear 値は deref で取り出せない
- affine/linear 値を参照越しに操作するには `EReplace` を使う（v2 以降で整備）
- **参照自体の usage は固定しない**：`u_r` は任意（ULinear/UAffine/UUnrestricted）。
  参照 `r` が linear なら `typed ... r (MkTy ULinear (TRef ...)) Γ'` が `r` を消費する。
  `T_Deref` に `MkTy UUnrestricted (TRef ...)` を固定すると、関数引数 `r: UAffine (TRef ...)`
  などへの `*r` が checker では通るが証明できない CheckerSoundness ホールになる。

---

### 4. `TypeChecker.v` 修正

#### 4.1 EBorrow の推論

```coq
| EBorrow rk (PVar x) =>
    match ctx_lookup_b x Γ with
    | None              => infer_err (ErrUnknownVar x)
    | Some (_, true)    => infer_err (ErrAlreadyConsumed x)
    | Some (T_x, false) =>
        if usage_eqb (ty_usage T_x) ULinear
        then infer_err (ErrUsageMismatch (ty_usage T_x) UAffine)
        else
          (* &mut はさらに mutability チェック *)
          match rk with
          | RUnique =>
              match ctx_lookup_mut_b x Γ with
              | Some MMutable => infer_ok (MkTy UUnrestricted (TRef LStatic rk T_x), Γ)
              | _             => infer_err (ErrImmutableBorrow x)
              end
          | RShared =>
              infer_ok (MkTy UUnrestricted (TRef LStatic rk T_x), Γ)
          end
    end
```

新しいエラーが必要：

```coq
| ErrImmutableBorrow : ident -> infer_error
```

#### 4.2 EDeref の推論

```coq
(* 参照自体の usage はチェックしない（T_Deref が u_r を forall で受け取るため）。
   inner type が UUnrestricted であることだけを確認する。 *)
| EDeref r =>
    match infer_core fenv Γ r with
    | infer_err err => infer_err err
    | infer_ok (T_r, Γ') =>
        match ty_core T_r with
        | TRef _ _ T_inner =>
            (* affine/linear を deref して move out することは禁止 *)
            if usage_eqb (ty_usage T_inner) UUnrestricted
            then infer_ok (T_inner, Γ')
            else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
        | _ => infer_err (ErrNotAReference (ty_core T_r))
        end
    end
```

新しいエラーが必要（`infer_error` に追加）：

```coq
| ErrImmutableBorrow : ident -> infer_error     (* &mut x where x is immutable *)
| ErrNotAReference : TypeCore Ty -> infer_error (* deref of non-reference type *)
```

---

### 5. `AlphaRenaming.v` 修正

#### 5.1 expr_alpha への追加

```coq
| EA_Borrow : forall ρ rk x,
    expr_alpha ρ (EBorrow rk (PVar x))
               (EBorrow rk (PVar (lookup_rename x ρ)))

| EA_Deref : forall ρ e er,
    expr_alpha ρ e er ->
    expr_alpha ρ (EDeref e) (EDeref er)
```

#### 5.2 free_vars_expr / expr_size / alpha_rename_expr への追加

```coq
| EBorrow _ (PVar x) => [x]           (* free_vars_expr *)
| EDeref e            => free_vars_expr e

| EBorrow _ _ => 1                    (* expr_size *)
| EDeref e    => S (expr_size e)

(* alpha_rename_expr *)
| EBorrow rk (PVar x) =>
    (EBorrow rk (PVar (rename_var ρ x)), used)

| EDeref e =>
    let (er, used') := alpha_rename_expr ρ used e in
    (EDeref er, used')
```

#### 5.3 backward typing 保存補題への追加

T_Borrow ケースと T_Deref ケースの backward 証明を追加。

---

### 6. `CheckerSoundness.v` 修正

- EBorrow と EDeref の健全性証明ケースを追加
- `T_Borrow` と `T_Deref` の適用

---

### 7. OCaml 修正

#### 7.1 `ast.ml` への追加

```ocaml
| NBorrow of ref_kind * name   (* &x / &mut x *)
| NDeref of named_expr         (* (*e) *)
```

#### 7.2 `parser.mly` への追加

```
atom_expr:
  | LPAREN; AMP; x = ID; RPAREN
    { NBorrow (RShared, x) }
  | LPAREN; AMP; KW_MUT; x = ID; RPAREN
    { NBorrow (RUnique, x) }
  | LPAREN; STAR; e = expr; RPAREN
    { NDeref e }
```

新トークン: `STAR`（`*`）を lexer に追加。

#### 7.3 `debruijn.ml` への追加

```ocaml
| NBorrow (rk, name) ->
    EBorrow (rk, make_ident name (lookup scope name))
| NDeref e ->
    EDeref (convert scope e)
```

#### 7.4 `fir.ml` への追加

```ocaml
type fir_instr =
  | ...
  | FIBorrow of tmp * ref_kind * ident  (* tmp = &x / &mut x *)
  | FIDeref  of tmp * tmp               (* tmp = *r *)

(* lower *)
| EBorrow (rk, PVar x) ->
    let t = fresh () in
    ([FIBorrow (t, rk, x)], t)
| EDeref e ->
    let (is, r) = lower_expr fenv e in
    let t = fresh () in
    (is @ [FIDeref (t, r)], t)
```

---

### 8. `_CoqProject` / `Makefile`

変更なし（新規 `.v` ファイルなし）。

---

## 影響範囲まとめ

| ファイル | 変更内容 | 重さ |
|---------|---------|------|
| `Syntax.v` | EBorrow, EDeref 追加 | 小 |
| `OperationalSemantics.v` | VRef 追加, Eval_Borrow, Eval_Deref | 中 |
| `TypingRules.v` | T_Borrow, T_Deref 追加, Lifetime import | 小 |
| `TypeChecker.v` | EBorrow/EDeref 推論, ErrNotAReference | 小 |
| `AlphaRenaming.v` | EA_Borrow, EA_Deref, free_vars/size/rename 更新, backward 証明 | 中 |
| `CheckerSoundness.v` | EBorrow/EDeref 健全性証明 | 中 |
| `CheckerUsageSoundness.v` | EBorrow/EDeref ケース追加（通常は自明） | 小 |
| `ocaml/ast.ml` | NBorrow, NDeref | 小 |
| `ocaml/lexer.ml` | STAR トークン追加 | 小 |
| `ocaml/parser.mly` | `(&x)`, `(&mut x)`, `(*e)` 構文 | 小 |
| `ocaml/debruijn.ml` | NBorrow/NDeref 変換 | 小 |
| `ocaml/fir.ml` | FIBorrow, FIDeref lowering | 小 |
| `fixtures/TypeChecker.ml` | make による自動再生成 | 自動 |

---

## テスト追加

### valid
- `tests/valid/borrow/shared_borrow.facet` — unrestricted 変数への `&x`、`(*r)` で読む
- `tests/valid/borrow/mut_borrow.facet` — `&mut x` で参照を作る（v1 では競合チェックなし）
- `tests/valid/borrow/borrow_unrestricted.facet` — unrestricted 変数の shared borrow + deref

### invalid
- `tests/invalid/borrow_error/linear_borrow.facet` — linear 変数の borrow はエラー
- `tests/invalid/borrow_error/affine_deref.facet` — affine inner type への deref（move out）はエラー
- `tests/invalid/borrow_error/deref_non_ref.facet` — 参照でない値を dereference はエラー
- `tests/invalid/borrow_error/mut_borrow_immutable.facet` — immutable 変数への `&mut` はエラー
  ```
  fn test() -> () {
    let a: i64 = 10;
    let r: &mut i64 = (&mut a);  (* エラー：a は immutable *)
    ()
  }
  ```

---

## Accepted Soundness Gaps（v1 既知の穴）

### Gap 1: Dangling reference（use-after-scope）

`T_BorrowShared/T_BorrowMut` は `LStatic` を全 borrow に割り当てるため、型システムは参照が永続すると主張する。しかし `Eval_Let` はスコープ終了時に `store_remove x s2` で変数を消去する。

```
(* 型検査は通る、実行時に詰まる *)
let r: &'static i64 =
  (let x: i64 = 5 in (&x))   (* x はスコープ終了で store から消去 *)
in (*r)                        (* Eval_Deref: store_lookup x = None → stuck! *)
```

型安全性（progress）は保証されない。これは **accepted gap** — safety theorem は v4 のスコープ。

### Gap 2: `&mut T` の UUnrestricted による排他性欠如

`T_BorrowMut` の結果型は `MkTy UUnrestricted (TRef LStatic RUnique T)`。`UUnrestricted` のため `&mut x` を複数コピーできる（aliasing `&mut`）。Rust の排他性保証は満たされない。

これは **accepted gap** — BorrowState（v2）が排他性を強制する。

---

## 検証基準

1. `cd rocq && make` が全ファイルエラーなしでコンパイルされる
2. `dune build` が成功する
3. 既存テスト（valid/invalid すべて）が引き続き合格する
4. 新規 valid テストが合格し、新規 invalid テストが正しくエラーを返す

---

## 今後の拡張（v2 以降）

```
v2: BorrowState を TypingRules の判断に組み込む
    - 共有借用と可変借用の競合チェック
    - &T は複数可, &mut T は1つだけ

v3: Re-borrow 規則
    - &mut から &mut への re-borrow
    - &mut から &T への downgrade re-borrow

v4: Safety theorems
    - infer が返す型が wf_type を満たすことの証明
    - no dangling reference
    - aliasing safety
```
