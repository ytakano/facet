# Lifetime v5: Region Context Integration と Dangling Reference 防止

## 目的

v4 までの soundness hole を閉じる:

```facet
fn make_ref(mut x: unrestricted isize) -> unrestricted &unrestricted isize {
    (&x)   (* ローカルパラメータへの参照を返す → dangling reference *)
}
```

現状、`EBorrow (PVar x)` は常に `TRef LStatic T` を返し、関数の return type と一致してしまう。  
v5 では `fn_lifetimes : nat`（エクスポートされた lifetime パラメータ数）を `fn_def` に追加し、  
borrow の result type をスコープ限定の `LVar n` に変更する。  
関数レベルで `wf_type Δ (fn_ret)` を検査することで dangling reference を弾く。

---

## 設計方針

### エクスポートされた lifetime と ローカル lifetime

`fn_lifetimes = k` の関数では:

- **エクスポート lifetime**: `LVar 0, LVar 1, ..., LVar (k-1)`  
  → `Δ = [LVar 0; LVar 1; ...; LVar (k-1)]`
  → 関数パラメータの参照型に明示的に使える（`&'a T` など）  
  → return type に使える（`wf_type Δ` で検査）

- **ローカル lifetime**: `LVar k`（= `LVar fn_lifetimes`）  
  → 値パラメータや let 束縛変数への borrow に割り当てる  
  → `Δ` に含まれないので return type に使えない  
  → dangling reference を防ぐ

### 変更する判断の型

```
(変更前) typed fenv Γ e T Γ'
(変更後) typed fenv n Γ e T Γ'    (* n = fn_lifetimes *)
```

`n` は現在の関数の `fn_lifetimes` 。ほとんどのルールでは単に pass-through。  
borrow ルールのみで `LVar n` を result type の lifetime として使う。

### borrow の lifetime 割り当て

| 式 | 変更前 result type | 変更後 result type |
|---|---|---|
| `EBorrow RShared (PVar x)` | `TRef LStatic RShared T` | `TRef (LVar n) RShared T` |
| `EBorrow RUnique (PVar x)` | `TRef LStatic RUnique T` | `TRef (LVar n) RUnique T` |
| `EBorrow RShared (PDeref (PVar r))` | `TRef LStatic RShared T` | `TRef (LVar n) RShared T` |
| `EBorrow RUnique (PDeref (PVar r))` | `TRef LStatic RUnique T` | `TRef (LVar n) RUnique T` |

re-borrow も `LVar n` を使う（子参照のライフタイムはローカルスコープに限定）。

### 関数レベルの検査

`infer fenv f` (TypeChecker.v の `infer`) の末尾に追加:

```
let n := fn_lifetimes f in
let Δ := mk_region_ctx n in
if wf_type_b Δ (fn_ret f) then ...
else infer_err ErrLifetimeLeak
```

`wf_type_b` は `wf_type` の決定的 bool 版（新規定義）。

---

## 変更しないもの（v5 スコープ外）

- `EDeref (EDeref ...)` alias chain（v6）
- `EVar r` で `&mut T` をコピーした場合のエイリアス追跡（v6）
- `PDeref (PDeref ...)` 深さ ≥ 2（引き続き `ErrNotImplemented`）
- lifetime サブタイピング（outlives 関係の強制）— v6 以降
- lifetime 推論（コード中で `'a` を省略した場合の自動推論）— v6 以降
- ECall でのライフタイム代入（関数呼び出し時に `LVar 0` → 実際のライフタイムへの置換）— v6

---

## 詳細実装手順

### 1. `Syntax.v`

`fn_def` に `fn_lifetimes` フィールドを追加:

```coq
Record fn_def : Type := MkFnDef {
  fn_name      : ident;
  fn_lifetimes : nat;        (* エクスポートされた lifetime パラメータ数 *)
  fn_params    : list param;
  fn_ret       : Ty;
  fn_body      : expr
}.
```

影響: `fn_def` を構築する箇所（AlphaRenaming.v の `alpha_rename_fn`、TypeChecker.v の `infer_core`、OCaml の `debruijn.ml`）すべてに `fn_lifetimes` フィールドを追加。

---

### 2. `TypingRules.v`

#### 2a. `typed` 判断に `n : nat` を追加

```coq
Inductive typed (fenv : list fn_def) (n : nat) : ctx -> expr -> Ty -> ctx -> Prop :=
```

全 rule に `n` を追加（ほとんどは pass-through）:

```coq
(* 例: T_Unit *)
| T_Unit : forall Γ,
    typed fenv n Γ EUnit (MkTy UUnrestricted TUnits) Γ

(* T_Let: e1 と e2 も同じ n *)
| T_Let : forall m x T1 T2 Γ Γ1 Γ2 e1 e2,
    typed fenv n Γ e1 T1 Γ1 ->
    typed fenv n (ctx_add x T1 m Γ1) e2 T2 Γ2 ->
    typed fenv n Γ (ELet m x T1 e1 e2) T2 Γ2
```

#### 2b. borrow ルールを更新

```coq
(* T_BorrowShared: LStatic → LVar n *)
| T_BorrowShared : forall Γ x T,
    ctx_lookup x Γ = Some (T, false) ->
    ty_usage T <> ULinear ->
    typed fenv n Γ (EBorrow RShared (PVar x))
      (MkTy UUnrestricted (TRef (LVar n) RShared T)) Γ

(* T_BorrowMut: LStatic → LVar n *)
| T_BorrowMut : forall Γ x T,
    ctx_lookup x Γ = Some (T, false) ->
    ctx_is_mut x Γ = true ->
    ty_usage T <> ULinear ->
    typed fenv n Γ (EBorrow RUnique (PVar x))
      (MkTy UUnrestricted (TRef (LVar n) RUnique T)) Γ

(* T_BorrowShared_Deref: LStatic → LVar n *)
| T_BorrowShared_Deref : forall Γ r u_r la T,
    ctx_lookup r Γ = Some (MkTy u_r (TRef la RShared T), false) ->
    ty_usage (MkTy u_r (TRef la RShared T)) <> ULinear ->
    typed fenv n Γ (EBorrow RShared (PDeref (PVar r)))
      (MkTy UUnrestricted (TRef (LVar n) RShared T)) Γ

(* T_BorrowMut_Deref: LStatic → LVar n *)
| T_BorrowMut_Deref : forall Γ r u_r la T,
    ctx_lookup r Γ = Some (MkTy u_r (TRef la RUnique T), false) ->
    ty_usage (MkTy u_r (TRef la RUnique T)) <> ULinear ->
    typed fenv n Γ (EBorrow RUnique (PDeref (PVar r)))
      (MkTy UUnrestricted (TRef (LVar n) RUnique T)) Γ
```

#### 2c. `mk_region_ctx` ヘルパー

```coq
(* n 個の LVar からなる region_ctx を生成: [LVar 0; LVar 1; ...; LVar (n-1)] *)
Fixpoint mk_region_ctx (n : nat) : region_ctx :=
  match n with
  | 0   => []
  | S k => mk_region_ctx k ++ [LVar k]
  end.
```

#### 2d. `wf_fn_ret_ok` 述語

```coq
(* 関数の return type が fn_lifetimes で決まる region_ctx でwell-formed *)
Definition wf_fn_ret_ok (fdef : fn_def) : Prop :=
  wf_type (mk_region_ctx (fn_lifetimes fdef)) (fn_ret fdef).
```

---

### 3. `TypeChecker.v`

#### 3a. `wf_type_b` — `wf_type` の bool 版

```coq
Fixpoint wf_type_b (Δ : region_ctx) (T : Ty) : bool :=
  match ty_core T with
  | TUnits | TIntegers | TFloats | TBooleans | TNamed _ => true
  | TFn params ret =>
      forallb (wf_type_b Δ) params && wf_type_b Δ ret
  | TRef l _rk inner =>
      lifetime_eqb l LStatic ||
      existsb (lifetime_eqb l) Δ
      (* ↑ wf_lifetime_b Δ l: l = LStatic または l ∈ Δ *)
      && wf_type_b Δ inner
  end.
```

補題: `wf_type_b_correct : wf_type_b Δ T = true ↔ wf_type Δ T`

#### 3b. `infer_core` に `n : nat` を追加

```coq
Fixpoint infer_core (fenv : list fn_def) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match e with
  (* ... 既存 case はすべて n を pass-through ... *)

  (* borrow: LStatic → LVar n *)
  | EBorrow rk (PVar x) =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, _) =>
          match rk with
          | RUnique =>
              if ctx_is_mut_b x Γ && negb (usage_eqb (ty_usage T) ULinear)
              then infer_ok (MkTy UUnrestricted (TRef (LVar n) RUnique T), Γ)
              else infer_err ErrMutabilityError
          | RShared =>
              if negb (usage_eqb (ty_usage T) ULinear)
              then infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T), Γ)
              else infer_err ErrLinearBorrow
          end
      end

  | EBorrow RShared (PDeref (PVar r)) => ... infer_ok (... TRef (LVar n) ...) ...
  | EBorrow RUnique (PDeref (PVar r)) => ... infer_ok (... TRef (LVar n) ...) ...

  (* ECall: 呼び出した関数の fn_lifetimes を使って再帰 *)
  | ECall fname args =>
      match lookup_fn fenv fname with
      | None => infer_err (ErrUnknownFn fname)
      | Some fdef =>
          let n_callee := fn_lifetimes fdef in
          (* ... fn_params を n_callee で再帰的に check ... *)
          (* 注: n_callee の LVar は呼び出し元コンテキストでは不透明 → v6 で lifetime substitution *)
```

**重要**: `infer_core` 内で `ECall` の arguments を check する際は `n`（呼び出し元）を使い、  
callee の `fn_lifetimes` は return type に使われている既存の `TRef LVar` を解釈するためのもの。

#### 3c. `infer` 関数に `wf_type_b` チェックを追加

```coq
Definition infer (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Δ := mk_region_ctx n in
  (* 1. return type の well-formedness を先に確認 *)
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  (* 2. 既存の body type inference *)
  match infer_body fenv n (params_ctx (fn_params f)) (fn_body f) with
  | infer_err e => infer_err e
  | infer_ok (T_body, Γ_out) =>
      if ty_core_eqb (ty_core T_body) (ty_core (fn_ret f)) then
        if usage_eqb (ty_usage T_body) (ty_usage (fn_ret f)) then
          if params_ok_b (fn_params f) Γ_out
          then infer_ok (fn_ret f, Γ_out)
          else infer_err ErrParamNotConsumed
        else infer_err (ErrUsageMismatch ...)
      else infer_err (ErrTypeMismatch ...)
  end.
```

新規エラー種類: `ErrLifetimeLeak` を `infer_error` に追加。

#### 3d. `infer_direct` も同様に更新

---

### 4. `AlphaRenaming.v`

#### 4a. `alpha_rename_fn` を更新

`MkFnDef` の呼び出しに `fn_lifetimes` を追加:

```coq
(MkFnDef (fn_name f) (fn_lifetimes f) params' (fn_ret f) body', used2)
```

#### 4b. `typed` を使用する定理を更新

```coq
Theorem alpha_rename_for_infer_typed_backward : forall fenv n Γ e fenv' e' T Γ',
  alpha_rename_for_infer Γ fenv e = (fenv', e') ->
  typed fenv' n Γ e' T Γ' ->
  typed fenv n Γ e T Γ'.
```

`n` を全 forall に追加するだけで証明構造は変わらない（α-renaming は型の中の lifetime に触れない）。

---

### 5. `CheckerSoundness.v`

全補題・定理のシグネチャを更新:

```coq
(* 変更前 *)
Theorem checker_soundness : forall fenv Γ e T Γ',
  infer_core fenv Γ e = infer_ok (T, Γ') -> typed fenv Γ e T Γ'.

(* 変更後 *)
Theorem checker_soundness : forall fenv n Γ e T Γ',
  infer_core fenv n Γ e = infer_ok (T, Γ') -> typed fenv n Γ e T Γ'.
```

各 case の borrow 節で `LVar n` を扱う部分のみ実質的な証明変更が生じる。  
その他の case は `n` の追加だけで証明構造は変わらない。

---

### 6. `CheckerUsageSoundness.v`

同様に `n` を全 forall に追加（proof structure は変わらない）。

---

### 7. `BorrowCheckSoundness.v`

`borrow_ok` 判断は `typed` に依存しないため影響は最小:  
`borrow_ok` の signature 自体は変わらない。  
`borrow_check_sound` / `borrow_check_complete` 補題も変わらない。

---

### 8. OCaml フロントエンド

#### 8a. `ast.ml`

```ocaml
type named_fn_def = {
  nf_name      : name;
  nf_lifetimes : int;     (* NEW: lifetime パラメータ数 *)
  nf_params    : named_param list;
  nf_ret       : TypeChecker.ty;
  nf_body      : named_expr;
}
```

参照型に lifetime annotation を追加:

```ocaml
(* named_ty (AST レベル) *)
type named_ty =
  | NTy of TypeChecker.ty                          (* lifetime なし → 後で解決 *)
  | NTyRef of string option * TypeChecker.ref_kind * named_ty
  (* ^-- string option: Some "'a" のような lifetime 変数名 *)
```

#### 8b. `parser.mly` — lifetime 構文の追加

```
fn_def:
| KW_FN; name = IDENT; LANGLE; lifetimes = separated_list(COMMA, LIFETIME); RANGLE;
  LPAREN; params = ...; RPAREN; ARROW; ret = ty; LBRACE; body = expr; RBRACE
  { { nf_name = name; nf_lifetimes = List.length lifetimes;
      nf_params = ...; nf_ret = ...; nf_body = ... } }
| KW_FN; name = IDENT;
  LPAREN; params = ...; RPAREN; ARROW; ret = ty; LBRACE; body = expr; RBRACE
  { { nf_name = name; nf_lifetimes = 0; ... } }    (* lifetime なし = 0 *)

ty:
| AMP; l = LIFETIME; t = ty { TRef (LVar (resolve_lt l lts), RShared, t) }
| AMP; l = LIFETIME; KW_MUT; t = ty { TRef (LVar (resolve_lt l lts), RUnique, t) }
| AMP; t = ty { TRef (LStatic, RShared, t) }      (* lifetime 省略 = LStatic or local? *)
| AMP; KW_MUT; t = ty { TRef (LStatic, RUnique, t) }
```

`LIFETIME` トークンは `'a`, `'b` などのリテラル（lexer で `'\''` + `IDENT` として認識）。

#### 8c. `debruijn.ml`

```ocaml
let convert_fn_def (f : named_fn_def) : fn_def =
  (* lifetime 変数の de Bruijn 変換: 'a → LVar 0, 'b → LVar 1, ... *)
  let lt_env = List.mapi (fun i lt -> (lt, i)) f.nf_lifetime_names in
  let resolve_lt l = List.assoc l lt_env in  (* string → nat *)
  ...
  { fn_name      = make_ident f.nf_name 0;
    fn_lifetimes = f.nf_lifetimes;            (* NEW *)
    fn_params    = params;
    fn_ret       = f.nf_ret;
    fn_body      = convert scope f.nf_body }
```

#### 8d. `grammar.ml`

grammar string を更新:

```
fn_def ::= 'fn' ident ('<' lifetime (',' lifetime)* '>')? '(' param* ')' '->' ty '{' expr '}'
ty ::= ... | '&' lifetime ty | '&' 'mut' lifetime ty | '&' ty | '&' 'mut' ty
lifetime ::= '\'' ident
```

---

### 9. テスト追加

#### valid — ライフタイムパラメータによる参照の返却

`tests/valid/lifetime/return_ref_param.facet`:
```facet
fn identity<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    r
}
```

`tests/valid/lifetime/read_through_ref.facet`:
```facet
fn deref<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted isize {
    (*r)
}
```

`tests/valid/lifetime/no_lifetime_no_ref.facet`:
```facet
fn double(mut x: unrestricted isize) -> unrestricted isize {
    let y: unrestricted isize = x in
    y
}
```

#### invalid — dangling reference（値パラメータの borrow を返す）

`tests/invalid/lifetime/return_local_borrow.facet`:
```facet
fn make_ref(mut x: unrestricted isize) -> unrestricted &unrestricted isize {
    (&x)
}
```
→ `ErrLifetimeLeak`: return type `&unrestricted isize = TRef LStatic ...` に対して  
  borrow 結果は `TRef (LVar 0) ...`（fn_lifetimes = 0 なので Δ = []）

`tests/invalid/lifetime/return_mut_local_borrow.facet`:
```facet
fn make_mut_ref(mut x: unrestricted isize) -> unrestricted &mut unrestricted isize {
    (&mut x)
}
```

---

## 新規エラー種類

```coq
Inductive infer_error : Type :=
  | ...
  | ErrLifetimeLeak    (* return type に export されていない LVar が含まれる *)
```

OCaml 側のエラーメッセージ: `"lifetime leak: return type references a local lifetime"`

---

## ECall での lifetime 扱い（注意事項・v6 持ち越し）

`fn f<'a>(r: &'a T) -> &'a T { r }` を呼び出す際、  
返り値の型は `TRef (LVar 0) T`（callee の LVar 0）。  
呼び出し元では `LVar 0` が何のライフタイムを表すか不明なため、  
v5 では **呼び出し結果の参照型を使う際の lifetime は検証しない**（保守的に許可）。

完全な lifetime substitution は v6 で実装予定。

---

## 既知の制限（v6 以降に持ち越し）

| 制限 | 内容 |
|------|------|
| ECall の lifetime 代入 | `f<'a>(r: &'a T) -> &'a T` の返り値型に caller の lifetime を代入しない |
| `EVar r` のコピー aliasing | `let s = r` （`r: &mut T`）でエイリアスが生じる問題 |
| `EDeref (EDeref ...)` chain | 二重 deref 時のフリーズチェック不完全 |
| `PDeref (PDeref ...)` depth ≥ 2 | 引き続き `ErrNotImplemented` |
| lifetime サブタイピング | `outlives` 関係を使った型強制 |
| lifetime 省略ルール | `&T` の lifetime を文脈から自動推論 |
