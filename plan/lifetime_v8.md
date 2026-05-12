# Lifetime v8: Recursive Places and Nested Deref

## Summary

v7 で lifetime substitution と outlives-based compatibility は入った。
v8 では v4-v7 から残っている `PDeref (PDeref ...)` と `EDeref (EDeref ...)` の制限を外し、place/deref を再帰的に扱えるようにする。

主目的は、`&mut *r` や `replace *r e` だけでなく、参照の参照に対する `&mut **r`、`replace **r e`、`**r` のような chain を型検査・borrow check・実行意味論で一貫して扱うこと。

v8 は alias tracking 全体の完成ではなく、現在 `ErrNotImplemented` になっている深い deref place と、深い `EDeref` に対する freeze check の穴を閉じる段階とする。

---

## Current Limitations

既存計画で v8 以降に持ち越されている制限:

- `PDeref (PDeref ...)` depth >= 2 は `TypeChecker.v` で `ErrNotImplemented`。
- `EBorrow _ (PDeref (PDeref _))` も `ErrNotImplemented`。
- `EDeref (EDeref ...)` chain の freeze check は、内側が直接 `EVar r` の場合しか見ていない。
- `OperationalSemantics.v` は `EReplace (PDeref (PVar r))` / `EAssign (PDeref (PVar r))` / `EBorrow _ (PDeref (PVar r))` だけを持ち、再帰 place の評価がない。
- OCaml parser は `replace *x e` までで、`replace **x e` や `&**x` を直接表現できない。
- `EVar r` のコピー aliasing、明示的 outlives constraint、lifetime elision、higher-rank lifetimes は未対応のまま残す。

---

## Design

### 1. Recursive place typing

`TypingRules.v` に place 専用の補助判断を追加する。

```coq
Inductive typed_place (fenv : list fn_def) (n : nat)
    : ctx -> place -> Ty -> ref_kind -> Prop :=
| TP_Var : forall Γ x T,
    ctx_lookup x Γ = Some (T, false) ->
    typed_place fenv n Γ (PVar x) T RShared
| TP_Deref : forall Γ p la rk T rk_base,
    typed_place fenv n Γ p (MkTy UUnrestricted (TRef la rk T)) rk_base ->
    typed_place fenv n Γ (PDeref p) T rk.
```

実装時には、`TP_Var` の `ref_kind` 表現は再検討してよい。
重要なのは `PDeref p` の型を「`p` が参照型を持つなら inner type」として再帰的に計算できること。

`T_ReBorrowShared`, `T_ReBorrowMut`, `T_Replace_Deref`, `T_Assign_Deref` は `PDeref (PVar r)` 固定ではなく `PDeref p` に一般化する。

### 2. Executable place inference

`TypeChecker.v` に checker 側の mirror を追加する。

```coq
Fixpoint infer_place (Γ : ctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match ctx_lookup_b x Γ with
      | Some (T, false) => infer_ok T
      | Some (_, true)  => infer_err (ErrAlreadyConsumed x)
      | None            => infer_err (ErrUnknownVar x)
      end
  | PDeref q =>
      match infer_place Γ q with
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      | infer_err err => infer_err err
      end
  end.
```

`infer_place_mut_target` または同等の補助関数を追加し、`replace` / `assign` では chain 上の最後に辿った参照が `RUnique` であることを確認する。

`EReplace (PDeref p)` と `EAssign (PDeref p)` はこの補助関数を使い、`PDeref (PDeref _)` の `ErrNotImplemented` branch を削除する。

`EBorrow RShared (PDeref p)` は、`p` が参照型を持つなら共有 re-borrow を許す。

`EBorrow RUnique (PDeref p)` は、`p` が `&mut T` に辿れる場合のみ許す。

### 3. Recursive freeze checks

現在の `borrow_ok_deref_check` は `EDeref (EVar r)` だけを見る。
v8 では deref expression と place chain の root を取り出し、chain 内に active mutable re-borrow がある場合を拒否する。

```coq
Fixpoint expr_ref_root (e : expr) : option ident :=
  match e with
  | EVar x => Some x
  | EDeref e' => expr_ref_root e'
  | _ => None
  end.

Definition borrow_ok_deref_check (BS : borrow_state) (e : expr) : Prop :=
  match expr_ref_root e with
  | Some r => bs_can_shared r BS
  | None => True
  end.
```

place 側も同様に `place_root : place -> ident` だけでなく、chain 上の参照変数を検査する補助を導入する。

`EReplace (PDeref p)` / `EAssign (PDeref p)` は、書き込み対象 chain に active re-borrow があれば拒否する。

### 4. Recursive place evaluation

`OperationalSemantics.v` に place 解決を追加する。

```coq
Inductive eval_place (fenv : list fn_def) : store -> place -> ident -> Prop :=
| EvalPlace_Var : forall s x,
    store_lookup x s <> None ->
    eval_place fenv s (PVar x) x
| EvalPlace_Deref : forall s p r se_r x,
    eval_place fenv s p r ->
    store_lookup r s = Some se_r ->
    se_val se_r = VRef x ->
    eval_place fenv s (PDeref p) x.
```

`Eval_Replace_Deref`, `Eval_Assign_Deref`, `Eval_ReBorrow` は `eval_place` を使う形に一般化する。

`Eval_Deref` は expression を評価して `VRef x` を得る現在の形を維持できるが、freeze check の soundness と対応するため、`EDeref (EDeref ...)` が型規則・checker で通ることを前提に証明を更新する。

### 5. OCaml frontend and FIR

surface syntax を一般化する。

追加する構文案:

```facet
replace **r 42
**r = 42
&**r
&mut **r
```

OCaml 側では `named_place` を導入し、`*` の個数を `PDeref` chain に変換する。

- `ocaml/ast.ml`: `named_place` を追加し、`NReplace`, `NAssign`, `NBorrow` を place-based にする。
- `ocaml/parser.mly`: `place` nonterminal を追加する。
- `ocaml/debruijn.ml`: `named_place` を `Syntax.place` に変換する。
- `ocaml/fir.ml`: `place_name` だけに依存する実装を見直す。v8 では nested place を実行対象まで辿る FIR 命令にするか、Rocq extraction の型検査専用に限定するかを実装時に決める。

FIR がすぐに nested place を実行できない場合、v8 の `.facet` テストは typecheck CLI を対象にし、FIR 実行は v9 に分ける。

---

## Affected Files

- `rocq/theories/TypeSystem/Syntax.v`
  - `place` 自体は既に再帰型なので原則変更なし。

- `rocq/theories/TypeSystem/TypingRules.v`
  - `typed_place` または同等の補助判断を追加。
  - `T_ReBorrowShared`, `T_ReBorrowMut`, `T_Replace_Deref`, `T_Assign_Deref` を `PDeref p` に一般化。
  - `borrow_ok_deref_check` と write-through-reference の borrow rules を recursive place に対応。

- `rocq/theories/TypeSystem/TypeChecker.v`
  - `infer_place`, `infer_deref_target`, `place_freeze_check_b` を追加。
  - `ErrNotImplemented` になっている `PDeref (PDeref _)` / nested reborrow branches を削除。
  - `borrow_check` の `EDeref` / `EReplace` / `EAssign` / `EBorrow` を recursive place 対応に変更。

- `rocq/theories/TypeSystem/OperationalSemantics.v`
  - `eval_place` を追加。
  - replace/assign/reborrow の評価規則を recursive place 対応に一般化。

- `rocq/theories/TypeSystem/CheckerSoundness.v`
  - `infer_place_sound` を追加。
  - replace/assign/reborrow の soundness case を recursive helper に合わせて更新。

- `rocq/theories/TypeSystem/BorrowCheckSoundness.v`
  - recursive freeze helper の soundness/completeness を追加。

- `rocq/theories/TypeSystem/AlphaRenaming.v`
  - 既存の `place_alpha` は recursive なので、一般化した typing/borrow rules に合わせて proof を更新。

- `ocaml/ast.ml`, `ocaml/parser.mly`, `ocaml/debruijn.ml`, `ocaml/fir.ml`
  - nested place surface syntax を追加する場合に更新。

- `fixtures/TypeChecker.ml`, `fixtures/TypeChecker.mli`
  - `cd rocq && make` で再生成。

---

## Tests

以下のテストを追加する。

### valid: `tests/valid/reborrow/nested_shared_reborrow.facet`

```facet
fn nested_shared(mut x: unrestricted isize) -> unrestricted isize {
    let r: unrestricted &mut unrestricted isize = (&mut x) in
    let rr: unrestricted &unrestricted &mut unrestricted isize = (&r) in
    let s: unrestricted &unrestricted isize = (&**rr) in
    (*s)
}
```

### valid: `tests/valid/replace/replace_through_nested_ref.facet`

```facet
fn nested_replace(mut x: unrestricted isize) -> unrestricted isize {
    let r: unrestricted &mut unrestricted isize = (&mut x) in
    let rr: unrestricted &mut unrestricted &mut unrestricted isize = (&mut r) in
    let old: unrestricted isize = (replace **rr 42) in
    old
}
```

### invalid: `tests/invalid/reborrow/nested_deref_while_mut_reborrowed.facet`

```facet
fn bad(mut x: unrestricted isize) -> unrestricted isize {
    let r: unrestricted &mut unrestricted isize = (&mut x) in
    let rr: unrestricted &mut unrestricted &mut unrestricted isize = (&mut r) in
    let child: unrestricted &mut unrestricted isize = (&mut **rr) in
    **rr
}
```

### invalid: `tests/invalid/reborrow/nested_write_while_reborrowed.facet`

```facet
fn bad(mut x: unrestricted isize) -> unrestricted isize {
    let r: unrestricted &mut unrestricted isize = (&mut x) in
    let rr: unrestricted &mut unrestricted &mut unrestricted isize = (&mut r) in
    let child: unrestricted &unrestricted isize = (&**rr) in
    (replace **rr 99)
}
```

### invalid: `tests/invalid/borrow_error/nested_deref_non_ref.facet`

```facet
fn bad(mut x: unrestricted isize) -> unrestricted isize {
    **x
}
```

注意: 現行 parser が nested place syntax をまだ受け付けないため、v8 実装では parser 拡張と同時に追加する。
Rocq 側の unit Example で先に `PDeref (PDeref (PVar r))` の checker behavior を確認してもよい。

---

## Proof Tasks

1. `infer_place_sound`
   - `infer_place Γ p = infer_ok T -> typed_place fenv n Γ p T ...`

2. `infer_place_complete` は v8 では必須にしない。
   - 既存の checker soundness 方針に合わせ、必要になった場合だけ追加する。

3. `borrow_check_recursive_freeze_sound`
   - boolean freeze helper が true なら Prop 側の recursive freeze check が成り立つ。

4. `borrow_check_complete`
   - `borrow_ok_deref_check` の定義変更に追従する。

5. `eval_place` と alpha renaming
   - nested place の root/renaming が一致する補題を追加する。

---

## Non-Goals

- `EVar r` のコピーによる alias tracking 完成。
- 明示的な `'a : 'b` surface syntax。
- user-defined outlives constraint context。
- lifetime elision。
- higher-rank lifetimes。
- FIR/実行系の大規模再設計。

---

## Validation

実装後に以下を実行する。

```sh
cd rocq && make
dune build
bash tests/run.sh
```

`tests/run.sh` がまだ実行可能ビットを持たない場合は `bash tests/run.sh` で実行する。

