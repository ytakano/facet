# BorrowState v2 実装要件

## 概要

v1 で追加した EBorrow/EDeref に、**借用競合チェック（BorrowState）**を型規則として組み込む。

### 要件

- `&T`（共有借用）は同一変数に対して複数同時に許可
- `&mut T`（可変借用）は同一変数に対して同時に 1 つまで
- `&T` と `&mut T` は同一変数に対して競合（共存禁止）

---

## アーキテクチャ方針

### 設計選択: 独立した `borrow_ok` 判断を追加

**既存の `typed` の signature は変更しない。**

`TypingRules.v` に新しい帰納的判断 `borrow_ok` を追加する。
プログラムが「正しい」とは `typed` と `borrow_ok` の**両方**を満たすことを意味する。

```
well_formed fenv BS Γ e T Γ' BS' ⟺
    typed fenv Γ e T Γ'
    ∧ borrow_ok fenv BS Γ e Γ' BS'
```

この設計を採用する理由:
- `typed` を変更すると `AlphaRenaming.v`・`CheckerSoundness.v`・`CheckerUsageSoundness.v`
  の全証明（約 1000 行）を書き直す必要があり、リスクが大きい
- 型正確性（structural）と借用安全性（aliasing）の分離は Rust コンパイラと同じ設計
- `borrow_ok` は `TypingRules.v` の中に入るため「判断への組み込み」要件を満たす

`TypeChecker.v` には `borrow_check` 関数を**独立して追加**し、
既存の `infer_core` は変更しない。

---

## 1. BorrowState の型定義（`TypingRules.v`）

```coq
(* 現在アクティブな借用の列 *)
Inductive borrow_entry : Type :=
  | BEShared : ident -> borrow_entry   (* &x が取られている *)
  | BEMut    : ident -> borrow_entry.  (* &mut x が取られている *)

Definition borrow_state := list borrow_entry.
```

### 補助関数

```coq
(* x に対してアクティブな mut 借用があるか *)
Definition bs_has_mut (x : ident) (bs : borrow_state) : bool :=
  List.existsb (fun e => match e with
    | BEMut y => ident_eqb x y | _ => false end) bs.

(* x に対してアクティブな借用（shared/mut 問わず）があるか *)
Definition bs_has_any (x : ident) (bs : borrow_state) : bool :=
  List.existsb (fun e => match e with
    | BEShared y | BEMut y => ident_eqb x y end) bs.

(* shared borrow が取れるか: mut 借用なし *)
Definition bs_can_shared (x : ident) (bs : borrow_state) : Prop :=
  bs_has_mut x bs = false.

(* mut borrow が取れるか: 一切の借用なし *)
Definition bs_can_mut (x : ident) (bs : borrow_state) : Prop :=
  bs_has_any x bs = false.

(* borrow_entry の equality（decidable） *)
Definition be_eqb (e1 e2 : borrow_entry) : bool :=
  match e1, e2 with
  | BEShared x, BEShared y => ident_eqb x y
  | BEMut x,    BEMut y    => ident_eqb x y
  | _,          _          => false
  end.

(* リストからエントリを 1 件除去 *)
Fixpoint bs_remove_one (e : borrow_entry) (bs : borrow_state) : borrow_state :=
  match bs with
  | []      => []
  | h :: t  => if be_eqb e h then t else h :: bs_remove_one e t
  end.

(* 複数エントリを一括除去（scope exit 用） *)
Definition bs_remove_all (to_remove bs : borrow_state) : borrow_state :=
  List.fold_left (fun acc e => bs_remove_one e acc) to_remove bs.
```

---

## 2. `borrow_ok` 判断（`TypingRules.v`）

```coq
Inductive borrow_ok (fenv : list fn_def)
    : borrow_state -> ctx -> expr -> ctx -> borrow_state -> Prop :=
```

### BS 変化なし（通常の式）

```coq
  | BO_Unit : forall BS Γ,
      borrow_ok fenv BS Γ EUnit Γ BS

  | BO_Lit : forall BS Γ l,
      borrow_ok fenv BS Γ (ELit l) Γ BS

  | BO_Var : forall BS Γ Γ' x T b,
      ctx_lookup x Γ = Some (T, b) ->
      ctx_consume x Γ = Some Γ' ∨ ty_usage T = UUnrestricted ->
      borrow_ok fenv BS Γ (EVar x) Γ' BS
      (* 注: ctx 変化は typed で行う。BO_Var は ctx 変化を再現するのではなく、
         BS 変化なしであることのみを表明する。
         ctx 出力は typed の出力と一致させる必要があるため、以下の代替設計を参照 *)
```

> **注意**: `borrow_ok` が ctx 変化まで追跡するのは重複が多い。
> `borrow_ok` を **ctx なし**の形式 `borrow_ok fenv BS e BS' : Prop` に単純化する案:
>
> ```coq
> Inductive borrow_ok (fenv : list fn_def) : borrow_state -> expr -> borrow_state -> Prop
> ```
>
> この場合 ctx は不要（&x の conflict check だけに必要だが、
> typed の前提条件として確認済みとみなすか、
> あるいは borrow_ok の precondition として ctx を受け取るが出力しない形にする）。
>
> **推奨設計**:
>
> ```coq
> Inductive borrow_ok (fenv : list fn_def) : borrow_state -> ctx -> expr -> borrow_state -> Prop
> ```
> ctx は入力のみ（出力しない）。ctx の変化追跡は typed に任せる。
> ctx threading は borrow_ok が自身で行う必要がある場合のみ渡す。

### 推奨 signature（ctx 入力のみ）

```coq
Inductive borrow_ok (fenv : list fn_def)
    : borrow_state -> ctx -> expr -> borrow_state -> Prop :=
```

### 各ケース

```coq
  (* 値式: BS, ctx ともに変化なし *)
  | BO_Unit : forall BS Γ,      borrow_ok fenv BS Γ EUnit      BS
  | BO_Lit  : forall BS Γ l,    borrow_ok fenv BS Γ (ELit l)   BS
  | BO_Var  : forall BS Γ x,    borrow_ok fenv BS Γ (EVar x)   BS

  (* 共有借用: x に mut 借用がなければ OK。BS に BEShared x を追加 *)
  | BO_BorrowShared : forall BS Γ x T,
      ctx_lookup x Γ = Some (T, false) ->
      bs_can_shared x BS ->
      borrow_ok fenv BS Γ (EBorrow RShared (PVar x)) (BEShared x :: BS)

  (* 可変借用: x に一切の借用がなければ OK。BS に BEMut x を追加 *)
  | BO_BorrowMut : forall BS Γ x T,
      ctx_lookup x Γ = Some (T, false) ->
      bs_can_mut x BS ->
      borrow_ok fenv BS Γ (EBorrow RUnique (PVar x)) (BEMut x :: BS)

  (* Deref: 内部式の BS 変化を伝播 *)
  | BO_Deref : forall BS BS' Γ e,
      borrow_ok fenv BS Γ e BS' ->
      borrow_ok fenv BS Γ (EDeref e) BS'

  (* Drop: 内部式の BS 変化を伝播 *)
  | BO_Drop : forall BS BS' Γ e,
      borrow_ok fenv BS Γ e BS' ->
      borrow_ok fenv BS Γ (EDrop e) BS'

  (* ELet: e1 → BS1, e2（Γ に x 追加）→ BS2
     scope exit: e1 が追加した借用エントリを BS2 から除去する
     これにより let r = &x; ... r out of scope; &mut x が後続で許可される *)
  | BO_Let : forall BS BS1 BS2 Γ m x T T2 e1 e2,
      borrow_ok fenv BS Γ e1 BS1 ->
      borrow_ok fenv BS1 (ctx_add x T m Γ) e2 BS2 ->
      let new_from_e1 := bs_new_entries BS BS1 in
      borrow_ok fenv BS Γ (ELet m x T e1 e2)
                (bs_remove_all new_from_e1 BS2)

  (* ELetInfer: ELet と同様 *)
  | BO_LetInfer : forall BS BS1 BS2 Γ m x e1 e2,
      borrow_ok fenv BS Γ e1 BS1 ->
      (* e1 の型は borrow_ok には不要（型はすでに typed で確認済み）
         ctx_add する型は infer から取得するか、borrow_ok では ctx 渡さず単純化 *)
      borrow_ok fenv BS1 Γ e2 BS2 ->
      borrow_ok fenv BS Γ (ELetInfer m x e1 e2) (bs_remove_all (bs_new_entries BS BS1) BS2)

  (* EReplace/EAssign: 右辺式の BS 変化を伝播 *)
  | BO_Replace : forall BS BS' Γ x e_new,
      borrow_ok fenv BS Γ e_new BS' ->
      borrow_ok fenv BS Γ (EReplace (PVar x) e_new) BS'
  | BO_Assign  : forall BS BS' Γ x e_new,
      borrow_ok fenv BS Γ e_new BS' ->
      borrow_ok fenv BS Γ (EAssign (PVar x) e_new) BS'

  (* EIf: e1 で BS1、e2 で BS2、e3 で BS3
     両分岐の BS 変化が一致しなければならない
     （線形変数の消費と同様の対称性要件）
     BS_out = 両分岐の共通 BS を取る（max で安全側）
     簡略化: BS2 = BS3 を要求（両分岐が同じ借用状態で終わること）*)
  | BO_If : forall BS BS1 BS2 BS3 Γ e1 e2 e3,
      borrow_ok fenv BS  Γ e1 BS1 ->
      borrow_ok fenv BS1 Γ e2 BS2 ->
      borrow_ok fenv BS1 Γ e3 BS3 ->
      (* BS2 = BS3 を要求: 両分岐で同じ借用状態 *)
      BS2 = BS3 ->
      borrow_ok fenv BS Γ (EIf e1 e2 e3) BS2

  (* ECall: 引数を左→右に評価、BS を順次伝播 *)
  | BO_Call : forall BS BS' Γ fname args,
      borrow_ok_args fenv BS Γ args BS' ->
      borrow_ok fenv BS Γ (ECall fname args) BS'

with borrow_ok_args (fenv : list fn_def)
    : borrow_state -> ctx -> list expr -> borrow_state -> Prop :=
  | BO_Args_Nil  : forall BS Γ,      borrow_ok_args fenv BS Γ [] BS
  | BO_Args_Cons : forall BS BS1 BS2 Γ a rest,
      borrow_ok fenv BS Γ a BS1 ->
      borrow_ok_args fenv BS1 Γ rest BS2 ->
      borrow_ok_args fenv BS Γ (a :: rest) BS2
```

### `bs_new_entries` の定義

```coq
(* bs_after = new_entries ++ bs_before （prepend-only 不変条件） *)
(* 追加エントリ = bs_after の先頭 (|bs_after| - |bs_before|) 件 *)
Fixpoint bs_new_entries (bs_before bs_after : borrow_state) : borrow_state :=
  let n_before := List.length bs_before in
  let n_after  := List.length bs_after  in
  (* bs_after の先頭 (n_after - n_before) 件を返す *)
  firstn (n_after - n_before) bs_after.
```

> **前提条件**: `borrow_ok` は BorrowState を prepend のみで拡張する（除去は scope exit のみ）。
> この不変条件により `bs_new_entries` が正しく動作する。
> TypeChecker の `borrow_check` でも同じ不変条件を守る。

---

## 3. `borrow_check` 関数（`TypeChecker.v`）

`infer_core` は変更しない。独立した `borrow_check` 関数を追加。

```coq
(* 借用チェック専用エラー *)
| ErrBorrowConflict : ident -> infer_error   (* &mut x が既存借用と競合 *)
```

> `ErrBorrowConflict` は既存の `infer_error` 型に追加する。
> `ErrImmutableBorrow`（v1 追加済み）は継続使用。

```coq
(* 借用チェック関数 *)
(* borrow_state を持ち回りながら式全体を走査する *)
Fixpoint borrow_check (fenv : list fn_def) (BS : borrow_state) (Γ : ctx) (e : expr)
    : infer_result (borrow_state) :=
  match e with
  | EUnit | ELit _ | EVar _ | EReplace _ _ | EAssign _ _ => infer_ok BS

  | EBorrow RShared (PVar x) =>
      if bs_has_mut_b x BS
      then infer_err (ErrBorrowConflict x)    (* 既存 mut 借用と競合 *)
      else infer_ok (BEShared x :: BS)

  | EBorrow RUnique (PVar x) =>
      if bs_has_any_b x BS
      then infer_err (ErrBorrowConflict x)    (* 既存借用（shared/mut）と競合 *)
      else infer_ok (BEMut x :: BS)

  | EDeref e1 | EDrop e1 =>
      borrow_check fenv BS Γ e1

  | EReplace (PVar _) e_new | EAssign (PVar _) e_new =>
      borrow_check fenv BS Γ e_new

  | ELet m x T e1 e2 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let new_from_e1 := bs_new_entries BS BS1 in
          match borrow_check fenv BS1 (ctx_add_b x T m Γ) e2 with
          | infer_err err => infer_err err
          | infer_ok BS2  =>
              infer_ok (bs_remove_all_b new_from_e1 BS2)   (* scope exit release *)
          end
      end

  | ELetInfer m x e1 e2 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let new_from_e1 := bs_new_entries BS BS1 in
          match borrow_check fenv BS1 Γ e2 with
          | infer_err err => infer_err err
          | infer_ok BS2  => infer_ok (bs_remove_all_b new_from_e1 BS2)
          end
      end

  | EIf e1 e2 e3 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1  =>
          match borrow_check fenv BS1 Γ e2,
                borrow_check fenv BS1 Γ e3 with
          | infer_ok BS2, infer_ok BS3 =>
              if bs_eqb BS2 BS3     (* 両分岐の借用状態が一致 *)
              then infer_ok BS2
              else infer_err ErrContextCheckFailed
          | infer_err err, _ | _, infer_err err => infer_err err
          end
      end

  | ECall fname args =>
      borrow_check_args fenv BS Γ args
  end

with borrow_check_args (fenv : list fn_def) (BS : borrow_state) (Γ : ctx)
    (args : list expr) : infer_result (borrow_state) :=
  match args with
  | []       => infer_ok BS
  | a :: rest =>
      match borrow_check fenv BS Γ a with
      | infer_err err => infer_err err
      | infer_ok BS1  => borrow_check_args fenv BS1 Γ rest
      end
  end.
```

---

## 4. `infer` のエントリポイント更新（`TypeChecker.v`）

既存の `infer` は型チェックのみ。v2 では borrow_check を追加呼び出しする。

```coq
(* 型検査 + 借用チェック *)
Definition infer_full (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer fenv f with
  | infer_err err => infer_err err
  | infer_ok res  =>
      (* 型チェック成功後に借用チェックを実行 *)
      let Γ := params_ctx (fn_params f) in
      let BS_init : borrow_state := [] in
      match borrow_check fenv BS_init Γ (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _    => infer_ok res
      end
  end.
```

OCaml の `main.ml` は `infer` の代わりに `infer_full` を呼ぶ（または同様のロジックを OCaml 側で実装）。

---

## 5. `BorrowCheckSoundness.v`（新規ファイル）

`CheckerSoundness.v` に倣い、`borrow_check` と `borrow_ok` の対応を証明する。

```coq
From Facet.TypeSystem Require Import
  Lifetime Types Syntax TypingRules TypeChecker.

Theorem borrow_check_sound : forall fenv BS Γ e BS',
  borrow_check fenv BS Γ e = infer_ok BS' ->
  borrow_ok fenv BS Γ e BS'.

Theorem borrow_check_complete : forall fenv BS Γ e BS',
  borrow_ok fenv BS Γ e BS' ->
  borrow_check fenv BS Γ e = infer_ok BS'.
```

---

## 6. `_CoqProject` 更新

`BorrowCheckSoundness.v` を追加（`CheckerUsageSoundness.v` の後）:

```
theories/TypeSystem/BorrowCheckSoundness.v
```

---

## 7. OCaml 修正

### `main.ml`

`infer_full` を呼ぶように変更（または OCaml 側で borrow_check を呼ぶ）:

```ocaml
(* 型チェック + 借用チェック *)
let check_fn fenv f =
  match infer fenv f with
  | Infer_err err -> Error err
  | Infer_ok _    ->
      let bs_init = [] in
      let gamma = params_ctx f.fn_params in
      match borrow_check fenv bs_init gamma f.fn_body with
      | Infer_err err -> Error err
      | Infer_ok _    -> Ok ()
```

### エラーメッセージ追加

```ocaml
| ErrBorrowConflict id ->
    Printf.sprintf "borrow conflict: %s is already borrowed" (string_of_ident id)
```

---

## 8. テスト追加

### valid（既存 tests/valid/borrow/ を拡張）

- `multiple_shared.facet` — 同一変数への `&x` を 2 回取っても OK
  ```
  fn f(x: unrestricted isize) -> unrestricted () {
      let r1: unrestricted &unrestricted isize = (&x);
      let r2: unrestricted &unrestricted isize = (&x);
      ()
  }
  ```
- `shared_then_mut_disjoint.facet` — r1 の scope が終わった後 `&mut x` が取れる（lexical release）
  ```
  fn f(mut x: unrestricted isize) -> unrestricted () {
      let r1: unrestricted &unrestricted isize = (&x);
      let _: unrestricted () = (drop r1);  (* r1 を明示 drop しても scope は変わらない *)
      ...
  }
  ```

### invalid（`tests/invalid/borrow_error/` に追加）

- `mut_while_shared.facet` — 共有借用がアクティブな間に `&mut x` はエラー
  ```
  fn f(mut x: unrestricted isize) -> unrestricted &mut unrestricted isize {
      let r_shared: unrestricted &unrestricted isize = (&x);
      (&mut x)   (* エラー: x は既に共有借用されている *)
  }
  ```
- `double_mut.facet` — `&mut x` が 2 つはエラー
  ```
  fn f(mut x: unrestricted isize) -> unrestricted () {
      let r1: unrestricted &mut unrestricted isize = (&mut x);
      let r2: unrestricted &mut unrestricted isize = (&mut x);  (* エラー *)
      ()
  }
  ```
- `shared_after_mut.facet` — `&mut x` の後に `&x` はエラー（x がまだ mut 借用されている）
  ```
  fn f(mut x: unrestricted isize) -> unrestricted () {
      let r_mut: unrestricted &mut unrestricted isize = (&mut x);
      let r_shared: unrestricted &unrestricted isize = (&x);  (* エラー *)
      ()
  }
  ```

---

### 参照経由の replace / assign（`place` 拡張が前提）

> **注意**: この機能は `place` 型（現在は `ident` のみ）を `PDeref : ident -> place` に拡張することを要件とする。
> v2 の borrow_ok・borrow_check が完成した後の追加実装として計画する。

#### 必要な Rocq 変更（place 拡張）

```coq
(* Syntax.v: place に PDeref を追加 *)
(* 現在: Definition place := ident. *)
Inductive place : Type :=
  | PVar   : ident -> place    (* 直接変数: x *)
  | PDeref : ident -> place.   (* 参照を通じたアクセス: *r *)

(* TypingRules.v: T_Replace_Deref *)
(* r: &'a mut T が条件。T_Replace_Deref は T_Replace を PDeref に拡張する *)
| T_Replace_Deref : forall Γ Γ' r T T_new la e_new,
    ctx_lookup r Γ = Some (MkTy _ (TRef la RUnique T), false) ->
    typed fenv Γ e_new T_new Γ' ->
    ty_core T_new = ty_core T ->
    usage_sub (ty_usage T_new) (ty_usage T) ->
    typed fenv Γ (EReplace (PDeref r) e_new) T Γ'

(* TypingRules.v: T_Assign_Deref *)
| T_Assign_Deref : forall Γ Γ' r T T_new la e_new,
    ctx_lookup r Γ = Some (MkTy _ (TRef la RUnique T), false) ->
    ty_usage T <> ULinear ->      (* linear な古い値を暗黙 drop 禁止 *)
    typed fenv Γ e_new T_new Γ' ->
    ty_core T_new = ty_core T ->
    usage_sub (ty_usage T_new) (ty_usage T) ->
    typed fenv Γ (EAssign (PDeref r) e_new) (MkTy UUnrestricted TUnits) Γ'
```

> `T_Replace_Deref` は `r` を消費しない（参照は unrestricted なのでコピー可能）。
> `T_Assign_Deref` は `ty_usage T <> ULinear` を要求（linear な古い値を暗黙 drop できないため）。

#### 追加構文（OCaml パーサー）

```
atom_expr:
  | LPAREN; KW_REPLACE; STAR; r = ID; e = atom_expr; RPAREN
    { NReplace_Deref (r, e) }
  | LPAREN; STAR; r = ID; EQUAL; e = atom_expr; RPAREN
    { NAssign_Deref (r, e) }
```

#### valid テスト（`tests/valid/replace/`）

- `replace_via_mut_ref.facet` — mutable reference を通じた replace
  ```
  fn f(mut x: unrestricted isize) -> unrestricted isize {
      let r: unrestricted &mut unrestricted isize = (&mut x);
      let old: unrestricted isize = (replace *r 42);
      old
  }
  ```
  `r` が `&mut` → `T_Replace_Deref` が適用。古い値（42 以前の x の値）を返す。

- `replace_linear_via_mut_ref.facet` — linear 変数を mutable reference 経由で replace
  ```
  fn f(mut x: linear isize) -> unrestricted () {
      let r: unrestricted &mut linear isize = (&mut x);
      let old: linear isize = (replace *r 99);
      (drop old);
      (drop x)
  }
  ```
  `r` が `&mut linear isize`。replace で返った old（linear）を drop、最後に x も drop。

- `assign_via_mut_ref.facet` — mutable reference を通じた assign（古い値は unrestricted）
  ```
  fn f(mut x: unrestricted isize) -> unrestricted () {
      let r: unrestricted &mut unrestricted isize = (&mut x);
      (*r = 42);
      ()
  }
  ```
  unrestricted な古い値は暗黙 drop。unit を返す。

#### invalid テスト（`tests/invalid/replace_error/` または `borrow_error/`）

- `replace_via_shared_ref.facet` — shared reference を通じた replace はエラー
  ```
  fn f(x: unrestricted isize) -> unrestricted isize {
      let r: unrestricted &unrestricted isize = (&x);
      let old: unrestricted isize = (replace *r 42);
      old
  }
  ```
  エラー: `r` は `&T`（shared reference）。`T_Replace_Deref` は `&mut T` のみ適用可能。

- `assign_via_shared_ref.facet` — shared reference を通じた assign はエラー
  ```
  fn f(x: unrestricted isize) -> unrestricted () {
      let r: unrestricted &unrestricted isize = (&x);
      (*r = 42);
      ()
  }
  ```
  エラー: `r` は `&T`（shared reference）。mutable reference にのみ書き込み可能。

- `assign_linear_via_mut_ref.facet` — linear な古い値を暗黙 drop する assign はエラー
  ```
  fn f(mut x: linear isize) -> unrestricted () {
      let r: unrestricted &mut linear isize = (&mut x);
      (*r = 99);   (* エラー: linear な古い値を暗黙 drop できない *)
      (drop x)
  }
  ```
  エラー: `T_Assign_Deref` は `ty_usage T <> ULinear` を要求。linear 値は明示 drop が必要。
  代替: `(replace *r 99)` で old を受け取り `(drop old)` する。

---

## 9. 影響範囲まとめ

| ファイル | 変更内容 | 重さ |
|---------|---------|------|
| `TypingRules.v` | `borrow_entry`, `borrow_state`, 補助関数, `borrow_ok` 追加 | 大 |
| `TypeChecker.v` | `ErrBorrowConflict`, `borrow_check`, `borrow_check_args` 追加 | 大 |
| `BorrowCheckSoundness.v` | 新規ファイル: `borrow_check_sound`, `borrow_check_complete` | 大 |
| `_CoqProject` | `BorrowCheckSoundness.v` 追加 | 小 |
| `ocaml/main.ml` | `borrow_check` 呼び出し追加, `ErrBorrowConflict` エラーメッセージ | 小 |
| `fixtures/TypeChecker.ml` | `make` による自動再生成 | 自動 |

**変更なし**: `Syntax.v`, `OperationalSemantics.v`, `AlphaRenaming.v`,
`CheckerSoundness.v`, `CheckerUsageSoundness.v`, `ocaml/ast.ml`, `ocaml/parser.mly` など

---

## 10. 既知の制限（Accepted Gaps）

### Gap 1: エイリアス借用の追跡なし

参照を別変数にコピーすると、元の参照の scope exit 時に借用が解放されるが、
コピー先の変数はまだ参照を保持している。例:

```
let r1 = &x;
let r2 = r1;    (* r2 も &x を保持 *)
(* r1 の scope が終わっても r2 経由で x が借用されている *)
let rm = &mut x; (* borrow_check は誤って OK にするかもしれない *)
```

**対処**: v3 で alias tracking を実装するまでは accepted gap として文書化。

### Gap 2: if 分岐の BorrowState が異なる場合のリジェクト

両分岐で BorrowState が一致しない場合 `ErrContextCheckFailed` を返す。
これは分岐によって異なる変数を借用するプログラムを reject する可能性がある。

```
if cond { let r = &x; use(r) } else { let r2 = &y; use(r2) }
(* BS2 ≠ BS3 なのでリジェクトされる（両分岐でアクティブな借用が異なる） *)
```

**対処**: if rule の BorrowState merge 戦略を改善するか、scope exit release を if 分岐にも適用。v3 で対応。

### Gap 3: ELet の scope exit で解放されるのは直接の e1 の借用のみ

`e2` 内のサブ let が追加した借用は e2 の scope exit で解放されるが、
その解放分が最終 BS に正しく反映されるかは `bs_remove_all` の正確な動作に依存。

---

## 11. 検証基準

1. `cd rocq && make` が全ファイルエラーなしでコンパイルされる
2. `dune build` が成功する
3. 既存の全テスト（valid/invalid）が引き続き合格する
4. 新規 valid テストが合格する
5. 新規 invalid テストが正しくエラー（`ErrBorrowConflict`）を返す
6. `BorrowCheckSoundness.v` が `Admitted` なしでコンパイルされる

---

## 今後の拡張（v3 以降）

```
v3: Alias tracking と Re-borrow
    - エイリアス参照の scope を追跡
    - &mut T → &T の downgrade re-borrow
    - &mut T → &mut T の re-borrow

v4: Safety theorems
    - BorrowState が runtime の aliasing と一致することの証明
    - no dangling reference（lifetime と組み合わせ）
```
