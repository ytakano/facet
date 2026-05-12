From Facet.TypeSystem Require Import Types.
From Stdlib Require Import String ZArith Bool PeanoNat.

Definition ident := (string * nat)%type.

Definition ident_eqb (x y : ident) : bool :=
  String.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

Lemma ident_eqb_eq : forall x y,
  ident_eqb x y = true <-> x = y.
Proof.
  intros [xs xn] [ys yn]. unfold ident_eqb. simpl.
  rewrite andb_true_iff, String.eqb_eq, Nat.eqb_eq.
  split.
  - intros [Hstr Hnat]. subst. reflexivity.
  - intros H. inversion H. split; reflexivity.
Qed.

Lemma ident_eqb_neq : forall x y,
  ident_eqb x y = false <-> x <> y.
Proof.
  intros x y.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst.
    split; intros H; [discriminate | contradiction].
  - split; intros H.
    + intro Heqxy.
      apply ident_eqb_eq in Heqxy.
      rewrite Heqxy in Heq. discriminate.
    + reflexivity.
Qed.

Lemma ident_eqb_refl : forall x,
  ident_eqb x x = true.
Proof.
  intro x. apply ident_eqb_eq. reflexivity.
Qed.

Inductive literal : Type :=
| LInt   : Z -> literal
| LFloat : string -> literal
| LBool  : bool -> literal.

Inductive place : Type :=
| PVar   : ident -> place
| PDeref : place -> place.

Inductive expr : Type :=
| EUnit     : expr
| ELit      : literal -> expr
| EVar      : ident -> expr
| ELet      : mutability -> ident -> Ty -> expr -> expr -> expr
| ELetInfer : mutability -> ident -> expr -> expr -> expr
| ECall     : ident -> list expr -> expr
| EReplace  : place -> expr -> expr
| EAssign   : place -> expr -> expr
| EBorrow   : ref_kind -> place -> expr
| EDeref    : expr -> expr
| EDrop     : expr -> expr
| EIf       : expr -> expr -> expr -> expr.

Record param : Type := MkParam {
  param_mutability : mutability;
  param_name       : ident;
  param_ty         : Ty
}.

Record fn_def : Type := MkFnDef {
  fn_name   : ident;
  fn_params : list param;
  fn_ret    : Ty;
  fn_body   : expr
}.

Definition Syntax := list fn_def.
