From Stdlib Require Import List PeanoNat Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Lifetime                                                             *)
(* ------------------------------------------------------------------ *)

(* LStatic is the 'static lifetime that outlives all others.           *)
(* LVar n  represents the n-th lifetime parameter (0-indexed).         *)
(* LBound n represents the n-th lifetime bound by a higher-rank type.  *)
Inductive lifetime : Type :=
| LStatic
| LVar : nat -> lifetime
| LBound : nat -> lifetime.

Definition lifetime_eqb (l1 l2 : lifetime) : bool :=
  match l1, l2 with
  | LStatic,  LStatic  => true
  | LVar n1, LVar n2   => Nat.eqb n1 n2
  | LBound n1, LBound n2 => Nat.eqb n1 n2
  | _,        _        => false
  end.

Lemma lifetime_eqb_eq : forall l1 l2,
  lifetime_eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros l1 l2. split.
  - destruct l1, l2; simpl; intro H.
    + reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + apply Nat.eqb_eq in H. subst. reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + apply Nat.eqb_eq in H. subst. reflexivity.
  - intros <-. destruct l1; simpl.
    + reflexivity.
    + apply Nat.eqb_refl.
    + apply Nat.eqb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Region context                                                       *)
(* ------------------------------------------------------------------ *)

(* A region context Δ is a list of in-scope lifetime variables.        *)
Definition region_ctx := list lifetime.

(* ------------------------------------------------------------------ *)
(* Outlives relation                                                    *)
(* ------------------------------------------------------------------ *)

(* outlives Ω a b means "'a outlives 'b" (a lives at least as long as b)
   under explicit constraints Ω. Notation: 'a : 'b corresponds to an
   explicit pair (a, b) in Ω.                                           *)
Definition outlives_ctx := list (lifetime * lifetime).

Inductive outlives (Ω : outlives_ctx) : lifetime -> lifetime -> Prop :=
| Outlives_refl  : forall a,     outlives Ω a a
| Outlives_trans : forall a b c, outlives Ω a b -> outlives Ω b c -> outlives Ω a c
| Outlives_static : forall a,    outlives Ω LStatic a
| Outlives_constraint : forall a b, In (a, b) Ω -> outlives Ω a b.

Definition outlives_direct_b (Ω : outlives_ctx) (a b : lifetime) : bool :=
  lifetime_eqb a b ||
  match a with
  | LStatic => true
  | LVar _ | LBound _ => existsb (fun '(x, y) => lifetime_eqb a x && lifetime_eqb b y) Ω
  end.

Fixpoint outlives_b_fuel (fuel : nat) (Ω : outlives_ctx) (a b : lifetime) : bool :=
  outlives_direct_b Ω a b ||
  match fuel with
  | O => false
  | S fuel' =>
      existsb
        (fun '(x, y) => lifetime_eqb a x && outlives_b_fuel fuel' Ω y b)
        Ω
  end.

Definition outlives_b (Ω : outlives_ctx) (a b : lifetime) : bool :=
  outlives_b_fuel (length Ω) Ω a b.

Lemma outlives_direct_b_sound : forall Ω a b,
  outlives_direct_b Ω a b = true -> outlives Ω a b.
Proof.
  intros Ω a b H.
  unfold outlives_direct_b in H.
  apply orb_true_iff in H as [Heq | Hdirect].
  - apply lifetime_eqb_eq in Heq. subst. apply Outlives_refl.
  - destruct a.
    + apply Outlives_static.
    + apply existsb_exists in Hdirect as [[x y] [Hin Hxy]].
      apply andb_true_iff in Hxy as [Hx Hy].
      apply lifetime_eqb_eq in Hx. apply lifetime_eqb_eq in Hy. subst.
      apply Outlives_constraint. exact Hin.
    + apply existsb_exists in Hdirect as [[x y] [Hin Hxy]].
      apply andb_true_iff in Hxy as [Hx Hy].
      apply lifetime_eqb_eq in Hx. apply lifetime_eqb_eq in Hy. subst.
      apply Outlives_constraint. exact Hin.
Qed.

Lemma outlives_b_fuel_sound : forall fuel Ω a b,
  outlives_b_fuel fuel Ω a b = true -> outlives Ω a b.
Proof.
  induction fuel as [|fuel IH]; intros Ω a b H; simpl in H.
  - apply orb_true_iff in H as [Hdirect | Hfalse].
    + apply outlives_direct_b_sound. exact Hdirect.
    + discriminate.
  - apply orb_true_iff in H as [Hdirect | Hstep].
    + apply outlives_direct_b_sound. exact Hdirect.
    + apply existsb_exists in Hstep as [[x y] [Hin Hxy]].
      apply andb_true_iff in Hxy as [Hx Hrec].
      apply lifetime_eqb_eq in Hx. subst x.
      eapply Outlives_trans.
      * apply Outlives_constraint. exact Hin.
      * apply (IH Ω y b). exact Hrec.
Qed.

Lemma outlives_b_sound : forall Ω a b,
  outlives_b Ω a b = true -> outlives Ω a b.
Proof.
  intros Ω a b H. unfold outlives_b in H.
  eapply outlives_b_fuel_sound. exact H.
Qed.

Example outlives_b_static_var :
  outlives_b [] LStatic (LVar 0) = true.
Proof. reflexivity. Qed.

Example outlives_b_var_static_false :
  outlives_b [] (LVar 0) LStatic = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Well-formed lifetime                                                 *)
(* ------------------------------------------------------------------ *)

(* wf_lifetime Δ l holds when l is a valid lifetime in Δ.             *)
Inductive wf_lifetime (Δ : region_ctx) : lifetime -> Prop :=
| WF_LStatic : wf_lifetime Δ LStatic
| WF_LVar    : forall n, In (LVar n) Δ -> wf_lifetime Δ (LVar n)
| WF_LBound  : forall n, In (LBound n) Δ -> wf_lifetime Δ (LBound n).
