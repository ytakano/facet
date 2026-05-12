From Stdlib Require Import List PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Lifetime                                                             *)
(* ------------------------------------------------------------------ *)

(* LStatic is the 'static lifetime that outlives all others.           *)
(* LVar n  represents the n-th lifetime parameter (0-indexed).         *)
Inductive lifetime : Type :=
| LStatic
| LVar : nat -> lifetime.

Definition lifetime_eqb (l1 l2 : lifetime) : bool :=
  match l1, l2 with
  | LStatic,  LStatic  => true
  | LVar n1, LVar n2   => Nat.eqb n1 n2
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
    + apply Nat.eqb_eq in H. subst. reflexivity.
  - intros <-. destruct l1; simpl.
    + reflexivity.
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

(* outlives a b means "'a outlives 'b" (a lives at least as long as b). *)
(* Notation: 'a : 'b corresponds to outlives a b.                       *)
Inductive outlives : lifetime -> lifetime -> Prop :=
| Outlives_refl  : forall a,     outlives a a
| Outlives_trans : forall a b c, outlives a b -> outlives b c -> outlives a c
| Outlives_static : forall a,    outlives LStatic a.

Definition outlives_b (a b : lifetime) : bool :=
  match a, b with
  | LStatic, _ => true
  | LVar n, LVar m => Nat.eqb n m
  | LVar _, LStatic => false
  end.

Lemma outlives_b_sound : forall a b,
  outlives_b a b = true -> outlives a b.
Proof.
  intros a b H.
  destruct a, b; simpl in H; try discriminate.
  - apply Outlives_refl.
  - apply Outlives_static.
  - apply Nat.eqb_eq in H. subst. apply Outlives_refl.
Qed.

Example outlives_b_static_var :
  outlives_b LStatic (LVar 0) = true.
Proof. reflexivity. Qed.

Example outlives_b_var_static_false :
  outlives_b (LVar 0) LStatic = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Well-formed lifetime                                                 *)
(* ------------------------------------------------------------------ *)

(* wf_lifetime Δ l holds when l is a valid lifetime in Δ.             *)
Inductive wf_lifetime (Δ : region_ctx) : lifetime -> Prop :=
| WF_LStatic : wf_lifetime Δ LStatic
| WF_LVar    : forall n, In (LVar n) Δ -> wf_lifetime Δ (LVar n).
