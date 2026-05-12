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

(* ------------------------------------------------------------------ *)
(* Well-formed lifetime                                                 *)
(* ------------------------------------------------------------------ *)

(* wf_lifetime Δ l holds when l is a valid lifetime in Δ.             *)
Inductive wf_lifetime (Δ : region_ctx) : lifetime -> Prop :=
| WF_LStatic : wf_lifetime Δ LStatic
| WF_LVar    : forall n, In (LVar n) Δ -> wf_lifetime Δ (LVar n).
