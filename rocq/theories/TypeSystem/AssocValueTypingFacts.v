From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase
  AssocCompatibility AlphaTyping.

(* Prop-level single-value typing that stores only the lightweight checked
   associated-projection compatibility witness. *)
Inductive typed_value_assoc_checked
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    (Γ : ctx) (e : expr) (expected : Ty) (Γ' : ctx) : Prop :=
  | TValueAssocChecked : forall actual,
      typed fenv Ω n Γ e actual Γ' ->
      ty_compatible_assoc_checked env Ω actual expected ->
      typed_value_assoc_checked env fenv Ω n Γ e expected Γ'.

Lemma typed_value_assoc_checked_inv :
  forall env fenv Ω n Γ e expected Γ',
    typed_value_assoc_checked env fenv Ω n Γ e expected Γ' ->
    exists actual,
      typed fenv Ω n Γ e actual Γ' /\
      ty_compatible_assoc_checked env Ω actual expected.
Proof.
  intros env fenv Ω n Γ e expected Γ' Hvalue.
  inversion Hvalue as [actual Htyped Hcompat]; subst.
  exists actual. split; assumption.
Qed.

Lemma typed_value_assoc_checked_same_bindings :
  forall env fenv Ω n Γ e expected Γ',
    typed_value_assoc_checked env fenv Ω n Γ e expected Γ' ->
    ctx_same_bindings Γ Γ'.
Proof.
  intros env fenv Ω n Γ e expected Γ' Hvalue.
  destruct (typed_value_assoc_checked_inv _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped _]].
  destruct typed_same_bindings as [Htyped_same _].
  eapply Htyped_same. exact Htyped.
Qed.

Lemma typed_value_assoc_checked_intro :
  forall env fenv Ω n Γ e actual Γ' expected,
    typed fenv Ω n Γ e actual Γ' ->
    ty_compatible_assoc_checked env Ω actual expected ->
    typed_value_assoc_checked env fenv Ω n Γ e expected Γ'.
Proof.
  intros env fenv Ω n Γ e actual Γ' expected Htyped Hcompat.
  econstructor; eauto.
Qed.
