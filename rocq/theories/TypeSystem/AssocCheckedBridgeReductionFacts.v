From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules AssocCompatibility.

Definition ty_compatible_assoc_checked_reduces_to_assoc
    (env : global_env) (Ω : outlives_ctx) : Prop :=
  forall actual expected,
    ty_compatible_assoc_checked env Ω actual expected ->
    ty_compatible_assoc env Ω actual expected.

Lemma typed_args_assoc_checked_reduces_to_assoc :
  forall env fenv Ω n Γ args ps Γ',
    ty_compatible_assoc_checked_reduces_to_assoc env Ω ->
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    typed_args_assoc env fenv Ω n Γ args ps Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.
