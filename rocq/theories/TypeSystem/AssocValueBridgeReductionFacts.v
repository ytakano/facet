From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker
  AssocValueTypingFacts
  AssocStructFieldBridgeReductionFacts AssocEnvBridgeReductionFacts.

Lemma typed_value_assoc_checked_reduces_to_plain :
  forall env fenv Ω n Γ e expected Γ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_value_assoc_checked env fenv Ω n Γ e expected Γ' ->
    exists actual,
      typed fenv Ω n Γ e actual Γ' /\
      ty_compatible Ω actual expected.
Proof.
  intros env fenv Ω n Γ e expected Γ' Hcompat Hvalue.
  destruct (typed_value_assoc_checked_inv _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split; eauto.
Qed.

Lemma typed_value_assoc_checked_reduces_to_bool :
  forall env fenv Ω n Γ e expected Γ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_value_assoc_checked env fenv Ω n Γ e expected Γ' ->
    exists actual,
      typed fenv Ω n Γ e actual Γ' /\
      ty_compatible_b Ω actual expected = true.
Proof.
  intros env fenv Ω n Γ e expected Γ' Hcompat Hvalue.
  destruct (typed_value_assoc_checked_inv _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split; eauto.
Qed.
