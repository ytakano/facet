From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker EnvStructuralRules
  AssocCompatibility AssocEnvStructural
  AssocCheckedBridgeReductionFacts
  AssocStructFieldBridgeReductionFacts AssocEnvBridgeReductionFacts.

Lemma typed_value_env_structural_assoc_reduces_to_plain :
  forall env Ω n Σ e expected Σ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_value_env_structural_assoc env Ω n Σ e expected Σ' ->
    exists actual,
      typed_env_structural env Ω n Σ e actual Σ' /\
      ty_compatible Ω actual expected.
Proof.
  intros env Ω n Σ e expected Σ' Hcompat Hvalue.
  destruct (typed_value_env_structural_assoc_inv _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split; eauto.
Qed.

Lemma typed_value_env_structural_assoc_reduces_to_bool :
  forall env Ω n Σ e expected Σ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_value_env_structural_assoc env Ω n Σ e expected Σ' ->
    exists actual,
      typed_env_structural env Ω n Σ e actual Σ' /\
      ty_compatible_b Ω actual expected = true.
Proof.
  intros env Ω n Σ e expected Σ' Hcompat Hvalue.
  destruct (typed_value_env_structural_assoc_inv _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split; eauto.
Qed.

Lemma typed_value_roots_assoc_reduces_to_plain :
  forall env Ω n R Σ e expected Σ' R' roots,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_value_roots_assoc env Ω n R Σ e expected Σ' R' roots ->
    exists actual,
      typed_env_roots env Ω n R Σ e actual Σ' R' roots /\
      ty_compatible Ω actual expected.
Proof.
  intros env Ω n R Σ e expected Σ' R' roots Hcompat Hvalue.
  destruct (typed_value_roots_assoc_inv _ _ _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split; eauto.
Qed.

Lemma typed_value_roots_assoc_reduces_to_bool :
  forall env Ω n R Σ e expected Σ' R' roots,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_value_roots_assoc env Ω n R Σ e expected Σ' R' roots ->
    exists actual,
      typed_env_roots env Ω n R Σ e actual Σ' R' roots /\
      ty_compatible_b Ω actual expected = true.
Proof.
  intros env Ω n R Σ e expected Σ' R' roots Hcompat Hvalue.
  destruct (typed_value_roots_assoc_inv _ _ _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split; eauto.
Qed.
