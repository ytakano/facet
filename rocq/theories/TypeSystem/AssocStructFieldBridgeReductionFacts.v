From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules AssocCompatibility
  AssocCheckedBridgeReductionFacts AssocStructFieldTypingFacts.
From Stdlib Require Import List String.
Import ListNotations.

Lemma typed_struct_fields_assoc_checked_reduces_to_struct_fields :
  forall env fenv Ω n lts args Γ fields defs Γ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_struct_fields_assoc_checked env fenv Ω n lts args Γ fields defs Γ' ->
    typed_struct_fields fenv Ω n lts args Γ fields defs Γ'.
Proof.
  intros env fenv Ω n lts args Γ fields defs Γ' Hcompat Hfields.
  induction Hfields.
  - constructor.
  - econstructor; eauto.
Qed.
