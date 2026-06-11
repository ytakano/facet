From Facet.TypeSystem Require Import
  Types Syntax Program TypingRules AssocCompatibility
  AssocEnumPayloadTypingFacts AssocCheckedBridgeReductionFacts.
From Stdlib Require Import List.

Lemma typed_enum_payloads_assoc_checked_reduces_to_assoc :
  forall env fenv Ω n lts variant_lts args Γ payloads fields Γ',
    ty_compatible_assoc_checked_reduces_to_assoc env Ω ->
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads fields Γ' ->
    typed_args_assoc env fenv Ω n Γ payloads
      (params_of_tys
        (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)) Γ'.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads fields Γ'
    Hcompat Hpayloads.
  unfold typed_enum_payloads_assoc_checked in Hpayloads.
  eapply typed_args_assoc_checked_reduces_to_assoc; eauto.
Qed.
