From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker AssocCompatibility
  AssocHrtFacts AssocCheckedBridgeSoundness
  AssocHrtBridgeReductionFacts AssocEnumPayloadTypingFacts AssocEnumPayloadBridgeReductionFacts.
From Stdlib Require Import List.

Lemma assoc_checked_arg_tys_sound :
  forall env Ω arg_tys param_tys,
    assoc_checked_arg_tys env Ω arg_tys param_tys ->
    Forall2
      (fun actual expected => ty_compatible_assoc env Ω actual expected)
      arg_tys param_tys /\
    length arg_tys = length param_tys.
Proof.
  intros env Ω arg_tys param_tys Hargs.
  eapply assoc_checked_arg_tys_reduces_to_assoc.
  - apply ty_compatible_assoc_checked_reduces_to_assoc_proved.
  - exact Hargs.
Qed.

Lemma typed_enum_payloads_assoc_checked_sound :
  forall env fenv Ω n lts variant_lts args Γ payloads fields Γ',
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads fields Γ' ->
    typed_args_assoc env fenv Ω n Γ payloads
      (params_of_tys
        (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)) Γ'.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads fields Γ' Hpayloads.
  eapply typed_enum_payloads_assoc_checked_reduces_to_assoc.
  - apply ty_compatible_assoc_checked_reduces_to_assoc_proved.
  - exact Hpayloads.
Qed.
