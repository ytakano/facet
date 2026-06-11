From Facet.TypeSystem Require Import
  Types Syntax Program TypingRules CheckerBase AssocCompatibility
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

Lemma typed_enum_payloads_assoc_checked_reduces_to_plain :
  forall env fenv Ω n lts variant_lts args Γ payloads fields Γ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads fields Γ' ->
    typed_args fenv Ω n Γ payloads
      (params_of_tys
        (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)) Γ'.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads fields Γ'
    Hcompat Hpayloads.
  unfold typed_enum_payloads_assoc_checked in Hpayloads.
  eapply typed_args_assoc_checked_reduces_to_plain; eauto.
Qed.

Lemma typed_enum_payloads_assoc_checked_reduces_to_bool :
  forall env fenv Ω n lts variant_lts args Γ payloads fields Γ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads fields Γ' ->
    Forall2
      (fun payload expected =>
        exists actual Γin Γout,
          typed fenv Ω n Γin payload actual Γout /\
          ty_compatible_b Ω actual expected = true)
      payloads
      (map (instantiate_enum_variant_field_ty lts variant_lts args) fields).
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads fields Γ'
    Hcompat Hpayloads.
  unfold typed_enum_payloads_assoc_checked in Hpayloads.
  pose proof
    (typed_args_assoc_checked_reduces_to_bool
      env fenv Ω n Γ payloads
      (params_of_tys
        (map (instantiate_enum_variant_field_ty lts variant_lts args) fields))
      Γ' Hcompat Hpayloads) as Hpayloads_bool.
  clear Hpayloads Hcompat.
  induction (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)
    as [|expected expected_tail IH] in payloads, Hpayloads_bool |- *.
  - inversion Hpayloads_bool; subst. constructor.
  - destruct payloads as [|payload payloads_tail].
    + inversion Hpayloads_bool.
    + inversion Hpayloads_bool; subst.
      constructor.
      * destruct H2 as [actual [Γin [Γout [Htyped Hcompat]]]].
        exists actual, Γin, Γout. split; exact Htyped || exact Hcompat.
      * apply IH. exact H4.
Qed.
