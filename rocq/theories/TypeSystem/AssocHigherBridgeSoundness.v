From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker AssocCompatibility
  AssocHrtFacts AssocTraitMethodSigFacts AssocValueTypingFacts
  AssocCheckedBridgeSoundness CompatBoolSoundness
  AssocHrtBridgeReductionFacts AssocEnumPayloadTypingFacts AssocEnumPayloadBridgeReductionFacts.
From Stdlib Require Import List.
Import ListNotations.

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

Lemma trait_method_param_assoc_checked_sound :
  forall env Ω sig_param impl_param,
    trait_method_param_assoc_checked env Ω sig_param impl_param ->
    param_mutability sig_param = param_mutability impl_param /\
    param_name sig_param = param_name impl_param /\
    ty_compatible_assoc env Ω (param_ty impl_param) (param_ty sig_param).
Proof.
  intros env Ω sig_param impl_param Hparam.
  destruct Hparam as [Hmut [Hname Hcompat]].
  repeat split; try assumption.
  exact (ty_compatible_assoc_checked_sound
    env Ω (param_ty impl_param) (param_ty sig_param) Hcompat).
Qed.

Lemma trait_method_params_assoc_checked_sound :
  forall env Ω sig_params impl_params,
    trait_method_params_assoc_checked env Ω sig_params impl_params ->
    Forall2
      (fun sig_param impl_param =>
        param_mutability sig_param = param_mutability impl_param /\
        param_name sig_param = param_name impl_param /\
        ty_compatible_assoc env Ω
          (param_ty impl_param) (param_ty sig_param))
      sig_params impl_params.
Proof.
  intros env Ω sig_params impl_params Hparams.
  eapply Forall2_impl; [| exact Hparams].
  intros sig_param impl_param Hparam.
  apply trait_method_param_assoc_checked_sound. exact Hparam.
Qed.

Lemma trait_method_ret_assoc_checked_sound :
  forall env Ω sig impl,
    trait_method_ret_assoc_checked env Ω sig impl ->
    ty_compatible_assoc env Ω (fn_ret impl) (trait_method_ret sig).
Proof.
  intros env Ω sig impl Hret.
  exact (ty_compatible_assoc_checked_sound
    env Ω (fn_ret impl) (trait_method_ret sig) Hret).
Qed.

Lemma trait_method_sig_assoc_checked_sound :
  forall env sig impl,
    trait_method_sig_assoc_checked env sig impl ->
    fst (fn_name impl) = trait_method_name sig /\
    fn_lifetimes impl = trait_method_lifetimes sig /\
    fn_type_params impl = trait_method_type_params sig /\
    fn_bounds impl = trait_method_bounds sig /\
    fn_captures impl = [] /\
    Forall2
      (fun sig_param impl_param =>
        param_mutability sig_param = param_mutability impl_param /\
        param_name sig_param = param_name impl_param /\
        ty_compatible_assoc env (fn_outlives impl)
          (param_ty impl_param) (param_ty sig_param))
      (trait_method_params sig) (fn_params impl) /\
    ty_compatible_assoc env (fn_outlives impl) (fn_ret impl)
      (trait_method_ret sig).
Proof.
  intros env sig impl Hsig.
  destruct (trait_method_sig_assoc_checked_inv _ _ _ Hsig)
    as [Hname [Hlts [Htparams [Hbounds [Hcaptures [Hparams Hret]]]]]].
  repeat split; try assumption.
  - eapply Forall2_impl; [| exact Hparams].
    intros sig_param impl_param Hparam.
    destruct (trait_method_param_assoc_checked_sound
      env (fn_outlives impl) sig_param impl_param Hparam)
      as [Hmut [Hparam_name Hcompat]].
    repeat split; assumption.
  - apply trait_method_ret_assoc_checked_sound. exact Hret.
Qed.

Lemma typed_value_assoc_checked_sound :
  forall env fenv Ω n Γ e expected Γ',
    typed_value_assoc_checked env fenv Ω n Γ e expected Γ' ->
    exists actual,
      typed fenv Ω n Γ e actual Γ' /\
      ty_compatible_assoc env Ω actual expected.
Proof.
  intros env fenv Ω n Γ e expected Γ' Hvalue.
  destruct (typed_value_assoc_checked_inv _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hcompat]].
  exists actual. split.
  - exact Htyped.
  - exact (ty_compatible_assoc_checked_sound env Ω actual expected Hcompat).
Qed.
