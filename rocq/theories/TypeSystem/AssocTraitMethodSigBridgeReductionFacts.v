From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker
  AssocTraitMethodSigFacts
  AssocStructFieldBridgeReductionFacts AssocEnvBridgeReductionFacts.
From Stdlib Require Import List.
Import ListNotations.

Lemma trait_method_param_assoc_checked_reduces_to_plain :
  forall env Ω sig_param impl_param,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    trait_method_param_assoc_checked env Ω sig_param impl_param ->
    param_mutability sig_param = param_mutability impl_param /\
    param_name sig_param = param_name impl_param /\
    ty_compatible Ω (param_ty impl_param) (param_ty sig_param).
Proof.
  intros env Ω sig_param impl_param Hcompat Hparam.
  destruct Hparam as [Hmut [Hname Hty]].
  repeat split; eauto.
Qed.

Lemma trait_method_param_assoc_checked_reduces_to_bool :
  forall env Ω sig_param impl_param,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    trait_method_param_assoc_checked env Ω sig_param impl_param ->
    param_mutability sig_param = param_mutability impl_param /\
    param_name sig_param = param_name impl_param /\
    ty_compatible_b Ω (param_ty impl_param) (param_ty sig_param) = true.
Proof.
  intros env Ω sig_param impl_param Hcompat Hparam.
  destruct Hparam as [Hmut [Hname Hty]].
  repeat split; eauto.
Qed.

Lemma trait_method_params_assoc_checked_reduces_to_plain :
  forall env Ω sig_params impl_params,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    trait_method_params_assoc_checked env Ω sig_params impl_params ->
    Forall2
      (fun sig_param impl_param =>
        param_mutability sig_param = param_mutability impl_param /\
        param_name sig_param = param_name impl_param /\
        ty_compatible Ω (param_ty impl_param) (param_ty sig_param))
      sig_params impl_params.
Proof.
  intros env Ω sig_params impl_params Hcompat Hparams.
  eapply Forall2_impl; [| exact Hparams].
  intros sig_param impl_param Hparam.
  eapply trait_method_param_assoc_checked_reduces_to_plain; eauto.
Qed.

Lemma trait_method_params_assoc_checked_reduces_to_bool :
  forall env Ω sig_params impl_params,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    trait_method_params_assoc_checked env Ω sig_params impl_params ->
    Forall2
      (fun sig_param impl_param =>
        param_mutability sig_param = param_mutability impl_param /\
        param_name sig_param = param_name impl_param /\
        ty_compatible_b Ω (param_ty impl_param) (param_ty sig_param) = true)
      sig_params impl_params.
Proof.
  intros env Ω sig_params impl_params Hcompat Hparams.
  eapply Forall2_impl; [| exact Hparams].
  intros sig_param impl_param Hparam.
  eapply trait_method_param_assoc_checked_reduces_to_bool; eauto.
Qed.

Lemma trait_method_ret_assoc_checked_reduces_to_plain :
  forall env Ω sig impl,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    trait_method_ret_assoc_checked env Ω sig impl ->
    ty_compatible Ω (fn_ret impl) (trait_method_ret sig).
Proof.
  intros env Ω sig impl Hcompat Hret.
  apply Hcompat. exact Hret.
Qed.

Lemma trait_method_ret_assoc_checked_reduces_to_bool :
  forall env Ω sig impl,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    trait_method_ret_assoc_checked env Ω sig impl ->
    ty_compatible_b Ω (fn_ret impl) (trait_method_ret sig) = true.
Proof.
  intros env Ω sig impl Hcompat Hret.
  apply Hcompat. exact Hret.
Qed.

Lemma trait_method_sig_assoc_checked_reduces_to_plain :
  forall env sig impl,
    ty_compatible_assoc_checked_reduces_to_plain env (fn_outlives impl) ->
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
        ty_compatible (fn_outlives impl)
          (param_ty impl_param) (param_ty sig_param))
      (trait_method_params sig) (fn_params impl) /\
    ty_compatible (fn_outlives impl) (fn_ret impl) (trait_method_ret sig).
Proof.
  intros env sig impl Hcompat Hsig.
  destruct (trait_method_sig_assoc_checked_inv _ _ _ Hsig)
    as [Hname [Hlts [Htparams [Hbounds [Hcaptures [Hparams Hret]]]]]].
  repeat split; eauto using
    trait_method_params_assoc_checked_reduces_to_plain,
    trait_method_ret_assoc_checked_reduces_to_plain.
Qed.

Lemma trait_method_sig_assoc_checked_reduces_to_bool :
  forall env sig impl,
    ty_compatible_assoc_checked_reduces_to_bool env (fn_outlives impl) ->
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
        ty_compatible_b (fn_outlives impl)
          (param_ty impl_param) (param_ty sig_param) = true)
      (trait_method_params sig) (fn_params impl) /\
    ty_compatible_b (fn_outlives impl) (fn_ret impl)
      (trait_method_ret sig) = true.
Proof.
  intros env sig impl Hcompat Hsig.
  destruct (trait_method_sig_assoc_checked_inv _ _ _ Hsig)
    as [Hname [Hlts [Htparams [Hbounds [Hcaptures [Hparams Hret]]]]]].
  repeat split; eauto using
    trait_method_params_assoc_checked_reduces_to_bool,
    trait_method_ret_assoc_checked_reduces_to_bool.
Qed.
