From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker
  AssocCheckedBridgeReductionFacts
  AssocStructFieldBridgeReductionFacts AssocEnvBridgeReductionFacts
  AssocTraitMethodResolutionFacts AssocTraitMethodSigBridgeReductionFacts.
From Stdlib Require Import List.
Import ListNotations.

Lemma trait_method_resolution_assoc_checked_reduces_to_plain :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    ty_compatible_assoc_checked_reduces_to_plain env (fn_outlives fn) ->
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn ->
    lookup_trait trait_name env = Some t /\
    Nat.eqb (List.length trait_args) (trait_type_params t) = true /\
    find_trait_method_sig method_name (trait_methods t) = Some sig /\
    matching_impls trait_name trait_args for_ty (env_impls env) = [impl] /\
    find_impl_method_def method_name (impl_methods impl) = Some fn /\
    resolve_trait_method_impl env trait_name trait_args for_ty method_name =
      Some impl /\
    resolve_trait_method_def env trait_name trait_args for_ty method_name =
      Some fn /\
    fst (fn_name fn) = trait_method_name sig /\
    fn_lifetimes fn = trait_method_lifetimes sig /\
    fn_type_params fn = trait_method_type_params sig /\
    fn_bounds fn = trait_method_bounds sig /\
    fn_captures fn = [] /\
    Forall2
      (fun sig_param impl_param =>
        param_mutability sig_param = param_mutability impl_param /\
        param_name sig_param = param_name impl_param /\
        ty_compatible (fn_outlives fn)
          (param_ty impl_param) (param_ty sig_param))
      (trait_method_params sig) (fn_params fn) /\
    ty_compatible (fn_outlives fn) (fn_ret fn) (trait_method_ret sig).
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn
    Hcompat Hres.
  destruct (trait_method_resolution_assoc_checked_inv
    _ _ _ _ _ _ _ _ _ Hres)
    as [Htrait [Harity [Hsig [Himpls [Hfn [Hresolve_impl
      [Hresolve_def Hchecked]]]]]]].
  destruct (trait_method_sig_assoc_checked_reduces_to_plain
    env sig fn Hcompat Hchecked)
    as [Hname [Hlts [Htparams [Hbounds [Hcaptures [Hparams Hret]]]]]].
  repeat split; assumption.
Qed.

Lemma trait_method_resolution_assoc_checked_reduces_to_bool :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    ty_compatible_assoc_checked_reduces_to_bool env (fn_outlives fn) ->
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn ->
    lookup_trait trait_name env = Some t /\
    Nat.eqb (List.length trait_args) (trait_type_params t) = true /\
    find_trait_method_sig method_name (trait_methods t) = Some sig /\
    matching_impls trait_name trait_args for_ty (env_impls env) = [impl] /\
    find_impl_method_def method_name (impl_methods impl) = Some fn /\
    resolve_trait_method_impl env trait_name trait_args for_ty method_name =
      Some impl /\
    resolve_trait_method_def env trait_name trait_args for_ty method_name =
      Some fn /\
    fst (fn_name fn) = trait_method_name sig /\
    fn_lifetimes fn = trait_method_lifetimes sig /\
    fn_type_params fn = trait_method_type_params sig /\
    fn_bounds fn = trait_method_bounds sig /\
    fn_captures fn = [] /\
    Forall2
      (fun sig_param impl_param =>
        param_mutability sig_param = param_mutability impl_param /\
        param_name sig_param = param_name impl_param /\
        ty_compatible_b (fn_outlives fn)
          (param_ty impl_param) (param_ty sig_param) = true)
      (trait_method_params sig) (fn_params fn) /\
    ty_compatible_b (fn_outlives fn) (fn_ret fn)
      (trait_method_ret sig) = true.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn
    Hcompat Hres.
  destruct (trait_method_resolution_assoc_checked_inv
    _ _ _ _ _ _ _ _ _ Hres)
    as [Htrait [Harity [Hsig [Himpls [Hfn [Hresolve_impl
      [Hresolve_def Hchecked]]]]]]].
  destruct (trait_method_sig_assoc_checked_reduces_to_bool
    env sig fn Hcompat Hchecked)
    as [Hname [Hlts [Htparams [Hbounds [Hcaptures [Hparams Hret]]]]]].
  repeat split; assumption.
Qed.
