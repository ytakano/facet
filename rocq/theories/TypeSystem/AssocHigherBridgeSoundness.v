From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker EnvStructuralRules AssocCompatibility
  AssocHrtFacts AssocTraitMethodSigFacts AssocTraitMethodResolutionFacts AssocValueTypingFacts
  AssocEnvStructural AssocEnvFnDefTypingFacts AssocEnvRootFnDefTypingFacts
  TypeSafetyCheckedRoots AssocEnvValueBridgeReductionFacts
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

Lemma trait_method_resolution_assoc_checked_sound :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
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
        ty_compatible_assoc env (fn_outlives fn)
          (param_ty impl_param) (param_ty sig_param))
      (trait_method_params sig) (fn_params fn) /\
    ty_compatible_assoc env (fn_outlives fn) (fn_ret fn)
      (trait_method_ret sig).
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn Hres.
  destruct (trait_method_resolution_assoc_checked_inv
    _ _ _ _ _ _ _ _ _ Hres)
    as [Htrait [Harity [Hsig [Himpls [Hfn [Hresolve_impl
      [Hresolve_def Hchecked]]]]]]].
  destruct (trait_method_sig_assoc_checked_sound env sig fn Hchecked)
    as [Hname [Hlts [Htparams [Hbounds [Hcaptures [Hparams Hret]]]]]].
  repeat split; assumption.
Qed.

Lemma typed_value_env_structural_assoc_sound :
  forall env Ω n Σ e expected Σ',
    typed_value_env_structural_assoc env Ω n Σ e expected Σ' ->
    exists actual,
      typed_env_structural env Ω n Σ e actual Σ' /\
      ty_compatible_assoc env Ω actual expected.
Proof.
  intros env Ω n Σ e expected Σ' Hvalue.
  destruct (typed_value_env_structural_assoc_inv _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split.
  - exact Htyped.
  - exact (ty_compatible_assoc_checked_sound env Ω actual expected Hchecked).
Qed.

Lemma typed_value_roots_assoc_sound :
  forall env Ω n R Σ e expected Σ' R' roots,
    typed_value_roots_assoc env Ω n R Σ e expected Σ' R' roots ->
    exists actual,
      typed_env_roots env Ω n R Σ e actual Σ' R' roots /\
      ty_compatible_assoc env Ω actual expected.
Proof.
  intros env Ω n R Σ e expected Σ' R' roots Hvalue.
  destruct (typed_value_roots_assoc_inv _ _ _ _ _ _ _ _ _ _ Hvalue)
    as [actual [Htyped Hchecked]].
  exists actual. split.
  - exact Htyped.
  - exact (ty_compatible_assoc_checked_sound env Ω actual expected Hchecked).
Qed.

Lemma typed_args_env_structural_assoc_sound :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    Forall2
      (fun e p =>
        exists actual Σin Σout,
          typed_env_structural env Ω n Σin e actual Σout /\
          ty_compatible_assoc env Ω actual (param_ty p))
      args ps /\
    length args = length ps.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  induction Hargs.
  - split; constructor.
  - destruct IHHargs as [Htail Hlen].
    split.
    + constructor.
      * exists T_e, Σ, Σ1. split.
        -- exact H.
        -- exact (ty_compatible_assoc_checked_sound
             env Ω T_e (param_ty p) H0).
      * exact Htail.
    + simpl. f_equal. exact Hlen.
Qed.

Lemma typed_args_roots_assoc_sound :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    Forall2
      (fun e p =>
        exists actual Rin Rnext Σin Σout roots,
          typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
          ty_compatible_assoc env Ω actual (param_ty p))
      args ps /\
    length args = length ps.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  induction Hargs.
  - split; constructor.
  - destruct IHHargs as [Htail Hlen].
    split.
    + constructor.
      * exists T_e, R, R1, Σ, Σ1, roots. split.
        -- exact H.
        -- exact (ty_compatible_assoc_checked_sound
             env Ω T_e (param_ty p) H0).
      * exact Htail.
    + simpl. f_equal. exact Hlen.
Qed.

Lemma typed_fields_env_structural_assoc_sound :
  forall env Ω n lts args Σ fields defs Σ',
    typed_fields_env_structural_assoc env Ω n lts args Σ fields defs Σ' ->
    Forall
      (fun f =>
        exists e_field actual Σin Σout,
          lookup_field_b (field_name f) fields = Some e_field /\
          typed_env_structural env Ω n Σin e_field actual Σout /\
          ty_compatible_assoc env Ω actual
            (instantiate_struct_field_ty lts args f))
      defs.
Proof.
  intros env Ω n lts args Σ fields defs Σ' Hfields.
  induction Hfields.
  - constructor.
  - constructor.
    + exists e_field, T_field, Σ, Σ1. repeat split.
      * exact H.
      * exact H0.
      * exact (ty_compatible_assoc_checked_sound
          env Ω T_field (instantiate_struct_field_ty lts args f) H1).
    + exact IHHfields.
Qed.

Lemma typed_fields_roots_assoc_sound :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_assoc env Ω n lts args R Σ fields defs Σ' R' roots ->
    Forall
      (fun f =>
        exists e_field actual Rin Rnext Σin Σout roots_field,
          lookup_field_b (field_name f) fields = Some e_field /\
          typed_env_roots env Ω n Rin Σin e_field actual Σout Rnext roots_field /\
          ty_compatible_assoc env Ω actual
            (instantiate_struct_field_ty lts args f))
      defs.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots Hfields.
  induction Hfields.
  - constructor.
  - constructor.
    + exists e_field, T_field, R, R1, Σ, Σ1, roots_field. repeat split.
      * exact H.
      * exact H0.
      * exact (ty_compatible_assoc_checked_sound
          env Ω T_field (instantiate_struct_field_ty lts args f) H1).
    + exact IHHfields.
Qed.

Lemma typed_fn_env_structural_assoc_checked_sound :
  forall env f,
    typed_fn_env_structural_assoc_checked env f ->
    exists T_body Gamma_out,
      typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) /\
      ty_compatible_assoc
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f Hfn.
  destruct (typed_fn_env_structural_assoc_checked_inv env f Hfn)
    as [T_body [Gamma_out [Htyped [Hcompat Hparams]]]].
  exists T_body, Gamma_out. repeat split; try assumption.
  exact (ty_compatible_assoc_checked_sound
    (global_env_with_local_bounds env (fn_bounds f))
    (fn_outlives f) T_body (fn_ret f) Hcompat).
Qed.

Lemma typed_fn_env_roots_assoc_checked_sound :
  forall env f R0 R_out roots,
    typed_fn_env_roots_assoc_checked env f R0 R_out roots ->
    exists T_body Gamma_out,
      typed_env_roots (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        R0 (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
      ty_compatible_assoc
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots Hfn.
  destruct (typed_fn_env_roots_assoc_checked_inv env f R0 R_out roots Hfn)
    as [T_body [Gamma_out [Htyped [Hcompat Hparams]]]].
  exists T_body, Gamma_out. repeat split; try assumption.
  exact (ty_compatible_assoc_checked_sound
    (global_env_with_local_bounds env (fn_bounds f))
    (fn_outlives f) T_body (fn_ret f) Hcompat).
Qed.

Lemma typed_fn_env_roots_checked_assoc_checked_sound :
  forall env f R0 R_out roots,
    typed_fn_env_roots_checked_assoc_checked env f R0 R_out roots ->
    exists T_body Gamma_out,
      typed_env_roots_checked (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        R0 (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
      ty_compatible_assoc
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots Hfn.
  destruct (typed_fn_env_roots_checked_assoc_checked_inv
    env f R0 R_out roots Hfn)
    as [T_body [Gamma_out [Htyped [Hcompat Hparams]]]].
  exists T_body, Gamma_out. repeat split; try assumption.
  exact (ty_compatible_assoc_checked_sound
    (global_env_with_local_bounds env (fn_bounds f))
    (fn_outlives f) T_body (fn_ret f) Hcompat).
Qed.
