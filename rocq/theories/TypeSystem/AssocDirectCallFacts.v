From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt TypeChecker AssocCompatibility
  AssocArgBoolFacts AssocEnvStructural AssocEnvArgSoundness
  AssocEnvRootArgSoundness AssocDirectCallHelpers EnvStructuralRules
  EnvTypingSoundness EnvRootSoundness AssocHigherBridgeSoundness.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware direct top-level call facts                              *)
(* ------------------------------------------------------------------ *)

Lemma infer_direct_call_assoc_checked_args :
  forall env Ω n fdef arg_tys T,
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists σ_acc σ params_subst,
      no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0 = true /\
      build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
        arg_tys (fn_params fdef) = Some σ_acc /\
      σ = finalize_subst σ_acc /\
      params_subst = apply_lt_params σ (fn_params fdef) /\
      check_args_assoc env Ω arg_tys params_subst = None /\
      T = apply_lt_ty σ (fn_ret fdef).
Proof.
  intros env Ω n fdef arg_tys T Hinfer.
  unfold infer_direct_call_assoc in Hinfer.
  destruct (no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0)
    eqn:Hgate; try discriminate.
  destruct (build_sigma (fn_lifetimes fdef)
    (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef))
    as [sigma_acc|] eqn:Hsigma; try discriminate.
  destruct (check_args_assoc env Ω arg_tys
    (apply_lt_params (finalize_subst sigma_acc) (fn_params fdef)))
    as [err|] eqn:Hcheck; try discriminate.
  destruct (forallb (wf_lifetime_b (mk_region_ctx n))
    (finalize_subst sigma_acc)) eqn:?; try discriminate.
  destruct (outlives_constraints_hold_b Ω
    (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)))
    eqn:?; try discriminate.
  inversion Hinfer; subst.
  exists sigma_acc, (finalize_subst sigma_acc),
    (apply_lt_params (finalize_subst sigma_acc) (fn_params fdef)).
  repeat split; try reflexivity; assumption.
Qed.

Lemma infer_direct_call_generic_assoc_checked_args :
  forall env Ω n fdef type_args arg_tys T,
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys =
      infer_ok T ->
    exists params_typed σ_acc σ params_subst,
      no_captures_b fdef &&
        Nat.eqb (Datatypes.length type_args) (fn_type_params fdef) = true /\
      check_struct_bounds env (fn_bounds fdef) type_args = None /\
      params_typed = apply_type_params type_args (fn_params fdef) /\
      build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
        arg_tys params_typed = Some σ_acc /\
      σ = finalize_subst σ_acc /\
      params_subst = apply_lt_params σ params_typed /\
      check_args_assoc env Ω arg_tys params_subst = None /\
      T = apply_lt_ty σ (subst_type_params_ty type_args (fn_ret fdef)).
Proof.
  intros env Ω n fdef type_args arg_tys T Hinfer.
  unfold infer_direct_call_generic_assoc in Hinfer.
  destruct (no_captures_b fdef &&
    Nat.eqb (Datatypes.length type_args) (fn_type_params fdef))
    eqn:Hgate; try discriminate.
  destruct (check_struct_bounds env (fn_bounds fdef) type_args)
    as [err_bounds|] eqn:Hbounds; try discriminate.
  destruct (build_sigma (fn_lifetimes fdef)
    (repeat None (fn_lifetimes fdef)) arg_tys
    (apply_type_params type_args (fn_params fdef)))
    as [sigma_acc|] eqn:Hsigma; try discriminate.
  destruct (check_args_assoc env Ω arg_tys
    (apply_lt_params (finalize_subst sigma_acc)
      (apply_type_params type_args (fn_params fdef))))
    as [err|] eqn:Hcheck; try discriminate.
  destruct (forallb (wf_lifetime_b (mk_region_ctx n))
    (finalize_subst sigma_acc)) eqn:?; try discriminate.
  destruct (outlives_constraints_hold_b Ω
    (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)))
    eqn:?; try discriminate.
  inversion Hinfer; subst.
  exists (apply_type_params type_args (fn_params fdef)),
    sigma_acc, (finalize_subst sigma_acc),
    (apply_lt_params (finalize_subst sigma_acc)
      (apply_type_params type_args (fn_params fdef))).
  repeat split; try reflexivity; assumption.
Qed.

Lemma infer_env_args_collect_direct_call_assoc_checked_sound :
  forall fuel env Ω n fdef args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists params,
      typed_args_env_structural_assoc env Ω n Σ args params Σ'.
Proof.
  intros fuel env Ω n fdef args arg_tys T Σ Σ' Hcollect Hexpr Hcall.
  destruct (infer_direct_call_assoc_checked_args env Ω n fdef arg_tys T Hcall)
    as [sigma_acc [sigma [params [Hgate [Hsigma [Hs [Hparams [Hcheck Hret]]]]]]]].
  exists params.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_direct_call_generic_assoc_checked_sound :
  forall fuel env Ω n fdef type_args args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys =
      infer_ok T ->
    exists params,
      typed_args_env_structural_assoc env Ω n Σ args params Σ'.
Proof.
  intros fuel env Ω n fdef type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_direct_call_generic_assoc_checked_args
    env Ω n fdef type_args arg_tys T Hcall) as
    [params_typed [sigma_acc [sigma [params
      [Hgate [Hbounds [Htyped [Hsigma [Hs [Hparams [Hcheck Hret]]]]]]]]]]].
  exists params.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_direct_call_assoc_checked_sound :
  forall fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists params,
      typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_direct_call_assoc_checked_args env Ω n fdef arg_tys T Hcall)
    as [sigma_acc [sigma [params [Hgate [Hsigma [Hs [Hparams [Hcheck Hret]]]]]]]].
  exists params.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_direct_call_generic_assoc_checked_sound :
  forall fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys =
      infer_ok T ->
    exists params,
      typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_direct_call_generic_assoc_checked_args
    env Ω n fdef type_args arg_tys T Hcall) as
    [params_typed [sigma_acc [sigma [params
      [Hgate [Hbounds [Htyped [Hsigma [Hs [Hparams [Hcheck Hret]]]]]]]]]]].
  exists params.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_direct_call_assoc_sound :
  forall fuel env Ω n fdef args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists params,
      typed_args_env_structural_assoc env Ω n Σ args params Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args params /\
      Datatypes.length args = Datatypes.length params.
Proof.
  intros fuel env Ω n fdef args arg_tys T Σ Σ' Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_direct_call_assoc_checked_sound
    fuel env Ω n fdef args arg_tys T Σ Σ' Hcollect Hexpr Hcall)
    as [params Hargs].
  exists params. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound env Ω n Σ args params Σ' Hargs).
Qed.

Lemma infer_env_args_collect_direct_call_generic_assoc_sound :
  forall fuel env Ω n fdef type_args args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys =
      infer_ok T ->
    exists params,
      typed_args_env_structural_assoc env Ω n Σ args params Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args params /\
      Datatypes.length args = Datatypes.length params.
Proof.
  intros fuel env Ω n fdef type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_direct_call_generic_assoc_checked_sound
    fuel env Ω n fdef type_args args arg_tys T Σ Σ' Hcollect Hexpr Hcall)
    as [params Hargs].
  exists params. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound env Ω n Σ args params Σ' Hargs).
Qed.

Lemma infer_env_args_collect_roots_direct_call_assoc_sound :
  forall fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists params,
      typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args params /\
      Datatypes.length args = Datatypes.length params.
Proof.
  intros fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_direct_call_assoc_checked_sound
    fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall) as [params Hargs].
  exists params. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound env Ω n R Σ args params Σ' R' arg_roots Hargs).
Qed.

Lemma infer_env_args_collect_roots_direct_call_generic_assoc_sound :
  forall fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys =
      infer_ok T ->
    exists params,
      typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args params /\
      Datatypes.length args = Datatypes.length params.
Proof.
  intros fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_direct_call_generic_assoc_checked_sound
    fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall) as [params Hargs].
  exists params. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound env Ω n R Σ args params Σ' R' arg_roots Hargs).
Qed.
