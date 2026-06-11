From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt CheckerEnvHelpers TypeChecker AssocCompatibility
  AssocArgBoolFacts AssocHrtHelpers AssocHrtFacts AssocEnvStructural
  EnvStructuralRules EnvTypingSoundness AssocEnvArgSoundness EnvRootSoundness
  AssocEnvRootArgSoundness AssocHigherBridgeSoundness.
From Stdlib Require Import List Bool ZArith.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware env/root HRT argument collector composition              *)
(* ------------------------------------------------------------------ *)

Lemma infer_env_args_collect_hrt_assoc_checked_sound :
  forall fuel env Ω n m bounds body args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_hrt_call_env_assoc env Ω n m bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ'.
Proof.
  intros fuel env Ω n m bounds body args arg_tys T Σ Σ'
    Hcollect Hexpr Hhrt.
  destruct (infer_hrt_call_env_assoc_checked_args
    env Ω n m bounds body arg_tys T Hhrt) as
    [[param_tys [ret [sigma [_ [_ [Hcheck _]]]]]] |
     [env_lt [param_tys [ret [sigma [_ [_ [Hcheck _]]]]]]]].
  - exists (map (open_bound_ty sigma) param_tys).
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - exists (map (open_bound_ty (complete_bound_sigma_with_vars n sigma)) param_tys).
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_type_forall_assoc_checked_sound :
  forall fuel env Ω n type_params bounds body args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_type_forall_call_env_assoc
      env Ω type_params bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ'.
Proof.
  intros fuel env Ω n type_params bounds body args arg_tys T Σ Σ'
    Hcollect Hexpr Hforall.
  destruct (infer_type_forall_call_env_assoc_checked_args
    env Ω type_params bounds body arg_tys T Hforall) as
    [type_args [param_tys [ret [_ [_ [_ [Hcheck _]]]]]]].
  exists (map (subst_type_params_ty type_args) param_tys).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_type_forall_elab_assoc_checked_sound :
  forall fuel env Ω n type_params bounds body args arg_tys type_args_ret Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_type_forall_call_env_elab_assoc
      env Ω type_params bounds body arg_tys = infer_ok type_args_ret ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ'.
Proof.
  intros fuel env Ω n type_params bounds body args arg_tys type_args_ret Σ Σ'
    Hcollect Hexpr Hforall.
  destruct (infer_type_forall_call_env_elab_assoc_checked_args
    env Ω type_params bounds body arg_tys type_args_ret Hforall) as
    [type_args [param_tys [ret [_ [_ [_ [Hcheck _]]]]]]].
  exists (map (subst_type_params_ty type_args) param_tys).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_mixed_forall_assoc_checked_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_mixed_forall_call_env_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ'.
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    args arg_tys T Σ Σ' Hcollect Hexpr Hforall.
  destruct (infer_mixed_forall_call_env_assoc_checked_args
    env Ω n m lt_bounds type_params type_bounds body arg_tys T Hforall) as
    [type_args [param_tys [ret [sigma [_ [_ [_ [Hcheck _]]]]]]]].
  exists (map (open_bound_ty (complete_bound_sigma_with_vars n sigma))
    (map (subst_type_params_ty type_args) param_tys)).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_mixed_forall_elab_assoc_checked_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      args arg_tys type_args_ret Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_mixed_forall_call_env_elab_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ'.
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    args arg_tys type_args_ret Σ Σ' Hcollect Hexpr Hforall.
  destruct (infer_mixed_forall_call_env_elab_assoc_checked_args
    env Ω n m lt_bounds type_params type_bounds body arg_tys type_args_ret
    Hforall) as
    [type_args [param_tys [ret [sigma [_ [_ [_ [Hcheck _]]]]]]]].
  exists (map (open_bound_ty (complete_bound_sigma_with_vars n sigma))
    (map (subst_type_params_ty type_args) param_tys)).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_hrt_assoc_checked_sound :
  forall fuel env Ω n m bounds body R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_hrt_call_env_assoc env Ω n m bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots.
Proof.
  intros fuel env Ω n m bounds body R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hhrt.
  destruct (infer_hrt_call_env_assoc_checked_args
    env Ω n m bounds body arg_tys T Hhrt) as
    [[param_tys [ret [sigma [_ [_ [Hcheck _]]]]]] |
     [env_lt [param_tys [ret [sigma [_ [_ [Hcheck _]]]]]]]].
  - exists (map (open_bound_ty sigma) param_tys).
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - exists (map (open_bound_ty (complete_bound_sigma_with_vars n sigma)) param_tys).
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_type_forall_assoc_checked_sound :
  forall fuel env Ω n type_params bounds body R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_type_forall_call_env_assoc
      env Ω type_params bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots.
Proof.
  intros fuel env Ω n type_params bounds body R Σ args arg_tys T
    Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_type_forall_call_env_assoc_checked_args
    env Ω type_params bounds body arg_tys T Hforall) as
    [type_args [param_tys [ret [_ [_ [_ [Hcheck _]]]]]]].
  exists (map (subst_type_params_ty type_args) param_tys).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_type_forall_elab_assoc_checked_sound :
  forall fuel env Ω n type_params bounds body R Σ args arg_tys type_args_ret
      Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_type_forall_call_env_elab_assoc
      env Ω type_params bounds body arg_tys = infer_ok type_args_ret ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots.
Proof.
  intros fuel env Ω n type_params bounds body R Σ args arg_tys type_args_ret
    Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_type_forall_call_env_elab_assoc_checked_args
    env Ω type_params bounds body arg_tys type_args_ret Hforall) as
    [type_args [param_tys [ret [_ [_ [_ [Hcheck _]]]]]]].
  exists (map (subst_type_params_ty type_args) param_tys).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_mixed_forall_assoc_checked_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_mixed_forall_call_env_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots.
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    R Σ args arg_tys T Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_mixed_forall_call_env_assoc_checked_args
    env Ω n m lt_bounds type_params type_bounds body arg_tys T Hforall) as
    [type_args [param_tys [ret [sigma [_ [_ [_ [Hcheck _]]]]]]]].
  exists (map (open_bound_ty (complete_bound_sigma_with_vars n sigma))
    (map (subst_type_params_ty type_args) param_tys)).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_mixed_forall_elab_assoc_checked_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      R Σ args arg_tys type_args_ret Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_mixed_forall_call_env_elab_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots.
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    R Σ args arg_tys type_args_ret Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_mixed_forall_call_env_elab_assoc_checked_args
    env Ω n m lt_bounds type_params type_bounds body arg_tys type_args_ret
    Hforall) as
    [type_args [param_tys [ret [sigma [_ [_ [_ [Hcheck _]]]]]]]].
  exists (map (open_bound_ty (complete_bound_sigma_with_vars n sigma))
    (map (subst_type_params_ty type_args) param_tys)).
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_hrt_assoc_sound :
  forall fuel env Ω n m bounds body args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_hrt_call_env_assoc env Ω n m bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n m bounds body args arg_tys T Σ Σ' Hcollect Hexpr Hhrt.
  destruct (infer_env_args_collect_hrt_assoc_checked_sound
    fuel env Ω n m bounds body args arg_tys T Σ Σ' Hcollect Hexpr Hhrt)
    as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound
    env Ω n Σ args (params_of_tys param_tys) Σ' Hargs).
Qed.

Lemma infer_env_args_collect_type_forall_assoc_sound :
  forall fuel env Ω n type_params bounds body args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_type_forall_call_env_assoc
      env Ω type_params bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n type_params bounds body args arg_tys T Σ Σ'
    Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_type_forall_assoc_checked_sound
    fuel env Ω n type_params bounds body args arg_tys T Σ Σ'
    Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound
    env Ω n Σ args (params_of_tys param_tys) Σ' Hargs).
Qed.

Lemma infer_env_args_collect_type_forall_elab_assoc_sound :
  forall fuel env Ω n type_params bounds body args arg_tys type_args_ret Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_type_forall_call_env_elab_assoc
      env Ω type_params bounds body arg_tys = infer_ok type_args_ret ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n type_params bounds body args arg_tys type_args_ret Σ Σ'
    Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_type_forall_elab_assoc_checked_sound
    fuel env Ω n type_params bounds body args arg_tys type_args_ret Σ Σ'
    Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound
    env Ω n Σ args (params_of_tys param_tys) Σ' Hargs).
Qed.

Lemma infer_env_args_collect_mixed_forall_assoc_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_mixed_forall_call_env_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    args arg_tys T Σ Σ' Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_mixed_forall_assoc_checked_sound
    fuel env Ω n m lt_bounds type_params type_bounds body args arg_tys T Σ Σ'
    Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound
    env Ω n Σ args (params_of_tys param_tys) Σ' Hargs).
Qed.

Lemma infer_env_args_collect_mixed_forall_elab_assoc_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      args arg_tys type_args_ret Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_mixed_forall_call_env_elab_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    args arg_tys type_args_ret Σ Σ' Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_mixed_forall_elab_assoc_checked_sound
    fuel env Ω n m lt_bounds type_params type_bounds body args arg_tys
    type_args_ret Σ Σ' Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound
    env Ω n Σ args (params_of_tys param_tys) Σ' Hargs).
Qed.

Lemma infer_env_args_collect_roots_hrt_assoc_sound :
  forall fuel env Ω n m bounds body R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_hrt_call_env_assoc env Ω n m bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n m bounds body R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hhrt.
  destruct (infer_env_args_collect_roots_hrt_assoc_checked_sound
    fuel env Ω n m bounds body R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hhrt) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound
    env Ω n R Σ args (params_of_tys param_tys) Σ' R' arg_roots Hargs).
Qed.

Lemma infer_env_args_collect_roots_type_forall_assoc_sound :
  forall fuel env Ω n type_params bounds body R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_type_forall_call_env_assoc
      env Ω type_params bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n type_params bounds body R Σ args arg_tys T
    Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_roots_type_forall_assoc_checked_sound
    fuel env Ω n type_params bounds body R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound
    env Ω n R Σ args (params_of_tys param_tys) Σ' R' arg_roots Hargs).
Qed.

Lemma infer_env_args_collect_roots_type_forall_elab_assoc_sound :
  forall fuel env Ω n type_params bounds body R Σ args arg_tys type_args_ret
      Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_type_forall_call_env_elab_assoc
      env Ω type_params bounds body arg_tys = infer_ok type_args_ret ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n type_params bounds body R Σ args arg_tys type_args_ret
    Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_roots_type_forall_elab_assoc_checked_sound
    fuel env Ω n type_params bounds body R Σ args arg_tys type_args_ret
    Σ' R' arg_roots Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound
    env Ω n R Σ args (params_of_tys param_tys) Σ' R' arg_roots Hargs).
Qed.

Lemma infer_env_args_collect_roots_mixed_forall_assoc_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_mixed_forall_call_env_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    R Σ args arg_tys T Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_roots_mixed_forall_assoc_checked_sound
    fuel env Ω n m lt_bounds type_params type_bounds body R Σ args arg_tys T
    Σ' R' arg_roots Hcollect Hexpr Hforall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound
    env Ω n R Σ args (params_of_tys param_tys) Σ' R' arg_roots Hargs).
Qed.

Lemma infer_env_args_collect_roots_mixed_forall_elab_assoc_sound :
  forall fuel env Ω n m lt_bounds type_params type_bounds body
      R Σ args arg_tys type_args_ret Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_mixed_forall_call_env_elab_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys param_tys) /\
      Datatypes.length args = Datatypes.length (params_of_tys param_tys).
Proof.
  intros fuel env Ω n m lt_bounds type_params type_bounds body
    R Σ args arg_tys type_args_ret Σ' R' arg_roots Hcollect Hexpr Hforall.
  destruct (infer_env_args_collect_roots_mixed_forall_elab_assoc_checked_sound
    fuel env Ω n m lt_bounds type_params type_bounds body R Σ args arg_tys
    type_args_ret Σ' R' arg_roots Hcollect Hexpr Hforall)
    as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound
    env Ω n R Σ args (params_of_tys param_tys) Σ' R' arg_roots Hargs).
Qed.
