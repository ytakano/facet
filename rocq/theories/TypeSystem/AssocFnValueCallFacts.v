From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt TypeChecker AssocCompatibility
  AssocArgBoolFacts AssocHrtFacts AssocEnvStructural
  AssocEnvArgSoundness AssocEnvRootArgSoundness
  AssocFnValueCallHelpers EnvStructuralRules EnvTypingSoundness EnvRootSoundness
  AssocHigherBridgeSoundness.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware plain function-value call facts                          *)
(* ------------------------------------------------------------------ *)

Lemma infer_fn_value_call_assoc_checked_args :
  forall env Ω callee_ty arg_tys T,
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
    (exists param_tys ret,
        ty_core callee_ty = TFn param_tys ret /\
        check_arg_tys_assoc env Ω arg_tys param_tys = None /\
        assoc_checked_arg_tys env Ω arg_tys param_tys /\
        T = ret) \/
    (exists env_lt param_tys ret,
        ty_core callee_ty = TClosure env_lt param_tys ret /\
        check_arg_tys_assoc env Ω arg_tys param_tys = None /\
        assoc_checked_arg_tys env Ω arg_tys param_tys /\
        T = ret).
Proof.
  intros env Ω callee_ty arg_tys T Hinfer.
  unfold infer_fn_value_call_assoc in Hinfer.
  destruct (ty_core callee_ty) eqn:Hcore; try discriminate.
  - destruct (check_arg_tys_assoc env Ω arg_tys l) as [err|] eqn:Hcheck;
      try discriminate.
    inversion Hinfer; subst.
    left. eexists; eexists.
    split; [reflexivity |].
    split; [exact Hcheck |].
    split; [apply check_arg_tys_assoc_checked_arg_tys; exact Hcheck |].
    reflexivity.
  - destruct (check_arg_tys_assoc env Ω arg_tys l0) as [err|] eqn:Hcheck;
      try discriminate.
    inversion Hinfer; subst.
    right. eexists; eexists; eexists.
    split; [reflexivity |].
    split; [exact Hcheck |].
    split; [apply check_arg_tys_assoc_checked_arg_tys; exact Hcheck |].
    reflexivity.
Qed.

Lemma infer_env_args_collect_fn_value_call_assoc_checked_sound :
  forall fuel env Ω n callee_ty args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys param_tys) Σ'.
Proof.
  intros fuel env Ω n callee_ty args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_assoc_checked_args
    env Ω callee_ty arg_tys T Hcall) as
    [[param_tys [ret [_ [Hcheck [_ _]]]]] |
     [env_lt [param_tys [ret [_ [Hcheck [_ _]]]]]]].
  - exists param_tys.
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - exists param_tys.
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_fn_value_call_assoc_checked_sound :
  forall fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys param_tys) Σ' R' arg_roots.
Proof.
  intros fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_assoc_checked_args
    env Ω callee_ty arg_tys T Hcall) as
    [[param_tys [ret [_ [Hcheck [_ _]]]]] |
     [env_lt [param_tys [ret [_ [Hcheck [_ _]]]]]]].
  - exists param_tys.
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - exists param_tys.
    rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_fn_value_call_assoc_sound :
  forall fuel env Ω n callee_ty args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
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
  intros fuel env Ω n callee_ty args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_fn_value_call_assoc_checked_sound
    fuel env Ω n callee_ty args arg_tys T Σ Σ' Hcollect Hexpr Hcall)
    as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound
    env Ω n Σ args (params_of_tys param_tys) Σ' Hargs).
Qed.

Lemma infer_env_args_collect_roots_fn_value_call_assoc_sound :
  forall fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
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
  intros fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_fn_value_call_assoc_checked_sound
    fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound
    env Ω n R Σ args (params_of_tys param_tys) Σ' R' arg_roots Hargs).
Qed.

Lemma infer_fn_value_call_assoc_args_sound :
  forall env Ω callee_ty arg_tys T,
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
    (exists param_tys ret,
        ty_core callee_ty = TFn param_tys ret /\
        check_arg_tys_assoc env Ω arg_tys param_tys = None /\
        Forall2
          (fun actual expected =>
             ty_compatible_assoc env Ω actual expected)
          arg_tys param_tys /\
        T = ret) \/
    (exists env_lt param_tys ret,
        ty_core callee_ty = TClosure env_lt param_tys ret /\
        check_arg_tys_assoc env Ω arg_tys param_tys = None /\
        Forall2
          (fun actual expected =>
             ty_compatible_assoc env Ω actual expected)
          arg_tys param_tys /\
        T = ret).
Proof.
  intros env Ω callee_ty arg_tys T Hcall.
  destruct (infer_fn_value_call_assoc_checked_args env Ω callee_ty arg_tys T Hcall)
    as [[param_tys [ret [Hcore [Hcheck [_ Hret]]]]] |
        [env_lt [param_tys [ret [Hcore [Hcheck [_ Hret]]]]]]].
  - left. exists param_tys, ret. repeat split; try assumption.
    exact (check_arg_tys_assoc_sound env Ω arg_tys param_tys Hcheck).
  - right. exists env_lt, param_tys, ret. repeat split; try assumption.
    exact (check_arg_tys_assoc_sound env Ω arg_tys param_tys Hcheck).
Qed.

(* ------------------------------------------------------------------ *)
(* Assoc-aware explicit generic function-value call facts               *)
(* ------------------------------------------------------------------ *)

Lemma infer_fn_value_call_generic_assoc_checked_args :
  forall env Ω callee_ty type_args arg_tys T,
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists type_params bounds body param_tys ret,
      ty_core callee_ty = TTypeForall type_params bounds body /\
      ty_core body = TFn param_tys ret /\
      check_type_forall_bounds env bounds type_args = None /\
      check_arg_tys_assoc env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys) = None /\
      assoc_checked_arg_tys env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys) /\
      T = subst_type_params_ty type_args ret.
Proof.
  intros env Ω callee_ty type_args arg_tys T Hinfer.
  unfold infer_fn_value_call_generic_assoc in Hinfer.
  destruct (ty_core callee_ty) eqn:Hcore; try discriminate.
  destruct (ty_core t) eqn:Hbody; try discriminate.
  destruct (check_type_forall_bounds env l type_args) as [err_bounds|]
    eqn:Hbounds; try discriminate.
  destruct (check_arg_tys_assoc env Ω arg_tys
    (map (subst_type_params_ty type_args) l0)) as [err|] eqn:Hcheck;
    try discriminate.
  inversion Hinfer; subst.
  exists n, l, t, l0, t0.
  split; [reflexivity |].
  split; [exact Hbody |].
  split; [exact Hbounds |].
  split; [exact Hcheck |].
  split.
  - apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
  - reflexivity.
Qed.

Lemma infer_env_args_collect_fn_value_call_generic_assoc_checked_sound :
  forall fuel env Ω n callee_ty type_args args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ'.
Proof.
  intros fuel env Ω n callee_ty type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_generic_assoc_checked_args
    env Ω callee_ty type_args arg_tys T Hcall) as
    [type_params [bounds [body [param_tys [ret
      [_ [_ [_ [Hcheck [_ _]]]]]]]]]].
  exists param_tys.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_roots_fn_value_call_generic_assoc_checked_sound :
  forall fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R'
      arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Σ' R' arg_roots.
Proof.
  intros fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R'
    arg_roots Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_generic_assoc_checked_args
    env Ω callee_ty type_args arg_tys T Hcall) as
    [type_params [bounds [body [param_tys [ret
      [_ [_ [_ [Hcheck [_ _]]]]]]]]]].
  exists param_tys.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_args_collect_fn_value_call_generic_assoc_sound :
  forall fuel env Ω n callee_ty type_args args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists param_tys,
      typed_args_env_structural_assoc env Ω n Σ args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ' /\
      Forall2
        (fun e p =>
           exists actual Σin Σout,
             typed_env_structural env Ω n Σin e actual Σout /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys
          (map (subst_type_params_ty type_args) param_tys)) /\
      Datatypes.length args = Datatypes.length
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)).
Proof.
  intros fuel env Ω n callee_ty type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_fn_value_call_generic_assoc_checked_sound
    fuel env Ω n callee_ty type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_env_structural_assoc_sound env Ω n Σ args
    (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ'
    Hargs).
Qed.

Lemma infer_env_args_collect_roots_fn_value_call_generic_assoc_sound :
  forall fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R'
      arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists param_tys,
      typed_args_roots_assoc env Ω n R Σ args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Σ' R' arg_roots /\
      Forall2
        (fun e p =>
           exists actual Rin Rnext Σin Σout roots,
             typed_env_roots env Ω n Rin Σin e actual Σout Rnext roots /\
             ty_compatible_assoc env Ω actual (param_ty p))
        args (params_of_tys
          (map (subst_type_params_ty type_args) param_tys)) /\
      Datatypes.length args = Datatypes.length
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)).
Proof.
  intros fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R'
    arg_roots Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_fn_value_call_generic_assoc_checked_sound
    fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall) as [param_tys Hargs].
  exists param_tys. split; [exact Hargs |].
  exact (typed_args_roots_assoc_sound env Ω n R Σ args
    (params_of_tys (map (subst_type_params_ty type_args) param_tys))
    Σ' R' arg_roots Hargs).
Qed.

Lemma infer_fn_value_call_generic_assoc_args_sound :
  forall env Ω callee_ty type_args arg_tys T,
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists type_params bounds body param_tys ret,
      ty_core callee_ty = TTypeForall type_params bounds body /\
      ty_core body = TFn param_tys ret /\
      check_type_forall_bounds env bounds type_args = None /\
      check_arg_tys_assoc env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys) = None /\
      Forall2
        (fun actual expected => ty_compatible_assoc env Ω actual expected)
        arg_tys (map (subst_type_params_ty type_args) param_tys) /\
      T = subst_type_params_ty type_args ret.
Proof.
  intros env Ω callee_ty type_args arg_tys T Hcall.
  destruct (infer_fn_value_call_generic_assoc_checked_args
    env Ω callee_ty type_args arg_tys T Hcall) as
    [type_params [bounds [body [param_tys [ret
      [Hcore [Hbody [Hbounds [Hcheck [_ Hret]]]]]]]]]].
  exists type_params, bounds, body, param_tys, ret.
  repeat split; try assumption.
  exact (check_arg_tys_assoc_sound env Ω arg_tys
    (map (subst_type_params_ty type_args) param_tys) Hcheck).
Qed.
