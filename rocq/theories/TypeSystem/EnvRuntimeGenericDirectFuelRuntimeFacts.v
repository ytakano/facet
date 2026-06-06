From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectHiddenFrameFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef fuel,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef fuel Hsafe_args Hsummary Hstore Hroots Hshadow
    Hrn Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  revert env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  induction fuel as [| fuel' IH]; intros env Omega n R Sigma fname type_args
    args sigma Sigma_args R_args arg_roots s s' ret fdef Hsafe_args Hsummary
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store Heval_call Hunique
    Hin_fdef Hname_fdef Hcaps_fdef Htyped_args Houtlives.
  - eapply eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr;
      try eassumption.
    eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero.
    exact Hsummary.
  - destruct (callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases
      env (S fuel') fdef type_args Hsummary) as [Hexpr | Hgeneric].
    + destruct Hexpr as (T_expr & Gamma_expr & R_expr & roots_expr &
        ret_roots_expr & Hnodup_expr & Hexpr_summary & Hcompat_expr &
        Hexcl_roots_expr & Hexcl_env_expr).
      eapply eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr;
        try eassumption.
      unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated.
      repeat eexists; repeat split; eassumption.
    + destruct Hgeneric as (fuel_nested & fname_nested & nested_type_args &
        args_static & raw_body & synthetic_body & fcallee_static & T_body &
        Gamma_out & R_body & roots_body & Hfuel_eq & Hbody & Htarget &
        Hsynthetic & Hsafe_static & Hin_static & Hname_static & Harity_static &
        Hbounds_static & Hsummary_nested & Hnodup_applied & Htyped_synthetic &
        Hcompat_body & Hexcl_roots & Hexcl_env).
      inversion Hfuel_eq; subst fuel_nested; clear Hfuel_eq.
      dependent destruction Heval_call.
      match goal with
      | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
          assert (f_runtime = fdef) as -> by
            (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
      end.
      match goal with
      | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
          rename H into Heval_args;
          rename s_args0 into s_args;
          rename vs0 into vs
      end.
      match goal with
      | H : alpha_rename_fn_def (store_names s_args) fdef =
            (?fcall0, ?used0) |- _ =>
          rename H into Hrename;
          rename fcall0 into fcall;
          rename used0 into used'
      end.
      match goal with
      | H : eval _
            (bind_params (apply_type_params type_args (fn_params fcall)) vs s_args)
            (subst_type_params_expr type_args (fn_body fcall)) ?s_body0 ret |- _ =>
          rename H into Heval_body;
          rename s_body0 into s_body
      end.
      pose proof (store_safe_function_value_call_args_preservation_ready
        env args Hsafe_args) as Hready_args.
      pose proof (preservation_ready_args_implies_provenance_ready_closure
        args Hready_args) as Hprov_args.
      destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
        env Omega n R Sigma args
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fdef)))
        Sigma_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
        Heval_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store)
        as (Hstore_args & Hargs_values_sigma & Hpres_args & Hroots_args &
            Harg_roots_values & Hshadow_args & Hrn_args & Hnamed_args &
            Hkeys_args & Hsummary_args).
      pose (ps_runtime := apply_type_params type_args (fn_params fcall)).
      destruct (generic_direct_call_args_bind_type_params_runtime_package
        env Omega n R Sigma args type_args sigma fdef fcall used'
        s s_args vs Sigma_args R_args arg_roots Hsafe_args Heval_args
        Htyped_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hunique
        Hsummary_store Hrename)
        as (Hstore_bind & Hroots_bind & Hshadow_bind & Hrn_bind & Hcover_bind &
            Hnamed_bind & Hkeys_bind & Hsummary_bind & Hframe_start).
      fold ps_runtime in Hstore_bind, Hroots_bind, Hshadow_bind, Hrn_bind,
        Hcover_bind, Hnamed_bind, Hkeys_bind, Hsummary_bind, Hframe_start.
      pose (body_env := global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef))).
      assert (Hstore_bind_body_env :
        store_typed_prefix body_env (bind_params ps_runtime vs s_args)
          (sctx_of_ctx (params_ctx ps_runtime))).
      { subst body_env.
        eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
        exact Hstore_bind. }
      assert (Heval_body_body_env :
        eval body_env (bind_params ps_runtime vs s_args)
          (subst_type_params_expr type_args (fn_body fcall)) s_body ret).
      { subst body_env ps_runtime.
        eapply direct_call_eval_global_env_with_local_bounds.
        exact Heval_body. }
      assert (Hsummary_bind_body_env :
        store_function_closure_targets_summary body_env
          (bind_params ps_runtime vs s_args)).
      { subst body_env.
        apply store_function_closure_targets_summary_global_env_with_local_bounds.
        exact Hsummary_bind. }
      assert (Hstore_bind_body_env_ctx :
        store_typed_prefix body_env (bind_params ps_runtime vs s_args)
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))).
      { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - rewrite <- params_ctx_apply_type_params.
          exact Hstore_bind_body_env.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hunique_body_env : fn_env_unique_by_name body_env).
      { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
      destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args_call_frame
        env Omega n R Sigma Sigma_args R_args arg_roots args type_args
        sigma fdef fcall used' fname_nested nested_type_args args_static
        raw_body synthetic_body T_body Gamma_out R_body roots_body s s_args vs
        Hbody Htarget Hsynthetic Hsafe_static Hcaps_fdef Hrename
        Hnodup_applied Htyped_synthetic Hexcl_roots Htyped_args Hsafe_args Heval_args
        Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys)
        as (argsr & fcallee_runtime & sigma_nested & nested_arg_roots &
            Sigma_nested & R_nested & Hbody_runtime & Hsafe_runtime &
            Htyped_nested & Hin_nested & Hname_nested_runtime & Hcaps_nested &
            Houtlives_nested & Hret_nested & Hexcl_nested_roots &
            Hnested_roots_subset).
      assert (Heval_nested : eval body_env
        (bind_params ps_runtime vs s_args)
        (ECallGeneric fname_nested nested_type_args argsr) s_body ret).
      { subst body_env ps_runtime.
        rewrite <- Hbody_runtime.
        exact Heval_body_body_env. }
      assert (Hsummary_nested_body_env :
        callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
          body_env fuel' fcallee_runtime nested_type_args).
      { subst body_env.
        assert (fcallee_runtime = fcallee_static) as ->.
        { eapply Hunique.
          - exact Hin_nested.
          - exact Hin_static.
          - rewrite Hname_nested_runtime. exact (eq_sym Hname_static). }
        eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
        - exact Hunique.
        - exact Hsummary_nested. }
      assert (Hsafe_runtime_body :
        store_safe_function_value_call_args body_env argsr).
      { subst body_env.
        eapply store_safe_function_value_call_args_global_env_with_local_bounds.
        exact Hsafe_runtime. }
      destruct (IH body_env (fn_outlives fdef) (fn_lifetimes fdef)
        (call_param_root_env ps_runtime arg_roots R_args)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        fname_nested nested_type_args argsr sigma_nested Sigma_nested R_nested
        nested_arg_roots (bind_params ps_runtime vs s_args) s_body ret
        fcallee_runtime Hsafe_runtime_body Hsummary_nested_body_env
        Hstore_bind_body_env_ctx Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
        Hkeys_bind Hsummary_bind_body_env Heval_nested Hunique_body_env
        Hin_nested Hname_nested_runtime Hcaps_nested Htyped_nested
        Houtlives_nested)
        as [Hpkg_nested [s_nested_args [vs_nested [Heval_nested_args Hbody_eq]]]].
      assert (Hargs_values_fdef_type :
        eval_args_values_have_types env Omega s_args vs
          (apply_type_params type_args (fn_params fdef))).
      { eapply eval_args_values_have_types_apply_lt_params_inv.
        exact Hargs_values_sigma. }
      pose proof (alpha_rename_fn_def_shape (store_names s_args)
                    fdef fcall used' Hrename) as Hshape.
      destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
      assert (Hargs_values_fcall_type :
        eval_args_values_have_types env Omega s_args vs ps_runtime).
      { subst ps_runtime.
        eapply eval_args_values_have_types_params_alpha.
        - apply params_alpha_apply_type_compat. exact Hparams_alpha.
        - exact Hargs_values_fdef_type. }
      assert (Hfresh : params_fresh_in_store ps_runtime s_args).
      { subst ps_runtime.
        unfold params_fresh_in_store.
        rewrite params_ctx_apply_type_params.
        rewrite ctx_names_subst_type_params_ctx.
        eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
      assert (Hframe_scope_start :
        store_frame_scope ps_runtime (sctx_of_ctx (params_ctx ps_runtime))
          (bind_params ps_runtime vs s_args) s_args).
      { eapply store_frame_scope_bind_params. exact Hargs_values_fcall_type. }
      assert (Hframe_fresh_start :
        store_frame_static_fresh (sctx_of_ctx (params_ctx ps_runtime)) s_args).
      { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
      assert (Hframe_scope_start_ctx :
        store_frame_scope ps_runtime
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
          (bind_params ps_runtime vs s_args) s_args).
      { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - rewrite <- params_ctx_apply_type_params.
          exact Hframe_scope_start.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hframe_fresh_start_ctx :
        store_frame_static_fresh
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
          s_args).
      { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - rewrite <- params_ctx_apply_type_params.
          exact Hframe_fresh_start.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hprov_runtime_body : provenance_ready_args argsr).
      { apply preservation_ready_args_implies_provenance_ready_closure.
        eapply store_safe_function_value_call_args_preservation_ready.
        exact Hsafe_runtime_body. }
      destruct (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
        body_env (bind_params ps_runtime vs s_args) argsr s_nested_args
        vs_nested Heval_nested_args (fn_outlives fdef) (fn_lifetimes fdef)
        (call_param_root_env ps_runtime arg_roots R_args)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        (apply_lt_params sigma_nested
          (apply_type_params nested_type_args (fn_params fcallee_runtime)))
        Sigma_nested R_nested nested_arg_roots ps_runtime s_args
        Hprov_runtime_body
        Htyped_nested Hcover_bind Hroots_bind Hshadow_bind Hrn_bind
        Hframe_scope_start_ctx Hframe_fresh_start_ctx)
        as [_ [_ [_ [_ [Hframe_scope_nested Hframe_fresh_nested]]]]].
      assert (Hsame_nested :
        sctx_same_bindings (sctx_of_ctx (params_ctx ps_runtime)) Sigma_nested).
      { subst ps_runtime.
        rewrite params_ctx_apply_type_params.
        rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - eapply typed_args_env_structural_same_bindings.
          eapply typed_args_roots_structural. exact Htyped_nested.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hscope_nested : store_param_scope ps_runtime s_nested_args s_args).
      { eapply store_frame_scope_param_scope. exact Hframe_scope_nested. }
      assert (Hremoved_exact : store_remove_params ps_runtime s_body = s_args).
      { rewrite Hbody_eq.
        eapply store_remove_params_store_frame_scope_exact.
        - exact Hsame_nested.
        - exact Hscope_nested.
        - exact Hframe_scope_nested. }
      fold ps_runtime.
      rewrite Hremoved_exact.
      split.
      * constructor.
        -- exact Hstore_args.
        -- rewrite <- Hremoved_exact.
           rewrite Hbody_eq.
           assert (Hv_nested_env :
             value_has_type env s_nested_args ret
               (apply_lt_ty sigma_nested
                 (subst_type_params_ty nested_type_args
                   (fn_ret fcallee_runtime)))).
           { rewrite <- Hbody_eq.
             subst body_env.
             eapply direct_call_value_has_type_clear_global_env_local_bounds.
             exact (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg_nested). }
           assert (Hv_body : value_has_type env s_nested_args ret T_body).
           { rewrite Hret_nested. exact Hv_nested_env. }
           assert (Hv_fdef_inst :
             value_has_type env s_nested_args ret
               (subst_type_params_ty type_args (fn_ret fdef))).
           { eapply value_has_type_compatible.
             - exact Hv_body.
             - apply ty_compatible_b_sound with (Ω := fn_outlives fdef).
               exact Hcompat_body. }
           assert (Hv_fcall_inst :
             value_has_type env s_nested_args ret
               (subst_type_params_ty type_args (fn_ret fcall))).
           { rewrite <- Hret_alpha. exact Hv_fdef_inst. }
           assert (Hret_exclude : value_refs_exclude_params ps_runtime ret).
           { eapply value_roots_exclude_params.
             - exact (generic_direct_call_package_value_roots
                 _ _ _ _ _ _ _ _ Hpkg_nested).
             - exact Hexcl_nested_roots. }
           apply value_has_type_apply_lt_ty.
           rewrite Hret_alpha.
           eapply value_has_type_store_remove_params_excluding.
           ++ exact Hv_fcall_inst.
           ++ exact Hret_exclude.
        -- exact Hpres_args.
        -- exact Hroots_args.
        -- eapply direct_call_value_roots_within_store_subset.
           ++ exact (generic_direct_call_package_value_roots _ _ _ _ _ _ _ _ Hpkg_nested).
           ++ exact Hnested_roots_subset.
        -- exact Hshadow_args.
        -- exact Hrn_args.
        -- exact Hnamed_args.
        -- exact Hkeys_args.
        -- exact Hsummary_args.
      * exists s_args, vs.
        split; [exact Heval_args | reflexivity].
Qed.


Lemma eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel_zero :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 0 fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps Htyped_args
    Houtlives.
  eapply eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr;
    try eassumption.
  eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero.
  exact Hsummary.
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef fuel,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef fuel Hsafe_args Hsummary Hstore Hroots Hshadow
    Hrn Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps Htyped_args
    Houtlives.
  destruct (eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel
    env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef fuel Hsafe_args Hsummary Hstore Hroots Hshadow
    Hrn Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps
    Htyped_args Houtlives) as [Hpkg _].
  exact (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg).
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel_zero :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 0 fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps Htyped_args
    Houtlives.
  eapply eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named;
    try eassumption.
  eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero.
  exact Hsummary.
Qed.

