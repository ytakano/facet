From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeValidatorFacts.
From Facet.TypeSystem Require Export EnvRuntimeInitialFacts.
From Facet.TypeSystem Require Export EnvRuntimeFunctionValueCallFacts.
From Facet.TypeSystem Require Export EnvRuntimeNarrowSummaryFacts.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectCallFacts.
From Facet.TypeSystem Require Export EnvRuntimeNarrowCheckerFacts.
From Facet.TypeSystem Require Export EnvRuntimeFunctionValueRuntimeFacts.
From Facet.TypeSystem Require Export EnvRuntimeLocalBoundsBridgeFacts.
From Facet.TypeSystem Require Export EnvRuntimeNarrowRuntimePackage.
From Facet.TypeSystem Require Export EnvRuntimeDirectCallStoreSafeFacts.
From Facet.TypeSystem Require Export EnvRuntimeCheckedPrefixRuntimePackage.
From Facet.TypeSystem Require Export EnvRuntimeFinalStoreScopeFacts.
From Facet.TypeSystem Require Export EnvRuntimeCapturedCallFacts.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectRuntimePackage.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectAlphaRuntimeFacts.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectHiddenFrameFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Inductive expr_root_shadow_store_safe_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSS_Exact : forall R Σ e T Σ' R' roots ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Omega n R Σ e T Σ' R' roots ret_roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots
  | ERSS_FunctionValueCall : forall R Σ x args T_callee Gamma_callee
      R_callee roots_callee T Σ' R' roots,
      preservation_ready_args args ->
      infer_core_env_roots_shadow_safe env Omega n R (ctx_of_sctx Σ)
        (EVar x) = infer_ok
          (T_callee, Gamma_callee, R_callee, roots_callee) ->
      supported_non_type_generic_function_value_call_callee_shape T_callee ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExpr (EVar x) args) T Σ' R' roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ECallExpr (EVar x) args) T Σ' R' roots roots
  | ERSS_Let : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSS_If : forall R R1 R2 R3 Σ Σ1 Sigma2 Sigma3 Sigma4
      e1 e2 e3 T_cond T2 T3 roots_cond roots2 roots3 ret_roots2 ret_roots3,
      provenance_ready_expr e1 ->
      typed_env_roots_shadow_safe env Omega n R Σ e1 T_cond Σ1 R1
        roots_cond ->
      ty_core T_cond = TBooleans ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e2 T2 Sigma2 R2 roots2 ret_roots2 ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 ret_roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Sigma2) (ctx_of_sctx Sigma3) = Some Sigma4 ->
      R2 = R3 ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        (sctx_of_ctx Sigma4) R2 (root_set_union roots2 roots3)
        (root_set_union ret_roots2 ret_roots3).

Lemma expr_root_shadow_store_safe_summary_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Omega n R Σ e T Σ' R' roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
    exact H.
  - exact H2.
  - eapply TERS_Let; eauto.
  - subst R3. eapply TERS_If; eauto. apply root_env_equiv_refl.
Qed.
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

Definition callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname type_args args raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
    fn_body fdef = raw_body /\
    generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, synthetic_body) /\
    synthetic_body = ECallGeneric fname type_args args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    Datatypes.length type_args = fn_type_params fcallee /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fcallee) type_args = None /\
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcallee)) /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fcallee type_args /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_generic_direct_let_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname type_args args T_hidden raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
    fn_body fdef = raw_body /\
    let_bound_generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, T_hidden, synthetic_body) /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    Datatypes.length type_args = fn_type_params fcallee /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fcallee) type_args = None /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fcallee type_args /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_hidden (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_generic_direct_if_literal_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists b fname_then type_args_then args_then fname_else type_args_else
      args_else raw_body synthetic_body fthen felse T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    if_literal_generic_direct_call_target_expr raw_body =
      Some (b, fname_then, type_args_then, args_then,
        fname_else, type_args_else, args_else, synthetic_body) /\
    store_safe_function_value_call_args env args_then /\
    store_safe_function_value_call_args env args_else /\
    In fthen (env_fns env) /\
    fn_name fthen = fname_then /\
    In felse (env_fns env) /\
    fn_name felse = fname_else /\
    Datatypes.length type_args_then = fn_type_params fthen /\
    Datatypes.length type_args_else = fn_type_params felse /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fthen) type_args_then = None /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds felse) type_args_else = None /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fthen type_args_then /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 felse type_args_else /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_local_fn_value_generic_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists x fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    local_fn_value_call_target_expr_with_binder raw_body =
      Some (x, fname, args, synthetic_body) /\
    store_safe_function_value_call_args env args /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args) /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma subst_type_params_trait_ref_nil : forall tr,
  subst_type_params_trait_ref [] tr = tr.
Proof.
  intros tr. destruct tr as [name args].
  unfold subst_type_params_trait_ref. simpl.
  rewrite map_subst_type_params_ty_nil. reflexivity.
Qed.

Lemma subst_type_params_trait_bound_nil : forall b,
  subst_type_params_trait_bound [] b = b.
Proof.
  intros b. destruct b as [idx traits].
  unfold subst_type_params_trait_bound. simpl.
  f_equal.
  induction traits as [| tr traits IH]; simpl; auto.
  rewrite subst_type_params_trait_ref_nil, IH. reflexivity.
Qed.

Lemma subst_type_params_trait_bounds_nil : forall bounds,
  subst_type_params_trait_bounds [] bounds = bounds.
Proof.
  induction bounds as [| b bounds IH]; simpl; auto.
  rewrite subst_type_params_trait_bound_nil, IH. reflexivity.
Qed.

Lemma callee_body_root_shadow_captured_call_generic_direct_instantiated_nil_fuel :
  forall env fdef,
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10001 fdef [].
Proof.
  intros env fdef Hsummary.
  destruct Hsummary as
    (fname & type_args & args & raw_body & synthetic_body & fcallee &
      T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
      Hsynthetic & Hsafe & Hin & Hname & Harity & Hbounds & Hcallee_ready &
      Hcallee_summary & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
  eapply CBRSSNI_GenericDirect with
    (raw_body := raw_body) (synthetic_body := synthetic_body)
    (fcallee := fcallee) (T_body := T_body) (Gamma_out := Gamma_out)
    (R_body := R_body) (roots_body := roots_body).
  - rewrite subst_type_params_expr_nil. symmetry. exact Hbody.
  - exact Htarget.
  - exact Hsynthetic.
  - exact Hsafe.
  - exact Hin.
  - exact Hname.
  - exact Harity.
  - rewrite subst_type_params_trait_bounds_nil. exact Hbounds.
  - exact Hcallee_summary.
  - rewrite apply_type_params_nil. exact Hnodup.
  - rewrite subst_type_params_trait_bounds_nil.
    rewrite subst_type_params_ctx_nil.
    exact Htyped.
  - rewrite subst_type_params_ty_nil. exact Hcompat.
  - rewrite apply_type_params_nil. exact Hexcl_roots.
  - rewrite apply_type_params_nil. exact Hexcl_env.
Qed.

Definition callee_body_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_captured_call_provenance_summary env fdef \/
  callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_let_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_if_literal_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_local_fn_value_generic_direct_narrow_store_safe_summary
    env fdef \/
  exists T_body Gamma_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_store_safe_narrow_summary_checked env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_generic_direct_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef.
Proof.
  intros env fdef Hgeneric.
  unfold check_fn_root_shadow_generic_direct_store_safe_summary in Hgeneric.
  destruct (generic_direct_call_target_expr (fn_body fdef))
    as [[[[fname type_args] args] synthetic_body] |] eqn:Htarget;
    try discriminate.
  apply andb_true_iff in Hgeneric as [Hsafe_args Hgeneric].
  destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
    try discriminate.
  apply andb_true_iff in Hgeneric as [Htype_params Hgeneric].
  apply Nat.eqb_eq in Htype_params.
  destruct (check_struct_bounds
    (global_env_with_local_bounds env (fn_bounds fdef))
    (fn_bounds fcallee) type_args)
    as [bounds_err |] eqn:Hbounds; try discriminate.
  remember (global_env_with_local_bounds env
    (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
    as callee_body_env.
  destruct (infer_core_env_roots_shadow_safe callee_body_env
    (fn_outlives fcallee) (fn_lifetimes fcallee)
    (initial_root_env_for_fn fcallee)
    (subst_type_params_ctx type_args (fn_body_ctx fcallee))
    (subst_type_params_expr type_args (fn_body fcallee)))
    as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
    eqn:Hcallee_core; try discriminate.
  destruct (infer_env_roots_shadow_safe env fcallee
    (initial_root_env_for_fn fcallee))
    as [[[[T_callee_env Gamma_callee_env] R_callee_env]
          roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
  destruct (infer_env_roots_shadow_safe env
    (fn_with_body fdef synthetic_body)
    (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hgeneric.
  destruct Hgeneric as
    [[[[[[[Hcallee_ready Hcallee_expr] Hcallee_compat] Hcallee_roots]
         Hcallee_env_excl] Hcompat] Hroots] Henv].
  apply lookup_fn_b_sound in Hlookup_b.
  destruct Hlookup_b as [Hin_callee Hname_callee].
  pose proof
    (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
      env fcallee type_args Hcallee_expr) as Hcallee_summary.
  pose proof (infer_env_roots_shadow_safe_sound env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
  unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
  destruct Htyped_fn as
    (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
  exists fname, type_args, args, (fn_body fdef), synthetic_body, fcallee,
    T_body_actual, Gamma_out_actual, R_body, roots_body.
  split; [reflexivity |].
  split; [exact Htarget |].
  split.
  { unfold generic_direct_call_target_expr in Htarget.
    destruct (fn_body fdef); try discriminate.
    inversion Htarget. reflexivity. }
  split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
  split; [exact Hin_callee |].
  split; [exact Hname_callee |].
  split; [exact Htype_params |].
  split; [exact Hbounds |].
  split.
  { apply preservation_ready_expr_b_sound. exact Hcallee_ready. }
  split; [exact Hcallee_summary |].
  split.
  { change (NoDup
      (ctx_names
        (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
    eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
  split; [exact Htyped_body |].
  split; [exact Hcompat_body |].
  split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
  apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_captured_call_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_store_safe_summary in Hcheck.
  apply orb_true_iff in Hcheck as [Hprefix_local | Hnarrow].
  - apply orb_true_iff in Hprefix_local as [Hprefix_if | Hlocal].
    { apply orb_true_iff in Hprefix_if as [Hprefix_let | Hif].
      - apply orb_true_iff in Hprefix_let as [Hprefix | Hlet].
        + apply orb_true_iff in Hprefix as [Hhead | Hgeneric].
      { apply orb_true_iff in Hhead as [Hold | Hdirect].
        * left. apply check_fn_root_shadow_captured_call_provenance_summary_sound.
        exact Hold.
        * right. left.
      destruct (direct_call_target_expr (fn_body fdef))
        as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
      apply andb_true_iff in Hdirect as [Hready_args Hdirect].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee))
        as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
        eqn:Hcallee_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fcallee
        (initial_root_env_for_fn fcallee))
        as [[[[T_callee_env Gamma_callee_env] R_callee_env]
              roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hdirect.
      destruct Hdirect as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      destruct (check_expr_root_shadow_store_safe_narrow_summary_sound
        env (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee) T_callee Gamma_callee R_callee roots_callee
        Hcallee_core Hcallee_expr) as [ret_roots_callee Hcallee_summary].
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split.
      { unfold direct_call_target_expr in Htarget.
        destruct (fn_body fdef); try discriminate.
        - inversion Htarget. reflexivity.
        - destruct e; try discriminate.
          inversion Htarget. reflexivity. }
      split; [apply store_safe_function_value_call_args_b_sound; exact Hready_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split.
      { exists T_callee, Gamma_callee, R_callee, roots_callee,
          ret_roots_callee.
        repeat split.
        - eapply infer_env_roots_shadow_safe_params_nodup.
          exact Hcallee_env.
        - exact Hcallee_summary.
        - exact Hcallee_compat.
        - apply fn_params_roots_exclude_b_sound. exact Hcallee_roots.
        - apply fn_params_root_env_excludes_b_sound. exact Hcallee_env_excl. }
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
      }
      { right. right. left.
        eapply check_fn_root_shadow_generic_direct_store_safe_summary_sound.
        exact Hgeneric.
      }
        + right. right. right. left.
      destruct (let_bound_generic_direct_call_target_expr (fn_body fdef))
        as [[[[[fname type_args] args] T_hidden] synthetic_body] |]
        eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hlet as [Hsafe_args Hlet].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      apply andb_true_iff in Hlet as [Htype_params Hlet].
      apply Nat.eqb_eq in Htype_params.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fcallee) type_args)
        as [bounds_err |] eqn:Hbounds; try discriminate.
      remember (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
        as callee_body_env.
      destruct (infer_core_env_roots_shadow_safe callee_body_env
        (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee)
        (subst_type_params_ctx type_args (fn_body_ctx fcallee))
        (subst_type_params_expr type_args (fn_body fcallee)))
        as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
        eqn:Hcallee_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fcallee
        (initial_root_env_for_fn fcallee))
        as [[[[T_callee_env Gamma_callee_env] R_callee_env]
              roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hlet.
      destruct Hlet as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env fcallee type_args Hcallee_expr) as Hcallee_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, type_args, args, T_hidden, (fn_body fdef), synthetic_body,
        fcallee, T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split; [exact Htype_params |].
      split; [exact Hbounds |].
      split; [exact Hcallee_summary |].
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
      - right. right. right. right. left.
      destruct (if_literal_generic_direct_call_target_expr (fn_body fdef))
        as [[[[[[[[b fname_then] type_args_then] args_then] fname_else]
                type_args_else] args_else] synthetic_body] |] eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hif as [Hsafes Hif].
      apply andb_true_iff in Hsafes as [Hsafe_then Hsafe_else].
      destruct (lookup_fn_b fname_then (env_fns env)) as [fthen |]
        eqn:Hlookup_then; try discriminate.
      destruct (lookup_fn_b fname_else (env_fns env)) as [felse |]
        eqn:Hlookup_else; try discriminate.
      apply andb_true_iff in Hif as [Htype_params_pair Hif].
      apply andb_true_iff in Htype_params_pair as
        [Htype_params_then Htype_params_else].
      apply Nat.eqb_eq in Htype_params_then.
      apply Nat.eqb_eq in Htype_params_else.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fthen) type_args_then) as [bounds_then |]
        eqn:Hbounds_then; try discriminate.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds felse) type_args_else) as [bounds_else |]
        eqn:Hbounds_else; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fthen) (fn_lifetimes fthen)
        (initial_root_env_for_fn fthen)
        (subst_type_params_ctx type_args_then (fn_body_ctx fthen))
        (subst_type_params_expr type_args_then (fn_body fthen)))
        as [[[[T_then Gamma_then] R_then] roots_then] | err]
        eqn:Hthen_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fthen
        (initial_root_env_for_fn fthen))
        as [[[[T_then_env Gamma_then_env] R_then_env]
              roots_then_env] | err] eqn:Hthen_env; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives felse) (fn_lifetimes felse)
        (initial_root_env_for_fn felse)
        (subst_type_params_ctx type_args_else (fn_body_ctx felse))
        (subst_type_params_expr type_args_else (fn_body felse)))
        as [[[[T_else Gamma_else] R_else] roots_else] | err]
        eqn:Helse_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env felse
        (initial_root_env_for_fn felse))
        as [[[[T_else_env Gamma_else_env] R_else_env]
              roots_else_env] | err] eqn:Helse_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hif.
      destruct Hif as
        [[[[[[[[[[Hthen_expr Hthen_compat] Hthen_roots]
                Hthen_env_excl] Helse_expr] Helse_compat] Helse_roots]
            Helse_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_then.
      destruct Hlookup_then as [Hin_then Hname_then].
      apply lookup_fn_b_sound in Hlookup_else.
      destruct Hlookup_else as [Hin_else Hname_else].
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env fthen type_args_then Hthen_expr) as Hthen_summary.
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env felse type_args_else Helse_expr) as Helse_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists b, fname_then, type_args_then, args_then, fname_else,
        type_args_else, args_else, (fn_body fdef), synthetic_body, fthen,
        felse, T_body_actual, Gamma_out_actual, R_body, roots_body.
      repeat split; try reflexivity; try eassumption;
        try (apply store_safe_function_value_call_args_b_sound; eassumption);
        try (apply fn_params_roots_exclude_b_sound; eassumption);
        try (apply fn_params_root_env_excludes_b_sound; eassumption).
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
    }
    { right. right. right. right. right. left.
      destruct (local_fn_value_call_target_expr_with_binder (fn_body fdef))
        as [[[[x fname] args] synthetic_body] |] eqn:Htarget; try discriminate.
      repeat rewrite andb_true_iff in Hlocal.
      destruct Hlocal as [[[Hsafe_args Hnot_free_b] Hnot_local_b] Hlocal].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
        eqn:Hlookup_b; try discriminate.
      apply andb_true_iff in Hlocal as [Hcallee_generic Hlocal].
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hlocal.
      destruct Hlocal as [[Hcompat Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      pose proof
        (check_fn_root_shadow_generic_direct_store_safe_summary_sound
          env fcallee Hcallee_generic) as Hcallee_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists x, fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
      split.
      { rewrite <- args_free_vars_checker_eq.
        apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnot_free_b. }
      split.
      { apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnot_local_b. }
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split; [exact Hcallee_summary |].
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
    }
  - right. right. right. right. right. right.
    destruct (infer_core_env_roots_shadow_safe_checked env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef))
      as [[[[T_body Gamma_body] R_body] roots_body] | err] eqn:Hcore;
      try discriminate.
    destruct (infer_env_roots_shadow_safe_checked env fdef
      (initial_root_env_for_fn fdef))
      as [[[[T_env Gamma_env] R_env] roots_env] | err] eqn:Hinfer_env;
      try discriminate.
    repeat rewrite andb_true_iff in Hnarrow.
    destruct Hnarrow as [[[Hexpr Hcompat] Hroots] Henv].
    destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_sound
      env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef)
      T_body Gamma_body R_body roots_body Hcore Hexpr)
      as [ret_roots Hsummary].
    exists T_body, Gamma_body, R_body, roots_body, ret_roots.
    repeat split.
    + eapply infer_env_roots_shadow_safe_checked_params_nodup.
      exact Hinfer_env.
    + exact Hsummary.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Definition env_fns_root_shadow_captured_call_store_safe_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.

Lemma check_env_root_shadow_captured_call_store_safe_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_store_safe_summary env = true ->
    env_fns_root_shadow_captured_call_store_safe_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_store_safe_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
  exact Hcheck.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_summary_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_store_safe_summary_fuel] in Hcheck.
    rewrite Hinfer in Hcheck.
    repeat (apply orb_true_iff in Hcheck as [Hcheck | Hcheck]).
    + destruct (check_expr_root_shadow_captured_call_provenance_summary_fuel_sound
        (S fuel') env Omega n R Σ e T Σ' R' roots Hinfer Hcheck)
        as [ret_roots Hexact].
      exists ret_roots. apply ERSS_Exact. exact Hexact.
    + destruct e; try discriminate.
      apply andb_true_iff in Hcheck as [Hready_args Hsupported].
      pose proof
        (check_supported_non_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hinfer_callee & Hcallee_shape).
      subst e.
      exists roots.
      eapply ERSS_FunctionValueCall.
      * apply preservation_ready_args_b_sound. exact Hready_args.
      * exact Hinfer_callee.
      * exact Hcallee_shape.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2i Sigma2i] R2i] roots2i] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[[Hfreei_ret Hsctx_oki] Hroots2i] Henv2i]
        Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i t m Σ1) e2 T2i Sigma2i R2i roots2i Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_oki, Hroots2i, Henv2i in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSS_Let.
      * exact Hbound_summary.
      * exact Hcompat.
      * exact Hlookup_x.
      * apply roots_exclude_b_sound. exact Hroots1.
      * apply root_env_excludes_b_sound. exact Henv1.
      * exact Hbody_summary.
      * exact Hfreei_ret.
      * exact Hsctx_oki.
      * apply roots_exclude_b_sound. exact Hroots2i.
      * apply root_env_excludes_b_sound. exact Henv2i.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err]
        eqn:Hcond; try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans) eqn:Hcond_core;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Helse_check].
      apply andb_true_iff in Hhead as [Hhead Hthen_check].
      apply andb_true_iff in Hhead as [Hcond_bool Hready_cond].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e2) as [[[[T2i Sigma2i] R2i] roots2i] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e3) as [[[[T3 Sigma3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2i) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2i R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Sigma2i) (ctx_of_sctx Sigma3))
        as [Sigma4 |] eqn:Hmerge; try discriminate.
      destruct (IH env Omega n R1 Σ1 e2 T2i Sigma2i R2i roots2i Hthen
        Hthen_check) as [ret_roots2i Hthen_summary].
      destruct (IH env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      exists (root_set_union ret_roots2i ret_roots3).
      eapply ERSS_If.
      * apply provenance_ready_expr_b_sound. exact Hready_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true. exact Hroot_eq.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_summary
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_summary,
    infer_core_env_roots_shadow_safe.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Omega n R
    (sctx_of_ctx Gamma) e) as [[[[T0 Sigma0] R0] roots0] | err]
    eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_summary_fuel_sound;
    eassumption.
Qed.

Lemma initial_root_env_for_params_covers :
  forall ps,
    root_env_covers_params ps (initial_root_env_for_params ps).
Proof.
  induction ps as [| p ps IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Hx | Hin].
    + subst x. exists [RParam (param_name p)].
      simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl.
      destruct (ident_eqb x (param_name p)) eqn:Heq.
      * exists [RParam (param_name p)]. reflexivity.
      * destruct (IH x Hin) as [roots Hlookup].
        exists roots. exact Hlookup.
Qed.

Lemma initial_root_env_for_fn_covers :
  forall f,
    root_env_covers_params (fn_params f) (initial_root_env_for_fn f).
Proof.
  intros f.
  unfold initial_root_env_for_fn.
  apply initial_root_env_for_params_covers.
Qed.

Lemma runtime_struct_expr_true : forall e,
  struct_expr e = true.
Proof.
  fix IH 1.
  intro e.
  destruct e; simpl; try reflexivity.
  - rewrite IH, IH. reflexivity.
  - rewrite IH, IH. reflexivity.
	  - induction l as [| a rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
	  - induction l0 as [| a rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
	  - rewrite IH.
	    induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l0 as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l1 as [| [fname field] rest IHfields]; simpl.
    + reflexivity.
    + rewrite IH, IHfields. reflexivity.
	  - induction l1 as [| payload rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| [[name binders] branch] rest IHbranches]; simpl.
    + reflexivity.
    + rewrite IH, IHbranches. reflexivity.
	  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, IH, IH. reflexivity.
Qed.

Lemma infer_core_env_runtime_structural_sound :
  forall env Ω n Γ e T Γ',
    infer_core_env env Ω n Γ e = infer_ok (T, Γ') ->
    typed_env_structural env Ω n (sctx_of_ctx Γ) e T (sctx_of_ctx Γ').
Proof.
  unfold infer_core_env, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n Γ e T Γ' Hinfer.
  destruct (infer_core_env_state_fuel 10000 env Ω n Γ e) as [[T0 Σ] | err]
    eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_struct_structural_sound.
  - apply runtime_struct_expr_true.
  - exact Hcore.
Qed.

Lemma infer_env_runtime_structural_sound :
  forall env f T Γ',
    infer_env env f = infer_ok (T, Γ') ->
    typed_fn_env_structural env f.
Proof.
  unfold infer_env, typed_fn_env_structural.
  intros env f T Γ' Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env (global_env_with_local_bounds env (fn_bounds f))
              (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
              (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompatible; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_out) eqn:Hparams;
    try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ'.
  repeat split.
  - eapply infer_core_env_runtime_structural_sound. exact Hcore.
  - exact Hcompatible.
  - exact Hparams.
Qed.

Lemma call_body_start_state_param_scope :
  forall env Ω s_args vs ps,
    eval_args_values_have_types env Ω s_args vs ps ->
    store_param_scope ps (bind_params ps vs s_args) s_args /\
    root_env_covers_params ps (initial_root_env_for_params ps).
Proof.
  intros env Ω s_args vs ps Hargs.
  split.
  - eapply store_param_scope_bind_params. exact Hargs.
  - apply initial_root_env_for_params_covers.
Qed.

Theorem infer_full_env_roots_big_step_safe_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed env f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Htyped)
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready
    Hroots Hstore_shadow Hroot_shadow Heval.
  eapply infer_full_env_roots_big_step_safe_ready; eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_structural_ready :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_ready_expr (fn_body f) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v Hinfer Hstore Hready Heval.
  unfold infer_full_env in Hinfer.
  destruct (infer_env (alpha_normalize_global_env env) f)
    as [[T0 Γ0] | err] eqn:Hinfer_env; try discriminate.
  destruct (borrow_check_env (alpha_normalize_global_env env) []
              (fn_body_ctx f) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  eapply typed_fn_env_structural_big_step_safe_ready.
  - eapply infer_env_runtime_structural_sound. exact Hinfer_env.
  - exact Hready.
  - exact (initial_store_for_fn_store_typed (alpha_normalize_global_env env) f s Hstore).
  - exact Heval.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed env f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique_body_env Hfns_ready_body_env
      (direct_call_callee_body_root_evidence_of_check body_env
        Hcallee_body_roots))
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_evidence :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed env f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique_body_env Hfns_ready_body_env Hcallee_body_roots)
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready Hroots
    Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready Hcallee_roots Heval.
  eapply infer_full_env_roots_big_step_safe_direct_call_ready; eassumption.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_direct_call_evidence :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready Hroots
    Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready Hcallee_roots Heval.
  eapply infer_full_env_roots_big_step_safe_direct_call_evidence;
    eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_summary_check_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_summary_bridge
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hsummary
    Hbridge Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_evidence;
    try eassumption.
  eapply direct_call_callee_body_root_evidence_of_summary_bridge.
  - apply env_fns_root_summary_evidence_of_check.
    apply env_fns_root_summary_check_ready_global_env_with_local_bounds.
    exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    direct_call_callee_body_root_shadow_summary_bridge
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hsummary
    Hbridge Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_evidence;
    try eassumption.
  eapply direct_call_callee_body_root_evidence_of_shadow_summary_bridge.
  - exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge_of_unique :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hroots_infer Hsummary
    Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge;
    try eassumption.
  apply direct_call_callee_body_root_shadow_summary_bridge_of_unique.
  exact Hunique.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_shadow_summary_sidecar :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hroots_infer Hsummary
    Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge_of_unique;
    eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_shadow_summary_evidence :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within (initial_root_env_for_fn f) s ->
    store_no_shadow s ->
    root_env_store_roots_named (initial_root_env_for_fn f) s ->
    root_env_store_keys_named (initial_root_env_for_fn f) s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v _ Hsummary Hin Hstore Hready Hroots
    Hstore_shadow Hnamed Hkeys Hunique Hfns_ready Heval.
  destruct (env_fns_root_shadow_summary_evidence_in_unique
              (alpha_normalize_global_env env) Hsummary Hunique
              (fn_name f) f Hin eq_refl)
    as [Hnodup Hbody_summary].
  unfold callee_body_root_shadow_ready_at in Hbody_summary.
  destruct Hbody_summary as
    (T_body & Γ_out & R_body & roots_body &
      _ & _ & Htyped_shadow & Hcompat & _ & _).
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
  pose (body_env :=
    global_env_with_local_bounds (alpha_normalize_global_env env)
      (fn_bounds f)).
  assert (Hstore_body_env :
      store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed (alpha_normalize_global_env env) f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  assert (Hsummary_body :
      env_fns_root_shadow_summary_evidence body_env).
  { subst body_env.
    apply env_fns_root_shadow_summary_evidence_global_env_with_local_bounds.
    exact Hsummary. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
      (typed_env_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
        Htyped_shadow)
      Hunique_body_env Hfns_ready_body_env
      (direct_call_callee_body_root_evidence_of_shadow_summary_bridge
        body_env
        Hsummary_body
        (direct_call_callee_body_root_shadow_summary_bridge_of_unique
          body_env Hunique_body_env)))
    as [_ [Hv _]].
  assert (Hv_env :
      value_has_type (alpha_normalize_global_env env) s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.
