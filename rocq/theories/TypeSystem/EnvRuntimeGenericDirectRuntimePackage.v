From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectRuntimePackageBase
  EnvRuntimeCapturedCallFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma generic_direct_call_cleanup_value_from_body_package :
  forall env sigma type_args ps_runtime fdef fcall s_body ret T_body R_body
      roots_body frame_final,
    value_has_type env s_body ret T_body ->
    ty_compatible_b (fn_outlives fcall) T_body
      (subst_type_params_ty type_args (fn_ret fcall)) = true ->
    alpha_rename_fn_def [] fdef = (fcall, []) \/
      fn_ret fcall = fn_ret fdef ->
    store_param_scope ps_runtime s_body frame_final ->
    store_roots_within R_body s_body ->
    value_roots_within roots_body ret ->
    store_no_shadow s_body ->
    NoDup (ctx_names (params_ctx ps_runtime)) ->
    roots_exclude_params ps_runtime roots_body ->
    root_env_excludes_params ps_runtime R_body ->
    (fn_ret fcall = fn_ret fdef) ->
    value_has_type env (store_remove_params ps_runtime s_body) ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env sigma type_args ps_runtime fdef fcall s_body ret T_body R_body
    roots_body frame_final Hv_body Hcompat _ Hscope Hroots Hret_roots Hshadow
    Hnodup Hexclude_roots Hexclude_env Hret_eq.
  assert (Hv_ret_fcall :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fcall))).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat. }
  assert (Hv_ret_fdef :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fdef))).
  { rewrite <- Hret_eq. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              ps_runtime s_body frame_final R_body roots_body ret
              Hscope Hroots Hret_roots Hshadow Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  apply value_has_type_apply_lt_ty.
  eapply value_has_type_store_remove_params_excluding.
  - exact Hv_ret_fdef.
  - exact Hret_exclude.
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_expr :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
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
    Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  dependent destruction Heval_call.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  | Hlookup_fn : lookup_fn ?fname_call ?fns = Some ?f_runtime |- _ =>
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
  pose proof (typed_args_roots_params_of_tys_map_param_ty
    env Omega n R Sigma args
    (apply_lt_params sigma
      (apply_type_params type_args (fn_params fdef)))
    Sigma_args R_args arg_roots Htyped_args) as Htyped_args_param_tys.
  pose proof (runtime_tfn_signature_bridge_apply_lt_params
    sigma (apply_type_params type_args (fn_params fdef))
    (subst_type_params_ty type_args (fn_ret fdef))) as Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
    env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args Hready_args) as Hprov_args.
  destruct (generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args type_args fdef fcall
    (map param_ty
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef))))
    (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
    s s_args vs used' Hsummary Hcaps_fdef Hbridge Hsafe_args
    Htyped_args_param_tys Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
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
  assert (Hnodup : NoDup (ctx_names (params_ctx ps_runtime))).
  { subst ps_runtime.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  pose (body_env := global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall))).
  fold body_env in Hsummary_body.
  fold ps_runtime in Hsummary_body.
  rename Hsummary_body into Hsummary_body_env.
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
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret Hstore_bind_body_env
    Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind
    Hsummary_bind_body_env Heval_body_body_env Hunique_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
      [Hrootset_body [Hshadow_body [Hrn_body [Hnamed_body
        [Hkeys_body Hsummary_body_store]]]]]]]]]].
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret ps_runtime s_args
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env
    Hcover_bind Hframe_start)
    as [frame_final Hscope_body].
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fcall))).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hv_ret_fdef :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fdef))).
  { rewrite Hret_alpha. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              ps_runtime s_body frame_final R_body roots_body ret
              Hscope_body Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params ps_runtime s_body) ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  exact Hv_final.
Qed.
