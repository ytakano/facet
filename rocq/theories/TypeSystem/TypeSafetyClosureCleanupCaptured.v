From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyClosureCleanupCtxErased.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready_in_frame env captured Rcap s_args R_args
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    value_roots_within roots_body ret /\
    store_remove_params (fn_captures fcall)
      (store_remove_params (fn_params fcall) s_body) = s_args.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured Rcap
    s_args R_args Σ_args fdef fcall σ s_body vs ret used' T_body Γ_out
    R_params R_body roots_body Hframe_params_ready Htyped_args Hrename
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body
    Htyped_body Hcompat_body Hexclude_all Hexclude_env_all Heval_body.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  pose proof (captured_params_store_typed_in_frame_store_param_prefix
                env captured s_args (fn_captures fcall)
                Hcaptured_params_typed)
    as Hprefix_caps0.
  pose proof (store_param_prefix_append_frame
                (fn_captures fcall) captured s_args []
                Hprefix_caps0) as Hprefix_caps.
  simpl in Hprefix_caps.
  pose proof (store_param_prefix_bind_params
                env Ω (captured ++ s_args) vs (fn_params fcall)
                Hargs_fcall) as Hprefix_params.
  pose proof (store_param_prefix_app
                (fn_params fcall) (fn_captures fcall)
                (bind_params (fn_params fcall) vs (captured ++ s_args))
                (captured ++ s_args) s_args
                Hprefix_params Hprefix_caps) as Hprefix_all.
  assert (Hnodup_all :
    NoDup (ctx_names
      (params_ctx (fn_params fcall ++ fn_captures fcall)))).
  { pose proof (store_names_store_param_prefix
                  (fn_params fcall ++ fn_captures fcall)
                  (bind_params (fn_params fcall) vs (captured ++ s_args))
                  s_args Hprefix_all) as Hnames_prefix.
    unfold store_no_shadow in Hshadow_bind.
    rewrite Hnames_prefix in Hshadow_bind.
    exact (NoDup_app_left_ts _ _ Hshadow_bind). }
  assert (Hstore_captured_prefix :
    store_typed_prefix env (captured ++ s_args)
      (sctx_of_ctx (params_ctx (fn_captures fcall)))).
  { eapply captured_params_store_typed_in_frame_prefix_frame.
    exact Hcaptured_params_typed. }
  assert (Hnodup_params :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hstore_bind_prefix :
    store_typed_prefix env
      (bind_params (fn_params fcall) vs (captured ++ s_args))
      (sctx_of_ctx (fn_body_ctx fcall))).
  { pose proof (bind_params_store_typed_prefix_extend
                  env Ω (captured ++ s_args)
                  (sctx_of_ctx (params_ctx (fn_captures fcall)))
                  vs (fn_params fcall) Hstore_captured_prefix
                  Hnodup_params Hfresh_params Hargs_fcall)
      as Hprefix.
    unfold fn_body_ctx, fn_body_params, sctx_of_ctx in *.
    rewrite params_ctx_app. exact Hprefix. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Hstore_bind_prefix_body_env :
    store_typed_prefix body_env
      (bind_params (fn_params fcall) vs (captured ++ s_args))
      (sctx_of_ctx (fn_body_ctx fcall))).
  { subst body_env.
    eapply cleanup_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_prefix. }
  assert (Heval_body_body_env :
    eval body_env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret).
  { subst body_env.
    eapply cleanup_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall ++ fn_captures fcall)
      (sctx_of_ctx (fn_body_ctx fcall))
      (bind_params (fn_params fcall) vs (captured ++ s_args))
      s_args).
  { unfold fn_body_ctx, fn_body_params, sctx_of_ctx.
    constructor. exact Hprefix_all. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh (sctx_of_ctx (fn_body_ctx fcall)) s_args).
  { unfold fn_body_ctx, fn_body_params, sctx_of_ctx.
    eapply store_param_prefix_frame_static_fresh; eassumption. }
  destruct (proj1 Hframe_mutual
              body_env
              (bind_params (fn_params fcall) vs (captured ++ s_args))
              (fn_body fcall) s_body ret Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall ++ fn_captures fcall) s_args
              Hprov_body Htyped_body Hcover_all Hroots_bind Hshadow_bind
              Hrn_params Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  pose proof (proj1 Htyping_mutual
                body_env
                (bind_params (fn_params fcall) vs (captured ++ s_args))
                (fn_body fcall) s_body ret Heval_body_body_env
                (fn_outlives fcall) (fn_lifetimes fcall)
                R_params (sctx_of_ctx (fn_body_ctx fcall))
                T_body (sctx_of_ctx Γ_out) R_body roots_body
                Hprov_body Hstore_bind_prefix_body_env Hroots_bind Hshadow_bind
                Hrn_params Htyped_body) as Hbody_package.
  destruct (typed_rooted_eval_roots _ _ _ _ _ _ _ _ Hbody_package)
    as [Hroots_body Hret_roots Hshadow_body _].
  destruct Hbody_package as [Hstore_body Hv_body _ _].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret _]].
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply cleanup_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct Hparam_mutual as [Hscope_expr _].
  assert (Hscope_start :
    store_param_scope (fn_params fcall ++ fn_captures fcall)
      (bind_params (fn_params fcall) vs (captured ++ s_args)) s_args).
  { constructor. exact Hprefix_all. }
  destruct (Hscope_expr body_env
              (bind_params (fn_params fcall) vs (captured ++ s_args))
              (fn_body fcall) s_body ret Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall ++ fn_captures fcall) s_args
              Hprov_body Htyped_body)
              as [frame_final Hscope_body].
  { exact Hcover_all. }
  { exact Hscope_start. }
  assert (Hsame_body :
    sctx_same_bindings (sctx_of_ctx (fn_body_ctx fcall))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  destruct (eval_call_body_ctx_cleanup_erased_core
              env Ω s_args Σ_args fdef fcall σ s_body ret T_body Γ_out
              R_body roots_body frame_final Htyped_args Hret Hnodup_all
              Hframe_scope Hscope_body Hv_body_env Hroots_body Hret_roots
              Hshadow_body Hsame_body Hcompat_body Hexclude_all
              Hexclude_env_all)
    as [Hstore_erased [Hv_erased [Hremoved_exact_all _]]].
  assert (Hfinal_exact :
    store_remove_params (fn_captures fcall)
      (store_remove_params (fn_params fcall) s_body) = s_args).
  { rewrite <- store_remove_params_app. exact Hremoved_exact_all. }
  repeat split; try assumption.
  - rewrite <- store_remove_params_app. exact Hstore_erased.
  - rewrite <- store_remove_params_app. exact Hv_erased.
Qed.

Lemma eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) s s_fn s_args s_body callee args fname
      captured fdef fcall vs ret used' Rcap R_args Σ_args σ T_body Γ_out
      R_params R_body roots_body,
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    captured_call_frame_params_ready_in_frame env captured Rcap s_args R_args
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env s (ECallExpr callee args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    value_roots_within roots_body ret /\
    store_remove_params (fn_captures fcall)
      (store_remove_params (fn_params fcall) s_body) = s_args.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_fn s_args
    s_body callee args fname captured fdef fcall vs ret used' Rcap R_args
    Σ_args σ T_body Γ_out R_params R_body roots_body Heval_callee Hlookup
    Heval_args Hrename Heval_body Hframe_params_ready Htyped_args
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body
    Htyped_body Hcompat_body Hexclude_all Hexclude_env_all.
  split.
  - eapply Eval_CallExpr; eassumption.
  - assert (Hcleanup :
      store_typed env
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body)) Σ_args /\
      value_has_type env
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body))
        ret (apply_lt_ty σ (fn_ret fdef)) /\
      value_roots_within roots_body ret /\
      store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body) = s_args).
    { eapply
        (eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
          Hframe_mutual
          Htyping_mutual
          Hparam_mutual);
        eassumption. }
    destruct Hcleanup as [Hstore [Hv [Hret_roots Hfinal]]].
    repeat split; assumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_store captured ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured Rcap
    s_args R_args Σ_args fdef fcall σ s_body vs ret used' T_body
    Γ_out R_params R_body roots_body Hframe_ready Htyped_args Hrename
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_params
    Hprov_body Htyped_body Hcompat_body Hexclude_ret Hexclude_env
    Heval_body.
  eapply (eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core
            Hframe_mutual
            Htyping_mutual
            Hparam_mutual);
    try eassumption.
  eapply captured_call_frame_store_typed_in_frame; eassumption.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) s s_fn s_args s_body callee args fname
      captured fdef fcall vs ret used' Rcap R_args Σ_args σ T_body Γ_out
      R_params R_body roots_body,
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env s (ECallExpr callee args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_store captured ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_fn s_args
    s_body callee args fname captured fdef fcall vs ret used' Rcap R_args
    Σ_args σ T_body Γ_out R_params R_body roots_body Heval_callee Hlookup
    Heval_args Hrename Heval_body Hframe_ready Htyped_args Hargs_fcall
    Hroots_bind Hshadow_bind Hrn_params Hcover_params Hprov_body
    Htyped_body Hcompat_body Hexclude_ret Hexclude_env.
  split.
  - eapply Eval_CallExpr; eassumption.
  - eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core
              Hframe_mutual
              Htyping_mutual
              Hparam_mutual);
      eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args caps
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured Rcap
    s_args R_args Σ_args caps fdef fcall σ s_body vs ret used' T_body
    Γ_out R_params R_body roots_body Hframe_params_ready Htyped_args
    Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_params Hprov_body Htyped_body Hcompat_body Hexclude_ret
    Hexclude_env Heval_body.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  destruct
    (eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core
      Hframe_mutual
      Htyping_mutual
      Hparam_mutual
      env Ω captured Rcap s_args R_args Σ_args fdef fcall σ s_body vs
      ret used' T_body Γ_out R_params R_body roots_body
      (captured_call_frame_ready_in_frame_from_self
        env captured Rcap s_args R_args Hframe_ready)
      Htyped_args Hrename Hargs_fcall Hroots_bind Hshadow_bind
      Hrn_params Hcover_params Hprov_body Htyped_body Hcompat_body
      Hexclude_ret Hexclude_env Heval_body)
    as [_ Hcleanup].
  destruct Hcleanup as [Hprefix Hcleanup].
  destruct Hcleanup as [Hroots_body Hcleanup].
  destruct Hcleanup as [Hshadow_body Hcleanup].
  destruct Hcleanup as [Hrn_body Hcleanup].
  destruct Hcleanup as [Hv_ret Hcleanup].
  destruct Hcleanup as [Hpres Hcleanup].
  destruct Hcleanup as [frame_final [locals [Hscope [Hremoved
    [Hret_exclude [Hstore_exclude [Hremoved_exact Hroots_ret]]]]]]].
  assert (Htyped_frame :
    store_typed env (captured ++ s_args)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args)).
  { eapply captured_call_frame_params_store_typed.
    - split; eassumption.
    - exact Htyped_args. }
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Htyped_frame.
  - exists frame_final, locals. repeat split; assumption.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs_params_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) s s_fn s_args s_body callee args fname
      captured fdef fcall vs ret used' Rcap R_args Σ_args caps σ T_body
      Γ_out R_params R_body roots_body,
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env s (ECallExpr callee args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_fn s_args
    s_body callee args fname captured fdef fcall vs ret used' Rcap R_args
    Σ_args caps σ T_body Γ_out R_params R_body roots_body Heval_callee
    Hlookup Heval_args Hrename Heval_body Hframe_params_ready Htyped_args
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_params
    Hprov_body Htyped_body Hcompat_body Hexclude_ret Hexclude_env.
  split.
  - eapply Eval_CallExpr; eassumption.
  - eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_params_with_preservation_core
              Hframe_mutual
              Htyping_mutual
              Hparam_mutual);
      eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args caps
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    roots_exclude_params caps roots_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove_params caps
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params caps
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove_params caps
      (store_remove_params (fn_params fcall) s_body) = s_args.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured Rcap
    s_args R_args Σ_args caps fdef fcall σ s_body vs ret used' T_body
    Γ_out R_params R_body roots_body Hframe_params_ready Htyped_args
    Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_params Hprov_body Htyped_body Hcompat_body Hexclude_ret
    Hexclude_env Hexclude_caps Heval_body.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  destruct
    (eval_captured_call_body_cleanup_preserves_value_and_refs_params_with_preservation_core
      Hframe_mutual
      Htyping_mutual
      Hparam_mutual
      env Ω captured Rcap s_args R_args Σ_args caps fdef fcall σ
      s_body vs ret used' T_body Γ_out R_params R_body roots_body
      (conj Hframe_ready Hcaptured_params_typed) Htyped_args Hrename
      Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_params
      Hprov_body Htyped_body Hcompat_body Hexclude_ret Hexclude_env
      Heval_body)
    as [Hstore_frame Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [Hv_ret Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [frame_final [locals [_ [_ [_ [_
    [Hremoved_exact Hroots_ret]]]]]]].
  assert (Hfinal_exact :
    store_remove_params caps
      (store_remove_params (fn_params fcall) s_body) = s_args).
  { rewrite Hremoved_exact.
    eapply captured_params_store_typed_remove_app.
    exact Hcaptured_params_typed. }
  repeat split.
  - rewrite Hfinal_exact. exact Htyped_args.
  - rewrite Hremoved_exact.
    eapply value_has_type_store_remove_params_excluding.
    + rewrite <- Hremoved_exact. exact Hv_ret.
    + eapply value_roots_exclude_params; eassumption.
  - exact Hfinal_exact.
Qed.
