From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace
  TypeSafetyLocalFacts TypeSafetyRootNamed TypeSafetyBasePreservation
  TypeSafetyPrefixPreservation TypeSafetyRootPreservation
  TypeSafetyPreservationWrappers.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.
Lemma eval_call_body_cleanup_preserves_value_and_refs_frame :
  forall env (Ω : outlives_ctx) frame Σ_frame fdef fcall σ s_body vs ret
      used' T_body Γ_out R_params R_body roots_body,
    store_typed env frame Σ_frame ->
    alpha_rename_fn_def (store_names frame) fdef = (fcall, used') ->
    eval_args_values_have_types env Ω frame vs (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs frame) ->
    store_no_shadow (bind_params (fn_params fcall) vs frame) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs frame)
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_frame /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env frame
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = frame /\
    value_roots_within roots_body ret.
Proof.
  eapply (eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs :
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_ready env captured Rcap s_args R_args ->
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
  intros env Ω captured Rcap s_args R_args Σ_args fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body Hframe_ready
    Htyped_args Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_params Hprov_body Htyped_body Hcompat_body Hexclude_ret
    Hexclude_env Heval_body.
  eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    try eassumption.
  eapply captured_call_frame_ready_in_frame_from_self.
  exact Hframe_ready.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs :
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
    captured_call_frame_ready env captured Rcap s_args R_args ->
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
  intros env Ω s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret used' Rcap R_args Σ_args σ T_body Γ_out R_params R_body
    roots_body Heval_callee Hlookup Heval_args Hrename Heval_body
    Hframe_ready Htyped_args Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_params Hprov_body Htyped_body Hcompat_body
    Hexclude_ret Hexclude_env.
  eapply (eval_captured_call_expr_cleanup_preserves_value_and_refs_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    try eassumption.
  eapply captured_call_frame_ready_in_frame_from_self.
  exact Hframe_ready.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params :
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
  eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_params_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs_params :
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
  eapply (eval_captured_call_expr_cleanup_preserves_value_and_refs_params_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased :
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
  eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased :
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready env captured Rcap s_args R_args
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
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
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
    store_remove_params (fn_captures fcall)
      (store_remove_params (fn_params fcall) s_body) = s_args.
Proof.
  intros env Ω captured Rcap s_args R_args Σ_args fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body Hframe_ready
    Htyped_args Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_all Hprov_body Htyped_body Hcompat_body Hexclude_all
    Hexclude_env_all Heval_body.
  eapply (eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    try eassumption.
  eapply captured_call_frame_params_ready_in_frame_from_self.
  exact Hframe_ready.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased :
  forall env (Ω : outlives_ctx) captured s_args_hidden s_args
      Σ_args x T_hidden hidden fdef fcall σ s_body vs ret used'
      T_body Γ_out R_params R_body roots_body,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    captured_params_store_typed env captured (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    store_no_shadow
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    roots_exclude x roots_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body))) Σ_args /\
    value_has_type env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body)))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset :
  forall env (Ω : outlives_ctx) captured s_args_hidden s_args
      Σ_args x T_hidden hidden fdef fcall σ s_body vs ret used'
      T_body Γ_out R_params R_body roots_body roots_bound,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    captured_params_store_typed env captured (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    store_no_shadow
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    root_set_stores_subset roots_body roots_bound ->
    roots_exclude x roots_bound ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body))) Σ_args /\
    value_has_type env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body)))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_hidden_cleanup_package :
  forall env (Ω : outlives_ctx) s s_final m x T fname captures args ret,
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args)) s_final ret ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s ->
    exists captured fdef s_args_hidden s_args vs fcall used' s_body,
      lookup_fn fname (env_fns env) = Some fdef /\
      copy_capture_store_as captures (fn_captures fdef) s = Some captured /\
      s_args_hidden = store_add x T (VClosure fname captured) s_args /\
      eval_args env s args s_args vs /\
      store_refs_exclude_root x s_args /\
      Forall (value_refs_exclude_root x) vs /\
      alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
        (fcall, used') /\
      eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
        (fn_body fcall) s_body ret /\
      s_final =
        store_remove x
          (store_remove_params (fn_captures fcall)
            (store_remove_params (fn_params fcall) s_body)) /\
      forall sigma_result Σ_args T_body Γ_out R_params R_body roots_body roots_bound,
        captured_params_store_typed env captured (fn_captures fcall) ->
        store_typed env s_args Σ_args ->
        eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
          (fn_params fcall) ->
        store_roots_within R_params
          (bind_params (fn_params fcall) vs
            (captured ++ s_args_hidden)) ->
        store_no_shadow
          (bind_params (fn_params fcall) vs
            (captured ++ s_args_hidden)) ->
        root_env_no_shadow R_params ->
        root_env_covers_params (fn_params fcall ++ fn_captures fcall)
          R_params ->
        provenance_ready_expr (fn_body fcall) ->
        typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
          R_params (sctx_of_ctx (fn_body_ctx fcall))
          (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
        ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
        roots_exclude_params (fn_params fcall ++ fn_captures fcall)
          roots_body ->
        root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
          R_body ->
        root_set_stores_subset roots_body roots_bound ->
        roots_exclude x roots_bound ->
        store_typed env s_final Σ_args /\
        value_has_type env s_final ret (apply_lt_ty sigma_result (fn_ret fdef)) /\
        s_final = s_args.
Proof.
  eapply (eval_let_make_closure_captured_call_hidden_cleanup_package_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased :
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
    captured_call_frame_params_ready env captured Rcap s_args R_args
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
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
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
      ret (apply_lt_ty σ (fn_ret fdef)).
Proof.
  intros env Ω s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret used' Rcap R_args Σ_args σ T_body Γ_out R_params R_body
    roots_body Heval_callee Hlookup Heval_args Hrename Heval_body
    Hframe_params_ready Htyped_args Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body Hexclude_all
    Hexclude_env_all.
  eapply (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    try eassumption.
  eapply captured_call_frame_params_ready_in_frame_from_self.
  exact Hframe_params_ready.
Qed.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased :
  forall env (Ω : outlives_ctx) s s_args s_body args fname captures
      captured fdef fcall vs ret used' Rcap R_args Σ Σ_args captured_tys
      σ T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures (fn_captures fdef) =
      infer_ok captured_tys ->
    captured_call_frame_ready env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)).
Proof.
  eapply (eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto :
  forall env (Ω : outlives_ctx) s s_args s_body args fname captures
      captured fdef fcall vs ret used' R_args Σ Σ_args captured_tys
      σ T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures (fn_captures fdef) =
      infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)).
Proof.
  eapply (eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_runtime_args_ready_auto :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args vs R_args Σ_args arg_roots captured_tys,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args R_args
      (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args)).
Proof.
  eapply
    (eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_auto :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args_hidden s_args vs R_args Σ_args arg_roots captured_tys x T,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    ~ In x (store_names captured) ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args)).
Proof.
  eapply
    (eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args s_body vs ret R_args Σ_args arg_roots captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  eapply
    (eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.
Lemma eval_make_closure_captured_call_expr_preserves_typing_with_callee_components :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args s_body vs ret R_args Σ_args arg_roots env_lt captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  eapply
    (eval_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components :
  forall env Ω n R Σ m x T args fname captures fdef
      s s_final ret R_args Σ_args arg_roots captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args)) s_final ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    lookup_fn fname (env_fns env) = Some fdef ->
    ~ In x (store_names s) ->
    ~ In x (ctx_names (params_ctx (fn_captures fdef))) ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_typed env s_final Σ_args /\
    value_has_type env s_final ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  eapply
    (eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.
