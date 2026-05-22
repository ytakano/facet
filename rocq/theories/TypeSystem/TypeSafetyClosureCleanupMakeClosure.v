From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyClosureCleanupCaptured.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_args s_body
    args fname captures captured fdef fcall vs ret used' Rcap R_args Σ
    Σ_args captured_tys σ T_body Γ_out R_params R_body roots_body Hstore
    Heval_make Hlookup Heval_args Hrename Heval_body Hcheck Hframe_ready
    Htyped_args Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all
    Hprov_body Htyped_body Hcompat_body Hexclude_all Hexclude_env_all.
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready
      env Ω s Σ fname captures captured fdef fcall used' Rcap s_args
      R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck
      Hframe_ready) as Hframe_params_ready.
  destruct
    (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
      Hframe_mutual
      (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
        Htyping_mutual)
      Hparam_mutual env Ω s s s_args s_body
      (EMakeClosure fname captures) args fname captured fdef fcall vs ret
      used' Rcap R_args Σ_args σ T_body Γ_out R_params R_body roots_body
      Heval_make Hlookup Heval_args Hrename Heval_body)
    as [Heval_final [Hstore_final [Hv_final _]]].
  - eapply captured_call_frame_params_ready_in_frame_from_self.
    exact Hframe_params_ready.
  - exact Htyped_args.
  - exact Hargs_fcall.
  - exact Hroots_bind.
  - exact Hshadow_bind.
  - exact Hrn_params.
  - exact Hcover_all.
  - exact Hprov_body.
  - exact Htyped_body.
  - exact Hcompat_body.
  - exact Hexclude_all.
  - exact Hexclude_env_all.
  - repeat split; assumption.
Qed.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_args s_body
    args fname captures captured fdef fcall vs ret used' R_args Σ Σ_args
    captured_tys σ T_body Γ_out R_params R_body roots_body Hstore
    Heval_make Hlookup Heval_args Hrename Heval_body Hcheck Hnodup
    Hready_args Hroots_args Hshadow_args Hrn_args Hnamed_args Hkeys_args
    Htyped_args Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all
    Hprov_body Htyped_body Hcompat_body Hexclude_all Hexclude_env_all.
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready_auto
      env Ω s Σ fname captures captured fdef fcall used' args s_args vs
      R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck Hnodup
      Hready_args Heval_args Hroots_args Hshadow_args Hrn_args Hnamed_args
      Hkeys_args) as Hframe_params_ready.
  destruct
    (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
      Hframe_mutual
      (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
        Htyping_mutual)
      Hparam_mutual env Ω s s s_args s_body
      (EMakeClosure fname captures) args fname captured fdef fcall vs ret
      used' (empty_root_env_for_store captured) R_args Σ_args σ T_body
      Γ_out R_params R_body roots_body Heval_make Hlookup Heval_args
      Hrename Heval_body)
    as [Heval_final [Hstore_final [Hv_final _]]].
  - eapply captured_call_frame_params_ready_in_frame_from_self.
    exact Hframe_params_ready.
  - exact Htyped_args.
  - exact Hargs_fcall.
  - exact Hroots_bind.
  - exact Hshadow_bind.
  - exact Hrn_params.
  - exact Hcover_all.
  - exact Hprov_body.
  - exact Htyped_body.
  - exact Hcompat_body.
  - exact Hexclude_all.
  - exact Hexclude_env_all.
  - repeat split; assumption.
Qed.
