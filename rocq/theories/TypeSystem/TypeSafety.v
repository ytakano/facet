From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace
  TypeSafetyLocalFacts TypeSafetyRootNamed TypeSafetyBasePreservation
  TypeSafetyPrefixPreservation TypeSafetyRootPreservation.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Theorem eval_preserves_typing_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  exact eval_preserves_typing_ready_mutual_core.
Qed.

Theorem typed_fn_env_structural_big_step_safe_ready :
  forall env f s s' v,
    typed_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  eapply typed_fn_env_structural_big_step_safe_ready_with_preservation_core.
  exact eval_preserves_typing_ready_mutual.
Qed.

Theorem checked_fn_env_structural_big_step_safe_ready :
  forall env f s s' v,
    checked_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  eapply checked_fn_env_structural_big_step_safe_ready_with_preservation_core.
  exact eval_preserves_typing_ready_mutual.
Qed.

Theorem eval_preserves_typing_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  exact eval_preserves_typing_ready_prefix_mutual_core.
Qed.

Theorem eval_preserves_roots_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s').
Proof.
  exact (eval_preserves_roots_ready_prefix_mutual_with_preservation_core
    eval_preserves_typing_ready_prefix_mutual).
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ_args fname args
      fdef fcall σ s s_args s_body vs ret used' T_body Γ_out,
    store_typed env s Σ ->
    preservation_ready_args args ->
    typed_args_env_structural env Ω n Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args ->
    eval_args env s args s_args vs ->
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    typed_env_structural env (fn_outlives fcall) (fn_lifetimes fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env s_args Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    value_has_type env s_body ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body.
Proof.
  eapply eval_direct_call_body_preserves_typing_prefix_with_preservation_core.
  - exact eval_preserves_typing_ready_mutual.
  - exact eval_preserves_typing_ready_prefix_mutual.
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix_from_lookup :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ_args fname args
      fdef fcall σ s s_args s_body vs ret used',
    store_typed env s Σ ->
    preservation_ready_args args ->
    typed_args_env_structural env Ω n Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args ->
    eval_args env s args s_args vs ->
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    fn_captures fcall = [] ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    exists Γ_out,
      store_typed env s_args Σ_args /\
      store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
      value_has_type env s_body ret (apply_lt_ty σ (fn_ret fdef)) /\
      store_ref_targets_preserved env
        (bind_params (fn_params fcall) vs s_args) s_body.
Proof.
  eapply eval_direct_call_body_preserves_typing_prefix_from_lookup_with_preservation_core.
  - exact eval_preserves_typing_ready_mutual.
  - exact eval_preserves_typing_ready_prefix_mutual.
Qed.

Theorem eval_preserves_typing_roots_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  exact eval_preserves_typing_roots_ready_prefix_mutual_core.
Qed.

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
  eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
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
  eapply (eval_captured_call_expr_cleanup_preserves_value_and_refs_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
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
  eapply (eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
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
  eapply (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
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

Lemma eval_direct_call_body_cleanup_preserves_value_and_refs :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall σ s s_args s_body vs ret used'
      T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    provenance_ready_args args ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env s_args Σ_args /\
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = s_args /\
    value_roots_within roots_body ret.
Proof.
  eapply (eval_direct_call_body_cleanup_preserves_value_and_refs_with_preservation_core
            eval_preserves_typing_ready_mutual
            eval_preserves_roots_ready_mutual
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Theorem eval_preserves_typing_ready_with_call_invariants_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  exact
    (eval_preserves_typing_ready_with_call_invariants_mutual_with_preservation_core
       eval_preserves_typing_ready_mutual).
Qed.

Lemma eval_let_roots_ready_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R R' Σ Σ' s s'
      m x T_ann e1 e2 T roots v,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ (ELet m x T_ann e1 e2) T Σ' R' roots ->
    provenance_ready_expr (ELet m x T_ann e1 e2) ->
    preservation_ready_expr e1 ->
    preservation_ready_expr e2 ->
    eval env s (ELet m x T_ann e1 e2) s' v ->
    store_typed env s' Σ' /\
    value_has_type env s' v T /\
    store_ref_targets_preserved env s s' /\
    store_roots_within R' s' /\
    value_roots_within roots v /\
    store_no_shadow s' /\
    root_env_no_shadow R'.
Proof.
  eapply eval_let_roots_ready_preserves_typing_with_preservation_core.
  - exact eval_preserves_typing_ready_mutual.
  - exact eval_preserves_roots_ready_mutual.
Qed.

Theorem eval_preserves_typing_roots_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  exact eval_preserves_typing_roots_ready_mutual_core.
Qed.

Theorem eval_preserves_root_names_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      Forall (fun roots => root_set_store_roots_named roots s') roots) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s').
Proof.
  apply eval_preserves_root_names_ready_mutual_core.
  exact eval_preserves_typing_roots_ready_mutual.
Qed.

Lemma eval_args_root_subst_images_exclude_names_for_fresh_call :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_subst_images_exclude_names
      (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fcall) arg_roots).
Proof.
  eapply
    (eval_args_root_subst_images_exclude_names_for_fresh_call_with_preservation_core
      eval_preserves_root_names_ready_mutual);
    eassumption.
Qed.

Theorem eval_preserves_root_keys_named_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_keys_named R' s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_keys_named R' s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_keys_named R' s').
Proof.
  apply eval_preserves_root_keys_named_ready_mutual_core.
  exact eval_preserves_typing_roots_ready_mutual.
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

Lemma eval_args_root_keys_exclude_names_for_fresh_call :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_keys_named R s ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    forall x,
      In x (expr_local_store_names (fn_body fcall)) ->
      root_env_lookup x R_args = None.
Proof.
  eapply
    (eval_args_root_keys_exclude_names_for_fresh_call_with_preservation_core
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_args_root_tail_fresh_names_for_fresh_call :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_env_tail_fresh_names (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  eapply
    (eval_args_root_tail_fresh_names_for_fresh_call_with_preservation_core
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_args_root_names_excludes_params_ready :
  forall env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots
      ps_bind,
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    params_fresh_in_store ps_bind s_args ->
    root_env_excludes_params ps_bind R_args.
Proof.
  eapply
    (eval_args_root_names_excludes_params_ready_with_preservation_core
      eval_preserves_root_names_ready_mutual);
    eassumption.
Qed.

Lemma eval_args_root_sets_union_excludes_fresh_name :
  forall env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots x,
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    roots_exclude x (root_sets_union arg_roots).
Proof.
  eapply
    (eval_args_root_sets_union_excludes_fresh_name_with_preservation_core
      eval_preserves_root_names_ready_mutual
      preservation_ready_eval_store_names_mutual);
    eassumption.
Qed.

Lemma direct_call_callee_body_root_shadow_summary_bridge_of_unique :
  forall env,
    fn_env_unique_by_name env ->
    direct_call_callee_body_root_shadow_summary_bridge env.
Proof.
  eapply
    (direct_call_callee_body_root_shadow_summary_bridge_of_unique_with_preservation_core
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall (σ : list lifetime) s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  eapply
    (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset_with_preservation_core
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall (σ : list lifetime) s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args).
Proof.
  eapply
    (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_preservation_core
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_callee_components :
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

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique :
  forall env,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_provenance_summary_evidence env ->
    forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
        (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
        used',
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args).
Proof.
  eapply
    (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique_with_preservation_core
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_direct_call_body_provenance_ready_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall σ s s_args s_body vs ret used',
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    provenance_ready_args args ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    fn_captures fdef = [] ->
    callee_body_root_provenance_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body).
Proof.
  eapply
    (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_ready :
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_preservation_ready env ->
      direct_call_callee_body_root_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  eapply
    (eval_preserves_typing_direct_call_roots_ready_with_preservation_core
      eval_preserves_typing_roots_ready_mutual
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_provenance_ready :
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_provenance_summary_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  eapply
    (eval_preserves_typing_direct_call_roots_provenance_ready_with_preservation_core
      eval_preserves_typing_roots_ready_mutual
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary :
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots fdef,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_provenance_summary env fdef ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  eapply
    (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual
      eval_preserves_frame_scope_roots_ready_mutual
      eval_preserves_typing_roots_ready_prefix_mutual
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.
