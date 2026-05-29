From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace
  TypeSafetyLocalFacts TypeSafetyRootNamed TypeSafetyBasePreservation
  TypeSafetyPrefixPreservation TypeSafetyRootPreservation
  TypeSafetyPreservationWrappers TypeSafetyClosureWrappers.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
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
            (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
               eval_preserves_typing_roots_ready_prefix_mutual)
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_direct_call_body_cleanup_final_store_eq :
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
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_remove_params (fn_params fcall) s_body = s_args.
Proof.
  intros env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ
    s s_args s_body vs ret used' T_body Γ_out R_params R_body roots_body
    Hstore Hroots Hshadow Hrn Hprov_args Hready_args Htyped_args Heval_args
    Hrename Hroots_params Hshadow_params Hrn_params Hcover_params Hprov_body
    Htyped_body Hcompat Hexclude_roots Hexclude_env Heval_body.
  destruct
    (eval_direct_call_body_cleanup_preserves_value_and_refs
      env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ
      s s_args s_body vs ret used' T_body Γ_out R_params R_body roots_body
      Hstore Hroots Hshadow Hrn Hprov_args Hready_args Htyped_args
      Heval_args Hrename Hroots_params Hshadow_params Hrn_params
      Hcover_params Hprov_body Htyped_body Hcompat Hexclude_roots
      Hexclude_env Heval_body)
    as [_ [_ [_ [_ [_ [_ [_ [_ [frame_final [locals Hcleanup]]]]]]]]]].
  destruct Hcleanup as [_ [_ [_ [_ [Heq _]]]]].
  exact Heq.
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
      (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
         eval_preserves_typing_roots_ready_prefix_mutual)
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
      (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
         eval_preserves_typing_roots_ready_prefix_mutual)
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
      (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
         eval_preserves_typing_roots_ready_prefix_mutual)
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
      (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
         eval_preserves_typing_roots_ready_prefix_mutual)
      eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.


Lemma eval_empty_closure_call_expr_components_as_direct_call :
  forall env s s_fn s_args s_body callee args fname fdef fcall vs ret used',
    eval env s callee s_fn (VClosure fname []) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_captures fdef = [] ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    eval env s_fn (ECall fname args)
      (store_remove_params (fn_params fcall) s_body) ret.
Proof.
  intros env s s_fn s_args s_body callee args fname fdef fcall vs ret
    used' _ Hlookup Hcaps Heval_args Hrename Heval_body.
  eapply Eval_Call; eassumption.
Qed.

Lemma typed_args_roots_shadow_safe_param_tys_roots :
  forall env (Ω : outlives_ctx) (n : nat) R Σ args ps_shadow Σ' R'
      roots ps,
    typed_args_roots_shadow_safe env Ω n R Σ args ps_shadow Σ' R' roots ->
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      ps_shadow ps ->
    typed_args_roots env Ω n R Σ args ps Σ' R' roots.
Proof.
  intros env Ω n R Σ args ps_shadow Σ' R' roots ps Htyped.
  revert ps.
  induction Htyped; intros ps_target Hparams.
  - inversion Hparams; subst. constructor.
  - inversion Hparams; subst.
    eapply TERArgs_Cons.
    + eapply typed_env_roots_shadow_safe_roots. exact H.
    + lazymatch goal with
      | Hparam : param_ty _ = param_ty _ |- _ =>
          rewrite <- Hparam; exact H0
      end.
    + lazymatch goal with
      | IH : forall ps_target,
          Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p) _ ps_target ->
          typed_args_roots _ _ _ _ _ _ ps_target _ _ _ |- _ =>
          eapply IH
      end; eassumption.
Qed.

Lemma params_of_tys_map_param_ty_Forall2 :
  forall ps,
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      (params_of_tys (map param_ty ps)) ps.
Proof.
  induction ps as [| p ps IH].
  - constructor.
  - simpl. constructor.
    + reflexivity.
    + exact IH.
Qed.

Lemma typed_args_roots_shadow_safe_params_of_tys_map_param_ty_roots :
  forall env (Ω : outlives_ctx) (n : nat) R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args
      (params_of_tys (map param_ty ps)) Σ' R' roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots Htyped.
  eapply typed_args_roots_shadow_safe_param_tys_roots.
  - exact Htyped.
  - apply params_of_tys_map_param_ty_Forall2.
Qed.

Inductive runtime_tfn_signature_bridge
    : list Ty -> Ty -> list Ty -> Ty -> Prop :=
  | RTSB_Refl : forall params ret,
      runtime_tfn_signature_bridge params ret params ret
  | RTSB_Compatible : forall Ω params0 ret0 params1 ret1 params2 ret2,
      runtime_tfn_signature_bridge params0 ret0 params1 ret1 ->
      Forall2 (fun expected actual => ty_compatible Ω expected actual)
        params2 params1 ->
      ty_compatible Ω ret1 ret2 ->
      runtime_tfn_signature_bridge params0 ret0 params2 ret2
  | RTSB_LifetimeEquiv : forall params0 ret0 params1 ret1 params2 ret2,
      runtime_tfn_signature_bridge params0 ret0 params1 ret1 ->
      Forall2 ty_lifetime_equiv params1 params2 ->
      ty_lifetime_equiv ret1 ret2 ->
      runtime_tfn_signature_bridge params0 ret0 params2 ret2.

Lemma runtime_tfn_signature_bridge_trans :
  forall params0 ret0 params1 ret1 params2 ret2,
    runtime_tfn_signature_bridge params0 ret0 params1 ret1 ->
    runtime_tfn_signature_bridge params1 ret1 params2 ret2 ->
    runtime_tfn_signature_bridge params0 ret0 params2 ret2.
Proof.
  intros params0 ret0 params1 ret1 params2 ret2 H01 H12.
  revert params0 ret0 H01.
  induction H12 as
    [params ret
    | Ω params1 ret1 params_mid ret_mid params2 ret2 Hmid IH Hparams Hret
    | params1 ret1 params_mid ret_mid params2 ret2 Hmid IH Hparams Hret];
    intros params_base ret_base Hbase.
  - exact Hbase.
  - eapply RTSB_Compatible.
    + apply IH. exact Hbase.
    + exact Hparams.
    + exact Hret.
  - eapply RTSB_LifetimeEquiv.
    + apply IH. exact Hbase.
    + exact Hparams.
    + exact Hret.
Qed.

Lemma ty_compatible_tfn_signature_bridge :
  forall Ω T_actual u params ret,
    ty_compatible Ω T_actual (MkTy u (TFn params ret)) ->
    exists u_actual params_actual ret_actual,
      T_actual = MkTy u_actual (TFn params_actual ret_actual) /\
      runtime_tfn_signature_bridge params_actual ret_actual params ret.
Proof.
  intros Ω [u_actual core_actual] u params ret Hcompat.
  destruct core_actual; inversion Hcompat; subst; try discriminate.
  - match goal with
    | Hcore : TFn _ _ = TFn _ _ |- _ => inversion Hcore; subst; clear Hcore
    end.
    exists u_actual, params, ret. split.
    + reflexivity.
    + apply RTSB_Refl.
  - exists u_actual, l, t. split.
    + reflexivity.
    + eapply RTSB_Compatible.
      * apply RTSB_Refl.
      * eassumption.
      * eassumption.
Qed.

Lemma ty_lifetime_equiv_tfn_signature_bridge :
  forall T_actual u params ret,
    ty_lifetime_equiv T_actual (MkTy u (TFn params ret)) ->
    exists params_actual ret_actual,
      T_actual = MkTy u (TFn params_actual ret_actual) /\
      runtime_tfn_signature_bridge params_actual ret_actual params ret.
Proof.
  intros [u_actual core_actual] u params ret Hequiv.
  destruct core_actual; inversion Hequiv; subst; try discriminate.
  exists l, t. split.
  - reflexivity.
  - eapply RTSB_LifetimeEquiv.
    + apply RTSB_Refl.
    + eassumption.
    + eassumption.
Qed.

Lemma eval_args_values_have_types_params_of_tys_compatible :
  forall env Ω_args Ω_bridge Ω_out s vs params_expected params_actual,
    Forall2 (fun expected actual => ty_compatible Ω_bridge expected actual)
      params_expected params_actual ->
    eval_args_values_have_types env Ω_args s vs (params_of_tys params_expected) ->
    eval_args_values_have_types env Ω_out s vs (params_of_tys params_actual).
Proof.
  intros env Ω_args Ω_bridge Ω_out s vs params_expected params_actual
    Hparams Hargs.
  revert vs Hargs.
  induction Hparams as [| expected actual params_expected params_actual
      Hcompat_param Hparams IH]; intros vs Hargs;
    destruct vs as [| v vs]; simpl in Hargs; inversion Hargs; subst.
  - constructor.
  - simpl. econstructor.
    + eapply VHT_Compatible.
      * eapply VHT_Compatible; eassumption.
      * exact Hcompat_param.
    + apply ty_compatible_refl_exact.
    + apply IH. exact H5.
Qed.

Lemma eval_args_values_have_types_params_of_tys_lifetime_equiv :
  forall env Ω_args Ω_out s vs params_actual params_expected,
    Forall2 ty_lifetime_equiv params_actual params_expected ->
    eval_args_values_have_types env Ω_args s vs (params_of_tys params_expected) ->
    eval_args_values_have_types env Ω_out s vs (params_of_tys params_actual).
Proof.
  intros env Ω_args Ω_out s vs params_actual params_expected Hparams Hargs.
  revert vs Hargs.
  induction Hparams as [| actual expected params_actual params_expected
      Hequiv_param Hparams IH]; intros vs Hargs;
    destruct vs as [| v vs]; simpl in Hargs; inversion Hargs; subst.
  - constructor.
  - simpl. econstructor.
    + eapply VHT_LifetimeEquiv.
      * eapply VHT_Compatible; eassumption.
      * apply ty_lifetime_equiv_sym. exact Hequiv_param.
    + apply ty_compatible_refl_exact.
    + apply IH. exact H5.
Qed.

Lemma eval_args_values_have_types_params_of_tys_outlives_any :
  forall env Ω_args Ω_out s vs params,
    eval_args_values_have_types env Ω_args s vs (params_of_tys params) ->
    eval_args_values_have_types env Ω_out s vs (params_of_tys params).
Proof.
  intros env Ω_args Ω_out s vs params Hargs.
  revert vs Hargs.
  induction params as [| T params IH]; intros vs Hargs;
    destruct vs as [| v vs]; simpl in Hargs; inversion Hargs; subst.
  - constructor.
  - simpl. econstructor.
    + eapply VHT_Compatible; eassumption.
    + apply ty_compatible_refl_exact.
    + apply IH. exact H5.
Qed.

Lemma runtime_tfn_signature_bridge_args_values :
  forall env Ω_args Ω_out s vs params_actual ret_actual params_expected
      ret_expected,
    runtime_tfn_signature_bridge params_actual ret_actual
      params_expected ret_expected ->
    eval_args_values_have_types env Ω_args s vs (params_of_tys params_expected) ->
    eval_args_values_have_types env Ω_out s vs (params_of_tys params_actual).
Proof.
  intros env Ω_args Ω_out s vs params_actual ret_actual params_expected
    ret_expected Hbridge.
  revert Ω_args Ω_out vs.
  induction Hbridge; intros Ω_args Ω_out vs Hargs.
  - eapply eval_args_values_have_types_params_of_tys_outlives_any. exact Hargs.
  - eapply IHHbridge with (Ω_args := Ω_out).
    eapply eval_args_values_have_types_params_of_tys_compatible;
      eassumption.
  - eapply IHHbridge with (Ω_args := Ω_out).
    eapply eval_args_values_have_types_params_of_tys_lifetime_equiv;
      eassumption.
Qed.

Lemma runtime_tfn_signature_bridge_result_value :
  forall env s v params_actual ret_actual params_expected ret_expected,
    runtime_tfn_signature_bridge params_actual ret_actual
      params_expected ret_expected ->
    value_has_type env s v ret_actual ->
    value_has_type env s v ret_expected.
Proof.
  intros env s v params_actual ret_actual params_expected ret_expected
    Hbridge Htyped.
  induction Hbridge.
  - exact Htyped.
  - eapply VHT_Compatible.
    + apply IHHbridge. exact Htyped.
    + eassumption.
  - eapply VHT_LifetimeEquiv.
    + apply IHHbridge. exact Htyped.
    + eassumption.
Qed.

Lemma params_of_tys_length :
  forall ts,
    List.length (params_of_tys ts) = List.length ts.
Proof.
  induction ts; simpl; auto.
Qed.

Lemma runtime_tfn_signature_bridge_params_length :
  forall params_actual ret_actual params_expected ret_expected,
    runtime_tfn_signature_bridge params_actual ret_actual
      params_expected ret_expected ->
    List.length params_actual = List.length params_expected.
Proof.
  intros params_actual ret_actual params_expected ret_expected Hbridge.
  induction Hbridge.
  - reflexivity.
  - rewrite IHHbridge.
    symmetry. eapply Forall2_length. exact H.
  - rewrite IHHbridge.
    eapply Forall2_length. exact H.
Qed.

Lemma value_has_type_empty_closure_plain_tfn_non_generic :
  forall env s fname fdef u param_tys ret,
    value_has_type env s (VClosure fname [])
      (MkTy u (TFn param_tys ret)) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_env_unique_by_name env ->
    fn_type_params fdef = 0 /\ fn_lifetimes fdef = 0.
Proof.
  intros env s fname fdef u param_tys ret Htyped.
  remember (VClosure fname []) as v eqn:Hv.
  remember (MkTy u (TFn param_tys ret)) as T eqn:HT.
  revert fname fdef u param_tys ret Hv HT.
  induction Htyped; intros fname0 fdef0 u0 param_tys0 ret0 Hv HT
      Hlookup Hunique; try discriminate.
  - inversion Hv; subst fname0.
    assert (fdef0 = fdef) as ->.
    { eapply lookup_fn_deterministic; eassumption. }
    unfold fn_value_ty, fn_signature_ty_with_usage in HT.
    destruct (fn_type_params fdef) eqn:Htype_params;
      destruct (fn_lifetimes fdef) eqn:Hlifetimes; try discriminate.
    split; reflexivity.
  - inversion Hv; subst fname0.
    pose proof
      (lookup_fn_unique_by_name env fname fdef0 fdef Hlookup H H0 Hunique)
      as Heq.
    subst fdef.
    unfold fn_value_ty, fn_signature_ty_with_usage in HT.
    destruct (fn_type_params fdef0) eqn:Htype_params;
      destruct (fn_lifetimes fdef0) eqn:Hlifetimes; try discriminate.
    split; reflexivity.
  - match goal with
    | Hcompat : ty_compatible _ _ ?Texpect,
      HTy : ?Texpect = MkTy _ (TFn _ _) |- _ => rewrite HTy in Hcompat
    | Hcompat : ty_compatible _ _ ?Texpect,
      HTy : MkTy _ (TFn _ _) = ?Texpect |- _ => rewrite <- HTy in Hcompat
    end.
    match goal with
    | Hcompat : ty_compatible ?Ωc ?Tactual (MkTy u0 (TFn param_tys0 ret0)) |- _ =>
        destruct (ty_compatible_tfn_signature_bridge Ωc Tactual u0
          param_tys0 ret0 Hcompat)
          as [u_actual [params_actual [ret_actual [HTactual _]]]]
    end.
    subst T_actual.
    eapply IHHtyped; eauto.
  - match goal with
    | Hequiv : ty_lifetime_equiv _ ?Texpect,
      HTy : ?Texpect = MkTy _ (TFn _ _) |- _ => rewrite HTy in Hequiv
    | Hequiv : ty_lifetime_equiv _ ?Texpect,
      HTy : MkTy _ (TFn _ _) = ?Texpect |- _ => rewrite <- HTy in Hequiv
    end.
    match goal with
    | Hequiv : ty_lifetime_equiv ?Tactual (MkTy u0 (TFn param_tys0 ret0)) |- _ =>
        destruct (ty_lifetime_equiv_tfn_signature_bridge Tactual u0
          param_tys0 ret0 Hequiv)
          as [params_actual [ret_actual [HTactual _]]]
    end.
    subst T_actual.
    eapply IHHtyped; eauto.
Qed.

Lemma value_has_type_empty_closure_tfn_signature_bridge :
  forall env s fname fdef u param_tys ret,
    value_has_type env s (VClosure fname [])
      (MkTy u (TFn param_tys ret)) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_env_unique_by_name env ->
    fn_type_params fdef = 0 ->
    fn_lifetimes fdef = 0 ->
    runtime_tfn_signature_bridge
      (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret.
Proof.
  intros env s fname fdef u param_tys ret Htyped.
  remember (VClosure fname []) as v eqn:Hv.
  remember (MkTy u (TFn param_tys ret)) as T eqn:HT.
  revert fname fdef u param_tys ret Hv HT.
  induction Htyped; intros fname0 fdef0 u0 param_tys0 ret0 Hv HT
      Hlookup Hunique Htype_params Hlifetimes; try discriminate.
  - inversion Hv; subst fname0.
    rewrite H in Hlookup. inversion Hlookup; subst fdef0.
    unfold fn_value_ty, fn_signature_ty_with_usage in HT.
    rewrite Htype_params in HT. rewrite Hlifetimes in HT.
    simpl in HT.
    rewrite map_lifetimes_tys_close_fn_lifetime_0 in HT.
    rewrite map_lifetimes_ty_close_fn_lifetime_0 in HT.
    inversion HT; subst. apply RTSB_Refl.
  - inversion Hv; subst fname0.
    pose proof
      (lookup_fn_unique_by_name env fname fdef0 fdef Hlookup H H0 Hunique)
      as Heq.
    subst fdef.
    unfold fn_value_ty, fn_signature_ty_with_usage in HT.
    rewrite Htype_params in HT. rewrite Hlifetimes in HT.
    simpl in HT.
    rewrite map_lifetimes_tys_close_fn_lifetime_0 in HT.
    rewrite map_lifetimes_ty_close_fn_lifetime_0 in HT.
    inversion HT; subst. apply RTSB_Refl.
  - match goal with
    | Hcompat : ty_compatible _ _ ?Texpect,
      HTy : ?Texpect = MkTy _ (TFn _ _) |- _ => rewrite HTy in Hcompat
    | Hcompat : ty_compatible _ _ ?Texpect,
      HTy : MkTy _ (TFn _ _) = ?Texpect |- _ => rewrite <- HTy in Hcompat
    end.
    match goal with
    | Hcompat : ty_compatible ?Ωc ?Tactual (MkTy u0 (TFn param_tys0 ret0)) |- _ =>
        destruct (ty_compatible_tfn_signature_bridge Ωc Tactual u0
          param_tys0 ret0 Hcompat)
          as [u_actual [params_actual [ret_actual [HTactual Hstep]]]]
    end.
    subst T_actual.
    eapply runtime_tfn_signature_bridge_trans.
    + eapply IHHtyped; eauto.
    + exact Hstep.
  - match goal with
    | Hequiv : ty_lifetime_equiv _ ?Texpect,
      HTy : ?Texpect = MkTy _ (TFn _ _) |- _ => rewrite HTy in Hequiv
    | Hequiv : ty_lifetime_equiv _ ?Texpect,
      HTy : MkTy _ (TFn _ _) = ?Texpect |- _ => rewrite <- HTy in Hequiv
    end.
    match goal with
    | Hequiv : ty_lifetime_equiv ?Tactual (MkTy u0 (TFn param_tys0 ret0)) |- _ =>
        destruct (ty_lifetime_equiv_tfn_signature_bridge Tactual u0
          param_tys0 ret0 Hequiv)
          as [params_actual [ret_actual [HTactual Hstep]]]
    end.
    subst T_actual.
    eapply runtime_tfn_signature_bridge_trans.
    + eapply IHHtyped; eauto.
    + exact Hstep.
Qed.

Lemma ty_lifetime_equiv_map_lifetimes_ty :
  forall f T,
    ty_lifetime_equiv T (map_lifetimes_ty f T).
Proof.
  fix IH 2.
  intros f [u core].
  destruct core as [| | | | s | i | name lts args | name lts args
                   | params ret | env_lt params ret | n Ω body
                   | n bounds body | lt rk body]; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply TLE_Struct.
    induction args as [| T Ts IHTs]; simpl; constructor; auto.
  - apply TLE_Enum.
    induction args as [| T Ts IHTs]; simpl; constructor; auto.
  - apply TLE_Fn.
    + induction params as [| T Ts IHTs]; simpl; constructor; auto.
    + apply IH.
  - apply TLE_Closure.
    + induction params as [| T Ts IHTs]; simpl; constructor; auto.
    + apply IH.
  - apply TLE_Forall. apply IH.
  - apply TLE_TypeForall. apply IH.
  - apply TLE_Ref. apply IH.
Qed.

Lemma ty_lifetime_equiv_map_lifetimes_tys :
  forall f ts,
    Forall2 ty_lifetime_equiv ts (map (map_lifetimes_ty f) ts).
Proof.
  intros f ts.
  induction ts; simpl; constructor; auto.
  apply ty_lifetime_equiv_map_lifetimes_ty.
Qed.

Lemma ty_lifetime_equiv_map_lifetimes_tys_go :
  forall f ts,
    Forall2 ty_lifetime_equiv ts
      ((fix go (xs : list Ty) : list Ty :=
          match xs with
          | [] => []
          | x :: xs' => map_lifetimes_ty f x :: go xs'
          end) ts).
Proof.
  intros f ts.
  induction ts as [| T Ts IHTs]; simpl; constructor; auto.
  apply ty_lifetime_equiv_map_lifetimes_ty.
Qed.

Lemma Forall2_ty_lifetime_equiv_map_lifetimes_tys_sym :
  forall f ts,
    Forall2 ty_lifetime_equiv (map (map_lifetimes_ty f) ts) ts.
Proof.
  intros f ts.
  induction ts as [| T Ts IHTs]; simpl; constructor; auto.
  apply ty_lifetime_equiv_sym.
  apply ty_lifetime_equiv_map_lifetimes_ty.
Qed.

Lemma runtime_tfn_signature_bridge_open_bound_rhs :
  forall sigma params0 ret0 params1 ret1,
    runtime_tfn_signature_bridge params0 ret0 params1 ret1 ->
    runtime_tfn_signature_bridge params0 ret0
      (map (open_bound_ty sigma) params1) (open_bound_ty sigma ret1).
Proof.
  intros sigma params0 ret0 params1 ret1 Hbridge.
  eapply runtime_tfn_signature_bridge_trans.
  - exact Hbridge.
  - eapply RTSB_LifetimeEquiv.
    + apply RTSB_Refl.
    + unfold open_bound_ty. apply ty_lifetime_equiv_map_lifetimes_tys.
    + unfold open_bound_ty. apply ty_lifetime_equiv_map_lifetimes_ty.
Qed.

Lemma runtime_tfn_signature_bridge_open_bound_both :
  forall sigma params0 ret0 params1 ret1,
    runtime_tfn_signature_bridge params0 ret0 params1 ret1 ->
    runtime_tfn_signature_bridge
      (map (open_bound_ty sigma) params0) (open_bound_ty sigma ret0)
      (map (open_bound_ty sigma) params1) (open_bound_ty sigma ret1).
Proof.
  intros sigma params0 ret0 params1 ret1 Hbridge.
  eapply runtime_tfn_signature_bridge_trans.
  - eapply RTSB_LifetimeEquiv.
    + apply RTSB_Refl.
    + unfold open_bound_ty.
      apply Forall2_ty_lifetime_equiv_map_lifetimes_tys_sym.
    + unfold open_bound_ty.
      apply ty_lifetime_equiv_sym.
      apply ty_lifetime_equiv_map_lifetimes_ty.
  - eapply runtime_tfn_signature_bridge_open_bound_rhs.
    exact Hbridge.
Qed.

Lemma value_has_type_empty_closure_lookup_captures_for_tforall :
  forall env s fname fdef T,
    value_has_type env s (VClosure fname []) T ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_env_unique_by_name env ->
    fn_captures fdef = [].
Proof.
  intros env s fname fdef T Htyped.
  remember (VClosure fname []) as v eqn:Hv.
  revert fname fdef Hv.
  induction Htyped; intros fname0 fdef0 Hv Hlookup Hunique; try discriminate.
  - inversion Hv; subst fname0.
    assert (fdef0 = fdef) as -> by (eapply lookup_fn_deterministic; eassumption).
    exact H0.
  - inversion Hv; subst fname0.
    pose proof
      (lookup_fn_unique_by_name env fname fdef0 fdef Hlookup H H0 Hunique)
      as Heq.
    subst fdef.
    exact H1.
  - eapply IHHtyped; eauto.
  - eapply IHHtyped; eauto.
Qed.

Lemma value_has_type_empty_closure_tforall_tfn_components :
  forall env s fname fdef u m bounds body param_tys ret sigma,
    value_has_type env s (VClosure fname [])
      (MkTy u (TForall m bounds body)) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_env_unique_by_name env ->
    ty_core body = TFn param_tys ret ->
    fn_type_params fdef = 0 /\
    fn_captures fdef = [] /\
    runtime_tfn_signature_bridge
      (map param_ty (fn_params fdef)) (fn_ret fdef)
      (map (open_bound_ty sigma) param_tys) (open_bound_ty sigma ret).
Proof.
  intros env s fname fdef u m bounds body param_tys ret sigma Htyped.
  remember (VClosure fname []) as v eqn:Hv.
  remember (MkTy u (TForall m bounds body)) as T eqn:HT.
  revert fname fdef u m bounds body param_tys ret sigma Hv HT.
  induction Htyped; intros fname0 fdef0 u0 m0 bounds0 body0 param_tys0 ret0 sigma0
      Hv HT Hlookup Hunique Hbody; try discriminate.
  - inversion Hv; subst fname0.
    assert (fdef0 = fdef) as -> by (eapply lookup_fn_deterministic; eassumption).
    unfold fn_value_ty, fn_signature_ty_with_usage in HT.
    destruct (fn_type_params fdef) eqn:Htype_params.
    2: { simpl in HT.
         destruct (fn_lifetimes fdef); inversion HT; subst;
           simpl in Hbody; discriminate. }
    destruct (fn_lifetimes fdef) eqn:Hlifetimes; try discriminate.
    simpl in HT. inversion HT; subst.
    unfold close_fn_ty in Hbody. simpl in Hbody. inversion Hbody; subst.
    split; [reflexivity|].
    split; [exact H0|].
    eapply RTSB_LifetimeEquiv;
      [ apply RTSB_Refl
      | eapply Forall2_ty_lifetime_equiv_trans with
          (ys := ((fix go (xs : list Ty) : list Ty :=
                     match xs with
                     | [] => []
                     | x :: xs' => map_lifetimes_ty (close_fn_lifetime (S n)) x :: go xs'
                     end) (map param_ty (fn_params fdef))));
        [ apply ty_lifetime_equiv_map_lifetimes_tys_go
        | unfold open_bound_ty; apply ty_lifetime_equiv_map_lifetimes_tys ]
      | eapply ty_lifetime_equiv_trans with
          (T2 := map_lifetimes_ty (close_fn_lifetime (S n)) (fn_ret fdef));
        [ apply ty_lifetime_equiv_map_lifetimes_ty
        | unfold open_bound_ty; apply ty_lifetime_equiv_map_lifetimes_ty ] ].
  - inversion Hv; subst fname0.
    pose proof (lookup_fn_unique_by_name env fname fdef0 fdef Hlookup H H0 Hunique) as Heq.
    subst fdef.
    unfold fn_value_ty, fn_signature_ty_with_usage in HT.
    destruct (fn_type_params fdef0) eqn:Htype_params.
    2: { simpl in HT.
         destruct (fn_lifetimes fdef0); inversion HT; subst;
           simpl in Hbody; discriminate. }
    destruct (fn_lifetimes fdef0) eqn:Hlifetimes; try discriminate.
    simpl in HT. inversion HT; subst.
    unfold close_fn_ty in Hbody. simpl in Hbody. inversion Hbody; subst.
    split; [reflexivity|].
    split; [exact H1|].
    eapply RTSB_LifetimeEquiv;
      [ apply RTSB_Refl
      | eapply Forall2_ty_lifetime_equiv_trans with
          (ys := ((fix go (xs : list Ty) : list Ty :=
                     match xs with
                     | [] => []
                     | x :: xs' => map_lifetimes_ty (close_fn_lifetime (S n)) x :: go xs'
                     end) (map param_ty (fn_params fdef0))));
        [ apply ty_lifetime_equiv_map_lifetimes_tys_go
        | unfold open_bound_ty; apply ty_lifetime_equiv_map_lifetimes_tys ]
      | eapply ty_lifetime_equiv_trans with
          (T2 := map_lifetimes_ty (close_fn_lifetime (S n)) (fn_ret fdef0));
        [ apply ty_lifetime_equiv_map_lifetimes_ty
        | unfold open_bound_ty; apply ty_lifetime_equiv_map_lifetimes_ty ] ].
  - match goal with
    | Hcompat : ty_compatible _ _ ?Texpect,
      HTy : ?Texpect = MkTy _ (TForall _ _ _) |- _ => rewrite HTy in Hcompat
    | Hcompat : ty_compatible _ _ ?Texpect,
      HTy : MkTy _ (TForall _ _ _) = ?Texpect |- _ => rewrite <- HTy in Hcompat
    end.
    inversion H; subst; try discriminate.
    + destruct body0 as [u_body core_body].
      simpl in Hbody. rewrite Hbody in *.
      destruct (IHHtyped fname0 fdef0 _ _ _
        (MkTy u_body (TFn param_tys0 ret0))
        param_tys0 ret0 sigma0 eq_refl eq_refl Hlookup Hunique eq_refl)
        as [Htype_params [Hcaptures Hbridge]].
      repeat split; try exact Htype_params; try exact Hcaptures.
      exact Hbridge.
    + destruct body0 as [u_body core_body].
      simpl in Hbody. rewrite Hbody in *.
      match goal with
      | Hcompat_body : ty_compatible ?Ωc ?Tbody_actual
          (MkTy u_body (TFn param_tys0 ret0)) |- _ =>
          destruct (ty_compatible_tfn_signature_bridge Ωc Tbody_actual
            u_body param_tys0 ret0 Hcompat_body)
            as [u_actual [params_actual [ret_actual [HTbody_actual Hstep]]]]
      end.
      subst.
      destruct (IHHtyped fname0 fdef0 _ _ _
        (MkTy u_actual (TFn params_actual ret_actual))
        params_actual ret_actual sigma0 eq_refl eq_refl Hlookup Hunique eq_refl)
        as [Htype_params [Hcaptures Hbridge]].
      repeat split; try exact Htype_params; try exact Hcaptures.
      eapply runtime_tfn_signature_bridge_trans.
      * exact Hbridge.
      * eapply runtime_tfn_signature_bridge_open_bound_both.
        exact Hstep.
    + destruct body0 as [u_body core_body].
      simpl in Hbody. rewrite Hbody in *.
      match goal with
      | Hcompat_body : ty_compatible ?Ωc ?Tbody_actual
          (MkTy u_body (TFn param_tys0 ret0)) |- _ =>
          destruct (ty_compatible_tfn_signature_bridge Ωc Tbody_actual
            u_body param_tys0 ret0 Hcompat_body)
            as [u_actual [params_actual [ret_actual [HTbody_actual Hstep]]]]
      end.
      inversion HTbody_actual; subst; clear HTbody_actual.
      destruct (value_has_type_empty_closure_plain_tfn_non_generic
        env s fname0 fdef0 u_actual params_actual ret_actual Htyped
        Hlookup Hunique) as [Htype_params Hlifetimes].
      repeat split.
      * exact Htype_params.
      * eapply value_has_type_empty_closure_lookup_captures_for_tforall;
          eassumption.
      * eapply runtime_tfn_signature_bridge_trans.
        -- eapply value_has_type_empty_closure_tfn_signature_bridge;
             eassumption.
        -- eapply runtime_tfn_signature_bridge_open_bound_rhs.
           exact Hstep.
  - match goal with
    | Hequiv : ty_lifetime_equiv _ ?Texpect,
      HTy : ?Texpect = MkTy _ (TForall _ _ _) |- _ => rewrite HTy in Hequiv
    | Hequiv : ty_lifetime_equiv _ ?Texpect,
      HTy : MkTy _ (TForall _ _ _) = ?Texpect |- _ => rewrite <- HTy in Hequiv
    end.
    inversion H; subst; try discriminate.
    destruct body0 as [u_body core_body].
    simpl in Hbody. rewrite Hbody in *.
    match goal with
    | Hequiv_body : ty_lifetime_equiv ?Tbody_actual
        (MkTy u_body (TFn param_tys0 ret0)) |- _ =>
        destruct (ty_lifetime_equiv_tfn_signature_bridge Tbody_actual
          u_body param_tys0 ret0 Hequiv_body)
          as [params_actual [ret_actual [HTbody_actual Hstep]]]
    end.
    subst.
    destruct (IHHtyped fname0 fdef0 _ _ _
      (MkTy u_body (TFn params_actual ret_actual))
      params_actual ret_actual sigma0 eq_refl eq_refl Hlookup Hunique eq_refl)
      as [Htype_params [Hcaptures Hbridge]].
    repeat split; try exact Htype_params; try exact Hcaptures.
    eapply runtime_tfn_signature_bridge_trans.
    + exact Hbridge.
    + eapply runtime_tfn_signature_bridge_open_bound_both.
      exact Hstep.
Qed.

Lemma value_has_type_empty_closure_lookup_captures :
  forall env s fname fdef T,
    value_has_type env s (VClosure fname []) T ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_env_unique_by_name env ->
    fn_captures fdef = [].
Proof.
  intros env s fname fdef T Htyped.
  remember (VClosure fname []) as v eqn:Hv.
  revert fname fdef Hv.
  induction Htyped; intros fname0 fdef0 Hv Hlookup Hunique;
    try discriminate.
  - inversion Hv; subst fname0.
    assert (fdef0 = fdef) as ->.
    { eapply lookup_fn_deterministic; eassumption. }
    exact H0.
  - inversion Hv; subst fname0.
    pose proof
      (lookup_fn_unique_by_name env fname fdef0 fdef Hlookup H H0 Hunique)
      as Heq.
    subst fdef.
    exact H1.
  - eapply IHHtyped; eauto.
  - eapply IHHtyped; eauto.
Qed.

Lemma value_has_type_empty_closure_tfn_components :
  forall env s fname fdef u param_tys ret,
    value_has_type env s (VClosure fname [])
      (MkTy u (TFn param_tys ret)) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_env_unique_by_name env ->
    fn_type_params fdef = 0 ->
    fn_lifetimes fdef = 0 ->
    fn_captures fdef = [] /\
    runtime_tfn_signature_bridge
      (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret.
Proof.
  intros env s fname fdef u param_tys ret Htyped Hlookup Hunique
    Htype_params Hlifetimes.
  split.
  - eapply value_has_type_empty_closure_lookup_captures; eassumption.
  - eapply value_has_type_empty_closure_tfn_signature_bridge;
      eassumption.
Qed.

Lemma eval_args_values_have_types_params_of_tys_map_param_ty :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs
      (params_of_tys (map param_ty ps)) ->
    eval_args_values_have_types env Ω s vs ps.
Proof.
  intros env Ω s vs ps.
  revert vs.
  induction ps as [| p ps IH]; intros vs Hargs;
    destruct vs as [| v vs]; simpl in Hargs; inversion Hargs; subst.
  - constructor.
  - simpl. econstructor.
    + eapply VHT_Compatible; eassumption.
    + apply ty_compatible_refl_exact.
    + apply IH. exact H5.
Qed.

Lemma typed_empty_closure_call_expr_tfn_components_direct_call_roots :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ1 R1 Σ' R'
      callee args fname fdef u roots_callee arg_roots,
    typed_env_roots_shadow_safe env Ω n R Σ callee
      (MkTy u (TFn (map param_ty (fn_params fdef)) (fn_ret fdef)))
      Σ1 R1 roots_callee ->
    typed_args_roots_shadow_safe env Ω n R1 Σ1 args
      (params_of_tys (map param_ty (fn_params fdef))) Σ' R' arg_roots ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_captures fdef = [] ->
    fn_type_params fdef = 0 ->
    Forall (fun '(a, b) => outlives Ω a b) (fn_outlives fdef) ->
    typed_env_roots env Ω n R1 Σ1 (ECall fname args)
      (fn_ret fdef) Σ' R' (root_sets_union arg_roots).
Proof.
  intros env Ω n R Σ Σ1 R1 Σ' R' callee args fname fdef u
    roots_callee arg_roots _ Htyped_args Hlookup Hcaps Htype_params
    Houtlives.
  destruct (lookup_fn_in_name_readiness fname (env_fns env) fdef Hlookup)
    as [Hin Hname].
  rewrite <- (apply_lt_ty_nil_ts (fn_ret fdef)).
  eapply TER_Call with (fdef := fdef) (σ := []).
  - exact Hin.
  - exact Hname.
  - exact Hcaps.
  - exact Htype_params.
  - rewrite apply_lt_params_nil_ts.
    eapply typed_args_roots_shadow_safe_params_of_tys_map_param_ty_roots.
    exact Htyped_args.
  - rewrite apply_lt_outlives_nil_ts.
    exact Houtlives.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Sigma ->
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
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Gamma_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (params_of_tys param_tys) Sigma_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply
      (eval_args_root_tail_fresh_names_for_fresh_call_with_preservation_core
        eval_preserves_root_names_ready_mutual
        eval_preserves_root_keys_named_ready_mutual);
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - eapply
        (eval_args_root_names_excludes_params_ready_with_preservation_core
          eval_preserves_root_names_ready_mutual);
        eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite Hbounds;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.

Theorem eval_empty_closure_call_expr_tfn_components_preserve_typing_with_callee_summary :
  forall env s s_fn s_args s_body callee fname args fdef fcall vs ret used',
    eval env s callee s_fn (VClosure fname []) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_captures fdef = [] ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma Sigma1 R1 Sigma' R'
        callee_roots arg_roots u fsummary,
      typed_env_roots_shadow_safe env Omega n R Sigma callee
        (MkTy u (TFn (map param_ty (fn_params fdef)) (fn_ret fdef)))
        Sigma1 R1 callee_roots ->
      typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
        (params_of_tys (map param_ty (fn_params fdef)))
        Sigma' R' arg_roots ->
      fn_type_params fdef = 0 ->
      Forall (fun '(a, b) => outlives Omega a b) (fn_outlives fdef) ->
      preservation_ready_args args ->
      store_typed env s_fn Sigma1 ->
      store_roots_within R1 s_fn ->
      store_no_shadow s_fn ->
      root_env_no_shadow R1 ->
      root_env_store_roots_named R1 s_fn ->
      root_env_store_keys_named R1 s_fn ->
      fn_env_unique_by_name env ->
      In fsummary (env_fns env) ->
      fn_name fsummary = fname ->
      callee_body_root_shadow_provenance_summary env fsummary ->
      store_typed env (store_remove_params (fn_params fcall) s_body) Sigma' /\
      value_has_type env (store_remove_params (fn_params fcall) s_body)
        ret (fn_ret fdef) /\
      store_ref_targets_preserved env s_fn
        (store_remove_params (fn_params fcall) s_body) /\
      store_roots_within R'
        (store_remove_params (fn_params fcall) s_body) /\
      value_roots_within (root_sets_union arg_roots) ret /\
      store_no_shadow (store_remove_params (fn_params fcall) s_body) /\
      root_env_no_shadow R'.
Proof.
  intros env s s_fn s_args s_body callee fname args fdef fcall vs ret
    used' Heval_callee Hlookup Hcaps Heval_args Hrename Heval_body Omega n R
    Sigma Sigma1 R1 Sigma' R' callee_roots arg_roots u fsummary
    Htyped_callee Htyped_args Htype_params Houtlives Hready_args Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hunique Hin_summary Hfname_summary
    Hcallee_summary.
  pose proof
    (typed_empty_closure_call_expr_tfn_components_direct_call_roots
      env Omega n R Sigma Sigma1 R1 Sigma' R' callee args fname fdef u
      callee_roots arg_roots Htyped_callee Htyped_args Hlookup Hcaps
      Htype_params Houtlives)
    as Htyped_call.
  pose proof
    (eval_empty_closure_call_expr_components_as_direct_call
      env s s_fn s_args s_body callee args fname fdef fcall vs ret used'
      Heval_callee Hlookup Hcaps Heval_args Hrename Heval_body)
    as Heval_call.
  eapply eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary;
    eassumption.
Qed.

Theorem eval_call_expr_tfn_components_preserve_typing_with_callee_summary_route :
  forall env s s_fn s_args s_body callee args fname captured fdef fcall
      vs ret_value used',
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret_value ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma Sigma1 R1 Sigma' R'
        callee_roots arg_roots u param_tys ret_ty,
      preservation_ready_args args ->
      provenance_ready_expr callee ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots_shadow_safe env Omega n R Sigma callee
        (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 callee_roots ->
      typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
        (params_of_tys param_tys) Sigma' R' arg_roots ->
      fn_env_unique_by_name env ->
      fn_type_params fdef = 0 ->
      fn_lifetimes fdef = 0 ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots) ->
      let s_final :=
        store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body) in
      store_typed env s_final Sigma' /\
      value_has_type env s_final ret_value ret_ty /\
      store_ref_targets_preserved env s s_final /\
      store_roots_within R' s_final /\
      value_roots_within
        (root_set_union callee_roots (root_sets_union arg_roots))
        ret_value /\
      store_no_shadow s_final /\
      root_env_no_shadow R'.
Proof.
  intros env s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret_value used' Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' callee_roots arg_roots u
    param_tys ret_ty Hready_args Hprov_callee Hstore Hroots Hshadow Hrn
    Htyped_callee_shadow Htyped_args_shadow Hunique Htype_params
    Hlifetimes Hcallee_route s_final.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma callee (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 callee_roots Htyped_callee_shadow) as Htyped_callee.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
              env s callee s_fn (VClosure fname captured) Heval_callee
              Omega n R Sigma (MkTy u (TFn param_tys ret_ty))
              Sigma1 R1 callee_roots Hprov_callee Hstore Hroots Hshadow
              Hrn Htyped_callee)
    as [Hstore_fn [Hv_callee [Hpres_callee
        [Hroots_fn [Hv_callee_roots [Hshadow_fn Hrn_fn]]]]]].
  pose proof
    (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured.
  subst captured.
  simpl in Hrename, Heval_body.
  destruct
    (value_has_type_empty_closure_tfn_components
      env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique
      Htype_params Hlifetimes)
    as [Hcaps_fdef Hbridge].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args_shadow) as Htyped_args.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_mutual)
              env s_fn args s_args vs Heval_args Omega n R1 Sigma1
              (params_of_tys param_tys) Sigma' R' arg_roots Hprov_args
              Hstore_fn Hroots_fn Hshadow_fn Hrn_fn Htyped_args)
    as [Hstore_args [Hargs_expected [Hpres_args
        [Hroots_args [_ [Hshadow_args Hrn_args]]]]]].
  assert (Hargs_fdef_tys :
    eval_args_values_have_types env Omega s_args vs
      (params_of_tys (map param_ty (fn_params fdef)))).
  { eapply runtime_tfn_signature_bridge_args_values.
    - exact Hbridge.
    - exact Hargs_expected. }
  assert (Hargs_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_params_of_tys_map_param_ty.
    exact Hargs_fdef_tys. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s_fn args s_args vs Omega n R1 Sigma1
              (params_of_tys param_tys) Sigma' R' arg_roots
              (fn_params fcall) Heval_args Hprov_args Htyped_args
              Hroots_fn Hshadow_fn Hrn_fn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
               (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps_fdef. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset
    in Hcallee_route.
  destruct Hcallee_route
    as (T_body & Gamma_out & R_body & roots_body &
        Hprov_body & Htyped_body_shadow & Hcompat_body &
        Hexclude_roots & Hexclude_env & Hresult_subset).
  pose proof (typed_env_roots_shadow_safe_roots
    (global_env_with_local_bounds env (fn_bounds fcall))
    (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R')
    (sctx_of_ctx (fn_body_ctx fcall))
    (fn_body fcall) T_body (sctx_of_ctx Gamma_out) R_body roots_body
    Htyped_body_shadow) as Htyped_body_ctx.
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R')
      fcall (fn_body fcall) T_body (sctx_of_ctx Gamma_out) R_body
      roots_body Hcaps_call Htyped_body_ctx) as Htyped_body.
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret_value).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_fcall. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh
      (sctx_of_ctx (params_ctx (fn_params fcall))) s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
              body_env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret_value Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R')
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body
              Hcover_params Hroots_bind Hshadow_bind Hrn_params
              Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  pose proof (proj1 eval_preserves_typing_roots_ready_prefix_mutual
                body_env (bind_params (fn_params fcall) vs s_args)
                (fn_body fcall) s_body ret_value Heval_body_body_env
                (fn_outlives fcall) (fn_lifetimes fcall)
                (call_param_root_env (fn_params fcall) arg_roots R')
                (sctx_of_ctx (params_ctx (fn_params fcall)))
                T_body (sctx_of_ctx Gamma_out) R_body roots_body
                Hprov_body Hstore_bind_body_env Hroots_bind Hshadow_bind
                Hrn_params Htyped_body) as Hbody_package.
  destruct Hbody_package as [Hstore_body [Hv_body [Hpres_body
    [Hroots_body [Hret_roots [Hshadow_body Hrn_body]]]]]].
  assert (Hstore_body_env :
    store_typed_prefix env s_body (sctx_of_ctx Gamma_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret_value T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
              body_env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret_value Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R')
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body
              Hcover_params)
    as [frame_final Hscope_body].
  { eapply store_param_scope_bind_params. exact Hargs_fcall. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  destruct
    (eval_direct_call_body_cleanup_preserves_value_and_refs_core
      env Omega s_fn s_args Sigma' fdef fcall [] s_body vs ret_value
      used' T_body Gamma_out R_body roots_body frame_final Hstore_args
      Hpres_args Hrename Hargs_fcall Hframe_scope Hscope_body
      Hstore_body_env Hv_body_env Hpres_body_env Hroots_body Hret_roots
      Hshadow_body Hrn_body Hsame_body Hcompat_body Hexclude_roots
      Hexclude_env)
    as [Hstore_final Hcleanup].
  destruct Hcleanup as [Hprefix_cleanup Hcleanup].
    destruct Hcleanup as [Hroots_cleanup Hcleanup].
    destruct Hcleanup as [Hshadow_cleanup Hcleanup].
    destruct Hcleanup as [Hrn_cleanup Hcleanup].
    destruct Hcleanup as [Hv_fdef Hcleanup].
    destruct Hcleanup as [Hpres_final [locals Hcleanup]].
    destruct Hcleanup as [Hremoved [Hret_exclude
      [Hstore_exclude [Hremoved_exact Hret_roots_body]]]].
    subst s_final.
    rewrite Hcaps_call. simpl.
    rewrite Hremoved_exact.
    repeat split.
    + exact Hstore_args.
    + rewrite <- Hremoved_exact.
      eapply runtime_tfn_signature_bridge_result_value.
      * exact Hbridge.
      * rewrite <- (apply_lt_ty_nil_ts (fn_ret fdef)). exact Hv_fdef.
    + rewrite <- Hremoved_exact.
      eapply store_ref_targets_preserved_trans.
      * exact Hpres_callee.
      * exact Hpres_final.
    + exact Hroots_args.
    + apply value_roots_within_union_r.
      eapply direct_call_value_roots_within_store_subset; eassumption.
    + exact Hshadow_args.
    + exact Hrn_args.
Qed.


Theorem eval_evar_call_expr_lifetime_forall_tfn_components_preserve_typing_with_callee_summary_route :
  forall env s s_fn s_args s_body x args fname captured fdef fcall
      vs ret_value used',
    eval env s (EVar x) s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret_value ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma Sigma1 R1 Sigma' R'
        callee_roots arg_roots u m bounds body param_tys ret_ty sigma,
      preservation_ready_args args ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
        (MkTy u (TForall m bounds body)) Sigma1 R1 callee_roots ->
      ty_core body = TFn param_tys ret_ty ->
      typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys))
        Sigma' R' arg_roots ->
      fn_type_params fdef = 0 ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef)
        (map (open_bound_ty sigma) param_tys) (open_bound_ty sigma ret_ty) ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots) ->
      let s_final :=
        store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body) in
      store_typed env s_final Sigma' /\
      value_has_type env s_final ret_value (open_bound_ty sigma ret_ty) /\
      store_ref_targets_preserved env s s_final /\
      store_roots_within R' s_final /\
      value_roots_within
        (root_set_union callee_roots (root_sets_union arg_roots))
        ret_value /\
      store_no_shadow s_final /\
      root_env_no_shadow R'.
Proof.
  intros env s s_fn s_args s_body x args fname captured fdef fcall
    vs ret_value used' Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' callee_roots arg_roots u
    m bounds body param_tys ret_ty sigma Hready_args Hstore Hroots Hshadow
    Hrn Htyped_callee_shadow _ Htyped_args_shadow Htype_params Hcaps_fdef
    Hbridge Hcallee_route s_final.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body))
    Sigma1 R1 callee_roots Htyped_callee_shadow) as Htyped_callee.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
              env s (EVar x) s_fn (VClosure fname captured) Heval_callee
              Omega n R Sigma (MkTy u (TForall m bounds body))
              Sigma1 R1 callee_roots (ProvReady_Var x) Hstore Hroots Hshadow
              Hrn Htyped_callee)
    as [Hstore_fn [Hv_callee [Hpres_callee
        [Hroots_fn [Hv_callee_roots [Hshadow_fn Hrn_fn]]]]]].
  pose proof
    (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TForall m bounds body)) Hv_callee) as Hcaptured.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args_shadow) as Htyped_args.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_mutual)
              env s_fn args s_args vs Heval_args Omega n R1 Sigma1
              (params_of_tys (map (open_bound_ty sigma) param_tys))
              Sigma' R' arg_roots Hprov_args Hstore_fn Hroots_fn
              Hshadow_fn Hrn_fn Htyped_args)
    as [Hstore_args [Hargs_expected [Hpres_args
        [Hroots_args [_ [Hshadow_args Hrn_args]]]]]].
  assert (Hargs_fdef_tys :
    eval_args_values_have_types env Omega s_args vs
      (params_of_tys (map param_ty (fn_params fdef)))).
  { eapply runtime_tfn_signature_bridge_args_values.
    - exact Hbridge.
    - exact Hargs_expected. }
  assert (Hargs_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_params_of_tys_map_param_ty.
    exact Hargs_fdef_tys. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s_fn args s_args vs Omega n R1 Sigma1
              (params_of_tys (map (open_bound_ty sigma) param_tys))
              Sigma' R' arg_roots
              (fn_params fcall) Heval_args Hprov_args Htyped_args
              Hroots_fn Hshadow_fn Hrn_fn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
               (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps_fdef. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset
    in Hcallee_route.
  destruct Hcallee_route
    as (T_body & Gamma_out & R_body & roots_body &
        Hprov_body & Htyped_body_shadow & Hcompat_body &
        Hexclude_roots & Hexclude_env & Hresult_subset).
  pose proof (typed_env_roots_shadow_safe_roots
    (global_env_with_local_bounds env (fn_bounds fcall))
    (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R')
    (sctx_of_ctx (fn_body_ctx fcall))
    (fn_body fcall) T_body (sctx_of_ctx Gamma_out) R_body roots_body
    Htyped_body_shadow) as Htyped_body_ctx.
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R')
      fcall (fn_body fcall) T_body (sctx_of_ctx Gamma_out) R_body
      roots_body Hcaps_call Htyped_body_ctx) as Htyped_body.
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret_value).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_fcall. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh
      (sctx_of_ctx (params_ctx (fn_params fcall))) s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
              body_env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret_value Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R')
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body
              Hcover_params Hroots_bind Hshadow_bind Hrn_params
              Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  pose proof (proj1 eval_preserves_typing_roots_ready_prefix_mutual
                body_env (bind_params (fn_params fcall) vs s_args)
                (fn_body fcall) s_body ret_value Heval_body_body_env
                (fn_outlives fcall) (fn_lifetimes fcall)
                (call_param_root_env (fn_params fcall) arg_roots R')
                (sctx_of_ctx (params_ctx (fn_params fcall)))
                T_body (sctx_of_ctx Gamma_out) R_body roots_body
                Hprov_body Hstore_bind_body_env Hroots_bind Hshadow_bind
                Hrn_params Htyped_body) as Hbody_package.
  destruct Hbody_package as [Hstore_body [Hv_body [Hpres_body
    [Hroots_body [Hret_roots [Hshadow_body Hrn_body]]]]]].
  assert (Hstore_body_env :
    store_typed_prefix env s_body (sctx_of_ctx Gamma_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret_value T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
              body_env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret_value Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R')
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body
              Hcover_params)
    as [frame_final Hscope_body].
  { eapply store_param_scope_bind_params. exact Hargs_fcall. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  destruct
    (eval_direct_call_body_cleanup_preserves_value_and_refs_core
      env Omega s_fn s_args Sigma' fdef fcall [] s_body vs ret_value
      used' T_body Gamma_out R_body roots_body frame_final Hstore_args
      Hpres_args Hrename Hargs_fcall Hframe_scope Hscope_body
      Hstore_body_env Hv_body_env Hpres_body_env Hroots_body Hret_roots
      Hshadow_body Hrn_body Hsame_body Hcompat_body Hexclude_roots
      Hexclude_env)
    as [Hstore_final Hcleanup].
  destruct Hcleanup as [Hprefix_cleanup Hcleanup].
    destruct Hcleanup as [Hroots_cleanup Hcleanup].
    destruct Hcleanup as [Hshadow_cleanup Hcleanup].
    destruct Hcleanup as [Hrn_cleanup Hcleanup].
    destruct Hcleanup as [Hv_fdef Hcleanup].
    destruct Hcleanup as [Hpres_final [locals Hcleanup]].
    destruct Hcleanup as [Hremoved [Hret_exclude
      [Hstore_exclude [Hremoved_exact Hret_roots_body]]]].
    subst s_final.
    rewrite Hcaps_call. simpl.
    rewrite Hremoved_exact.
    repeat split.
    + exact Hstore_args.
    + rewrite <- Hremoved_exact.
      eapply runtime_tfn_signature_bridge_result_value.
      * exact Hbridge.
      * rewrite <- (apply_lt_ty_nil_ts (fn_ret fdef)). exact Hv_fdef.
    + rewrite <- Hremoved_exact.
      eapply store_ref_targets_preserved_trans.
      * exact Hpres_callee.
      * exact Hpres_final.
    + exact Hroots_args.
    + apply value_roots_within_union_r.
      eapply direct_call_value_roots_within_store_subset; eassumption.
    + exact Hshadow_args.
    + exact Hrn_args.
Qed.


Theorem eval_call_expr_tfn_components_preserve_typing_with_callee_summary :
  forall env s s_fn s_args s_body callee args fname captured fdef fcall
      vs ret_value used',
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret_value ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma Sigma1 R1 Sigma' R'
        callee_roots arg_roots u param_tys ret_ty,
      preservation_ready_args args ->
      provenance_ready_expr callee ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots_shadow_safe env Omega n R Sigma callee
        (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 callee_roots ->
      typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
        (params_of_tys param_tys) Sigma' R' arg_roots ->
      fn_env_unique_by_name env ->
      callee_body_root_shadow_provenance_summary env fdef ->
      let s_final :=
        store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body) in
      store_typed env s_final Sigma' /\
      value_has_type env s_final ret_value ret_ty /\
      store_ref_targets_preserved env s s_final /\
      store_roots_within R' s_final /\
      value_roots_within
        (root_set_union callee_roots (root_sets_union arg_roots))
        ret_value /\
      store_no_shadow s_final /\
      root_env_no_shadow R'.
Proof.
  intros env s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret_value used' Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' callee_roots arg_roots u
    param_tys ret_ty Hready_args Hprov_callee Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Htyped_callee_shadow Htyped_args_shadow Hunique
    Hcallee_summary s_final.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma callee (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 callee_roots Htyped_callee_shadow) as Htyped_callee.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
              env s callee s_fn (VClosure fname captured) Heval_callee
              Omega n R Sigma (MkTy u (TFn param_tys ret_ty))
              Sigma1 R1 callee_roots Hprov_callee Hstore Hroots Hshadow
              Hrn Htyped_callee)
    as [Hstore_fn [Hv_callee [Hpres_callee
        [Hroots_fn [Hv_callee_roots [Hshadow_fn Hrn_fn]]]]]].
  destruct (proj1 eval_preserves_root_names_ready_mutual
              env s callee s_fn (VClosure fname captured) Heval_callee
              Omega n R Sigma (MkTy u (TFn param_tys ret_ty))
              Sigma1 R1 callee_roots Hprov_callee Hstore Hroots Hshadow
              Hrn Hnamed Htyped_callee) as [Hnamed_fn _].
  pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
              env s callee s_fn (VClosure fname captured) Heval_callee
              Omega n R Sigma (MkTy u (TFn param_tys ret_ty))
              Sigma1 R1 callee_roots Hprov_callee Hstore Hroots Hshadow
              Hrn Hkeys Htyped_callee) as Hkeys_fn.
  pose proof
    (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured.
  subst captured.
  simpl in Hrename, Heval_body.
  destruct
    (value_has_type_empty_closure_plain_tfn_non_generic
      env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique)
    as [Htype_params Hlifetimes].
  destruct
    (value_has_type_empty_closure_tfn_components
      env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique
      Htype_params Hlifetimes)
    as [Hcaps_fdef Hbridge].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args_shadow) as Htyped_args.
  assert (Hcallee_route :
    callee_body_root_shadow_provenance_ready_at_result_subset env fcall
      (call_param_root_env (fn_params fcall) arg_roots R')
      (root_sets_union arg_roots)).
  { eapply
      direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset;
      eassumption. }
  eapply eval_call_expr_tfn_components_preserve_typing_with_callee_summary_route;
    eassumption.
Qed.

Theorem eval_empty_closure_call_expr_components_preserve_typing_with_callee_summary :
  forall env s s_fn s_args s_body callee fname args fdef fcall vs ret used',
    eval env s callee s_fn (VClosure fname []) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_captures fdef = [] ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots fsummary,
      preservation_ready_args args ->
      store_typed env s_fn Sigma ->
      store_roots_within R s_fn ->
      store_no_shadow s_fn ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s_fn ->
      root_env_store_keys_named R s_fn ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R' roots ->
      fn_env_unique_by_name env ->
      In fsummary (env_fns env) ->
      fn_name fsummary = fname ->
      callee_body_root_shadow_provenance_summary env fsummary ->
      store_typed env (store_remove_params (fn_params fcall) s_body) Sigma' /\
      value_has_type env (store_remove_params (fn_params fcall) s_body)
        ret T /\
      store_ref_targets_preserved env s_fn
        (store_remove_params (fn_params fcall) s_body) /\
      store_roots_within R'
        (store_remove_params (fn_params fcall) s_body) /\
      value_roots_within roots ret /\
      store_no_shadow (store_remove_params (fn_params fcall) s_body) /\
      root_env_no_shadow R'.
Proof.
  intros env s s_fn s_args s_body callee fname args fdef fcall vs ret
    used' Heval_callee Hlookup Hcaps Heval_args Hrename Heval_body Omega n R
    Sigma T Sigma' R' roots fsummary Hready_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Htyped Hunique Hin_summary Hfname_summary
    Hcallee_summary.
  pose proof
    (eval_empty_closure_call_expr_components_as_direct_call
      env s s_fn s_args s_body callee args fname fdef fcall vs ret used'
      Heval_callee Hlookup Hcaps Heval_args Hrename Heval_body)
    as Heval_call.
  eapply eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary;
    eassumption.
Qed.
