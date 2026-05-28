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
