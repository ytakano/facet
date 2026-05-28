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
