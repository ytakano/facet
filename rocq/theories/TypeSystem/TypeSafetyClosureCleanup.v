From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosureRuntimeArgs.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma bind_params_ref_targets_preserved :
  forall env Ω s vs ps,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_ref_targets_preserved env s (bind_params ps vs s).
Proof.
  intros env Ω s vs ps Hnodup Hfresh Hargs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - apply store_ref_targets_preserved_refl.
  - simpl.
    eapply store_ref_targets_preserved_trans.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + apply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma bind_params_store_typed_prefix :
  forall env Ω s vs ps,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_typed_prefix env (bind_params ps vs s) (sctx_of_ctx (params_ctx ps)).
Proof.
  intros env Ω s vs ps Hnodup Hfresh Hargs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - simpl. unfold store_typed_prefix. exists [], s. split.
    + reflexivity.
    + constructor.
  - simpl.
    eapply store_typed_prefix_add_compatible.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + eapply value_has_type_store_preserved.
      * exact Hv.
      * eapply bind_params_ref_targets_preserved.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
        -- exact Hargs.
    + exact Hcompat.
    + apply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma bind_params_store_typed_prefix_extend :
  forall env Ω s Σ_frame vs ps,
    store_typed_prefix env s Σ_frame ->
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_typed_prefix env (bind_params ps vs s)
      (sctx_of_ctx (params_ctx ps) ++ Σ_frame).
Proof.
  intros env Ω s Σ_frame vs ps Hprefix Hnodup Hfresh Hargs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - simpl. exact Hprefix.
  - simpl.
    eapply store_typed_prefix_add_compatible.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + eapply value_has_type_store_preserved.
      * exact Hv.
      * eapply bind_params_ref_targets_preserved.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
        -- exact Hargs.
    + exact Hcompat.
    + apply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma eval_call_body_cleanup_preserves_value_and_refs_frame_core :
  forall env (Ω : outlives_ctx) frame Σ_frame fdef fcall σ s_body vs ret
      used' T_body Γ_out R_body roots_body frame_final,
    store_typed env frame Σ_frame ->
    alpha_rename_fn_def (store_names frame) fdef = (fcall, used') ->
    eval_args_values_have_types env Ω frame vs (fn_params fcall) ->
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx Γ_out) s_body frame ->
    store_param_scope (fn_params fcall) s_body frame_final ->
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) ->
    value_has_type env s_body ret T_body ->
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs frame) s_body ->
    store_roots_within R_body s_body ->
    value_roots_within roots_body ret ->
    store_no_shadow s_body ->
    root_env_no_shadow R_body ->
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_frame /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env frame
      (store_remove_params (fn_params fcall) s_body) /\
    exists locals,
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = frame /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω frame Σ_frame fdef fcall σ s_body vs ret used' T_body
    Γ_out R_body roots_body frame_final Hstore_frame Hrename Hargs_fcall
    Hframe_scope Hscope_body Hstore_body Hv_body Hpres_body Hroots_body
    Hret_roots Hshadow_body Hrn_body Hsame_body Hcompat_body Hexclude_ret
    Hexclude_env.
  pose proof (alpha_rename_fn_def_shape (store_names frame)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret _]].
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) frame).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              (fn_params fcall) s_body frame_final R_body roots_body ret
              Hscope_body Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_ret Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  assert (Hpres_bind :
    store_ref_targets_preserved env frame
      (bind_params (fn_params fcall) vs frame)).
  { eapply bind_params_ref_targets_preserved; eassumption. }
  assert (Hpres_frame_body :
    store_ref_targets_preserved env frame s_body).
  { eapply store_ref_targets_preserved_trans; eassumption. }
  assert (Hpres_frame_final :
    store_ref_targets_preserved env frame
      (store_remove_params (fn_params fcall) s_body)).
  { eapply store_ref_targets_preserved_remove_params_after_absent;
      eassumption. }
  assert (Hremoved_exact :
    store_remove_params (fn_params fcall) s_body = frame).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - eapply store_frame_scope_param_scope. exact Hframe_scope.
    - exact Hframe_scope. }
  assert (Hstore_final :
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_frame).
  { rewrite Hremoved_exact. exact Hstore_frame. }
  repeat split; try assumption.
  exists locals. repeat split; assumption.
Qed.

Definition eval_preserves_frame_scope_roots_ready_mutual_statement : Prop :=
  frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame).

Definition eval_preserves_typing_roots_ready_prefix_mutual_statement : Prop :=
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

Definition eval_preserves_param_scope_roots_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame').

Lemma eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω frame Σ_frame
    fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
    roots_body Hstore_frame Hrename Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_params Hprov_body Htyped_body Hcompat_body
    Hexclude_ret Hexclude_env Heval_body.
  pose proof (alpha_rename_fn_def_shape (store_names frame)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret _]].
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) frame).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs frame)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (bind_params (fn_params fcall) vs frame) frame).
  { eapply store_frame_scope_bind_params. exact Hargs_fcall. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh
      (sctx_of_ctx (params_ctx (fn_params fcall))) frame).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (proj1 Hframe_mutual
              env (bind_params (fn_params fcall) vs frame)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall) frame Hprov_body Htyped_body
              Hcover_params Hroots_bind Hshadow_bind Hrn_params
              Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  destruct (proj1 Htyping_mutual
              env (bind_params (fn_params fcall) vs frame)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Hprov_body Hstore_bind Hroots_bind Hshadow_bind Hrn_params
              Htyped_body)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body
        [Hret_roots [Hshadow_body Hrn_body]]]]]].
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct Hparam_mutual as [Hscope_expr _].
  assert (Hscope_start :
    store_param_scope (fn_params fcall)
      (bind_params (fn_params fcall) vs frame) frame).
  { eapply store_param_scope_bind_params. exact Hargs_fcall. }
  destruct (Hscope_expr env
              (bind_params (fn_params fcall) vs frame)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall) frame Hprov_body Htyped_body)
              as [frame_final Hscope_body].
  { exact Hcover_params. }
  { exact Hscope_start. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  destruct (eval_call_body_cleanup_preserves_value_and_refs_frame_core
              env Ω frame Σ_frame fdef fcall σ s_body vs ret used' T_body
              Γ_out R_body roots_body frame_final Hstore_frame Hrename
              Hargs_fcall Hframe_scope Hscope_body Hstore_body Hv_body
              Hpres_body Hroots_body Hret_roots Hshadow_body Hrn_body
              Hsame_body Hcompat_body Hexclude_ret Hexclude_env)
    as [Hstore_final Hcleanup].
  destruct Hcleanup as [Hstore_prefix Hcleanup].
  destruct Hcleanup as [Hroots_final Hcleanup].
  destruct Hcleanup as [Hshadow_final Hcleanup].
  destruct Hcleanup as [Hrn_final Hcleanup].
  destruct Hcleanup as [Hv_final Hcleanup].
  destruct Hcleanup as [Hpres_final [locals Hcleanup]].
  destruct Hcleanup as [Hremoved [Hret_exclude
    [Hstore_exclude [Hremoved_exact Hret_roots_final]]]].
  repeat split; try assumption.
  exists frame_final, locals. repeat split; assumption.
Qed.

Lemma eval_call_body_ctx_cleanup_erased_core :
  forall env (Ω : outlives_ctx) frame Σ_frame fdef fcall σ s_body ret
      T_body Γ_out R_body roots_body frame_final,
    store_typed env frame Σ_frame ->
    fn_ret fdef = fn_ret fcall ->
    NoDup (ctx_names
      (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
    store_frame_scope (fn_params fcall ++ fn_captures fcall)
      (sctx_of_ctx Γ_out) s_body frame ->
    store_param_scope (fn_params fcall ++ fn_captures fcall)
      s_body frame_final ->
    value_has_type env s_body ret T_body ->
    store_roots_within R_body s_body ->
    value_roots_within roots_body ret ->
    store_no_shadow s_body ->
    sctx_same_bindings (sctx_of_ctx (fn_body_ctx fcall))
      (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    store_typed env
      (store_remove_params (fn_params fcall ++ fn_captures fcall) s_body)
      Σ_frame /\
    value_has_type env
      (store_remove_params (fn_params fcall ++ fn_captures fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove_params (fn_params fcall ++ fn_captures fcall) s_body =
      frame /\
    value_refs_exclude_params (fn_params fcall ++ fn_captures fcall) ret.
Proof.
  intros env Ω frame Σ_frame fdef fcall σ s_body ret T_body
    Γ_out R_body roots_body frame_final Hstore_frame Hret Hnodup_all
    Hframe_scope Hscope_body Hv_body Hroots_body Hret_roots Hshadow_body
    Hsame_body Hcompat_body Hexclude_all Hexclude_env_all.
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              (fn_params fcall ++ fn_captures fcall) s_body frame_final
              R_body roots_body ret Hscope_body Hroots_body Hret_roots
              Hshadow_body Hnodup_all Hexclude_all Hexclude_env_all)
    as [locals [Hremoved [Hret_exclude _]]].
  assert (Hremoved_exact_all :
    store_remove_params (fn_params fcall ++ fn_captures fcall) s_body =
      frame).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - eapply store_frame_scope_param_scope. exact Hframe_scope.
    - exact Hframe_scope. }
  repeat split.
  - rewrite Hremoved_exact_all. exact Hstore_frame.
  - apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    + exact Hv_ret_fdef.
    + exact Hret_exclude.
  - exact Hremoved_exact_all.
  - exact Hret_exclude.
Qed.

Lemma eval_call_body_ctx_cleanup_hidden_frame_erased_core :
  forall env (Ω : outlives_ctx) s_args_hidden s_args Σ_args x T_hidden hidden
      fdef fcall σ s_body ret T_body Γ_out R_body roots_body frame_final,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    store_typed env s_args Σ_args ->
    fn_ret fdef = fn_ret fcall ->
    NoDup (ctx_names
      (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
    store_frame_scope (fn_params fcall ++ fn_captures fcall)
      (sctx_of_ctx Γ_out) s_body s_args_hidden ->
    store_param_scope (fn_params fcall ++ fn_captures fcall)
      s_body frame_final ->
    value_has_type env s_body ret T_body ->
    store_roots_within R_body s_body ->
    value_roots_within roots_body ret ->
    store_no_shadow s_body ->
    sctx_same_bindings (sctx_of_ctx (fn_body_ctx fcall))
      (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    roots_exclude x roots_body ->
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
  intros env Ω s_args_hidden s_args Σ_args x T_hidden hidden fdef fcall σ
    s_body ret T_body Γ_out R_body roots_body frame_final Hhidden
    Htyped_args Hret Hnodup_all Hframe_scope Hscope_body Hv_body
    Hroots_body Hret_roots Hshadow_body Hsame_body Hcompat_body
    Hexclude_all Hexclude_env_all Hroot_exclude_x.
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              (fn_params fcall ++ fn_captures fcall) s_body frame_final
              R_body roots_body ret Hscope_body Hroots_body Hret_roots
              Hshadow_body Hnodup_all Hexclude_all Hexclude_env_all)
    as [locals [Hremoved [Hret_exclude _]]].
  assert (Hret_exclude_x : value_refs_exclude_root x ret).
  { eapply value_roots_exclude_root; eassumption. }
  assert (Hremoved_exact_all :
    store_remove_params (fn_params fcall ++ fn_captures fcall) s_body =
      s_args_hidden).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - eapply store_frame_scope_param_scope. exact Hframe_scope.
    - exact Hframe_scope. }
  assert (Hfinal_exact :
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args).
  { rewrite <- store_remove_params_app.
    rewrite Hremoved_exact_all.
    subst s_args_hidden.
    apply store_remove_store_add_same. }
  repeat split.
  - rewrite Hfinal_exact. exact Htyped_args.
  - rewrite <- store_remove_params_app.
    apply value_has_type_store_remove_excluding_root.
    + apply value_has_type_apply_lt_ty.
      eapply value_has_type_store_remove_params_excluding.
      * exact Hv_ret_fdef.
      * exact Hret_exclude.
    + exact Hret_exclude_x.
  - exact Hfinal_exact.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core :
  (frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame)) ->
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame')) ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured
    s_args_hidden s_args Σ_args x T_hidden hidden fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body Hhidden
    Hcaptured_params_typed Htyped_args Hrename Hargs_fcall Hroots_bind
    Hshadow_bind Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body
    Hexclude_all Hexclude_env_all Hroot_exclude_x Heval_body.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured (fn_captures fcall) Hcaptured_params_typed)
    as Hprefix_caps0.
  pose proof (store_param_prefix_append_frame
                (fn_captures fcall) captured s_args_hidden []
                Hprefix_caps0) as Hprefix_caps.
  simpl in Hprefix_caps.
  pose proof (store_param_prefix_bind_params
                env Ω (captured ++ s_args_hidden) vs (fn_params fcall)
                Hargs_fcall) as Hprefix_params.
  pose proof (store_param_prefix_app
                (fn_params fcall) (fn_captures fcall)
                (bind_params (fn_params fcall) vs
                  (captured ++ s_args_hidden))
                (captured ++ s_args_hidden) s_args_hidden
                Hprefix_params Hprefix_caps) as Hprefix_all.
  assert (Hnodup_all :
    NoDup (ctx_names
      (params_ctx (fn_params fcall ++ fn_captures fcall)))).
  { pose proof (store_names_store_param_prefix
                  (fn_params fcall ++ fn_captures fcall)
                  (bind_params (fn_params fcall) vs
                    (captured ++ s_args_hidden))
                  s_args_hidden Hprefix_all) as Hnames_prefix.
    unfold store_no_shadow in Hshadow_bind.
    rewrite Hnames_prefix in Hshadow_bind.
    exact (NoDup_app_left_ts _ _ Hshadow_bind). }
  assert (Hstore_captured_prefix :
    store_typed_prefix env (captured ++ s_args_hidden)
      (sctx_of_ctx (params_ctx (fn_captures fcall)))).
  { eapply captured_params_store_typed_prefix_frame.
    exact Hcaptured_params_typed. }
  assert (Hnodup_params :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args_hidden)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hstore_bind_prefix :
    store_typed_prefix env
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      (sctx_of_ctx (fn_body_ctx fcall))).
  { pose proof (bind_params_store_typed_prefix_extend
                  env Ω (captured ++ s_args_hidden)
                  (sctx_of_ctx (params_ctx (fn_captures fcall)))
                  vs (fn_params fcall) Hstore_captured_prefix
                  Hnodup_params Hfresh_params Hargs_fcall)
      as Hprefix.
    unfold fn_body_ctx, fn_body_params, sctx_of_ctx in *.
    rewrite params_ctx_app. exact Hprefix. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall ++ fn_captures fcall)
      (sctx_of_ctx (fn_body_ctx fcall))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      s_args_hidden).
  { unfold fn_body_ctx, fn_body_params, sctx_of_ctx.
    constructor. exact Hprefix_all. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh (sctx_of_ctx (fn_body_ctx fcall))
      s_args_hidden).
  { unfold fn_body_ctx, fn_body_params, sctx_of_ctx.
    eapply store_param_prefix_frame_static_fresh; eassumption. }
  destruct (proj1 Hframe_mutual
              env
              (bind_params (fn_params fcall) vs
                (captured ++ s_args_hidden))
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall ++ fn_captures fcall) s_args_hidden
              Hprov_body Htyped_body Hcover_all Hroots_bind Hshadow_bind
              Hrn_params Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  destruct (proj1 Htyping_mutual
              env
              (bind_params (fn_params fcall) vs
                (captured ++ s_args_hidden))
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Hprov_body Hstore_bind_prefix Hroots_bind Hshadow_bind
              Hrn_params Htyped_body)
    as [_ [Hv_body [_ [Hroots_body [Hret_roots [Hshadow_body _]]]]]].
  pose proof (alpha_rename_fn_def_shape
                (store_names (captured ++ s_args_hidden))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret _]].
  destruct Hparam_mutual as [Hscope_expr _].
  assert (Hscope_start :
    store_param_scope (fn_params fcall ++ fn_captures fcall)
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      s_args_hidden).
  { constructor. exact Hprefix_all. }
  destruct (Hscope_expr env
              (bind_params (fn_params fcall) vs
                (captured ++ s_args_hidden))
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall ++ fn_captures fcall) s_args_hidden
              Hprov_body Htyped_body)
              as [frame_final Hscope_body].
  { exact Hcover_all. }
  { exact Hscope_start. }
  assert (Hsame_body :
    sctx_same_bindings (sctx_of_ctx (fn_body_ctx fcall))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  eapply eval_call_body_ctx_cleanup_hidden_frame_erased_core;
    eassumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured
    s_args_hidden s_args Σ_args x T_hidden hidden fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body roots_bound
    Hhidden Hcaptured_params_typed Htyped_args Hrename Hargs_fcall
    Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body Htyped_body
    Hcompat_body Hexclude_all Hexclude_env_all Hsubset Hroot_exclude_bound
    Heval_body.
  eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core
            Hframe_mutual Htyping_mutual Hparam_mutual);
    try eassumption.
  eapply roots_exclude_stores_subset; eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_hidden_cleanup_package_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_final m x T
    fname captures args ret Husage Heval Hready Hfree Hlocal Hrefs.
  destruct (eval_let_make_closure_captured_call_args_strip
              env s s_final m x T fname captures args ret Husage Heval
              Hready Hfree Hlocal Hrefs)
    as (captured & fdef & s_args_hidden & s_args & vs & fcall & used' &
        s_body & Hlookup & Hcopy & Hhidden & Heval_args & Hrefs_args &
        Hvs_refs & Hrename & Heval_body & Hfinal).
  exists captured, fdef, s_args_hidden, s_args, vs, fcall, used', s_body.
  split; [exact Hlookup|].
  split; [exact Hcopy|].
  split; [exact Hhidden|].
  split; [exact Heval_args|].
  split; [exact Hrefs_args|].
  split; [exact Hvs_refs|].
  split; [exact Hrename|].
  split; [exact Heval_body|].
  split; [exact Hfinal|].
  intros ? ? ? ? ? ? ? ?
    Hcaptured_params Htyped_args Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body Hexclude_all
    Hexclude_env_all Hsubset Hroot_exclude_bound.
  subst s_final.
  eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset_with_preservation_core
            Hframe_mutual Htyping_mutual Hparam_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core :
  (frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame)) ->
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame')) ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured Rcap
    s_args R_args Σ_args fdef fcall σ s_body vs ret used' T_body Γ_out
    R_params R_body roots_body Hframe_params_ready Htyped_args Hrename
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body
    Htyped_body Hcompat_body Hexclude_all Hexclude_env_all Heval_body.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  pose proof (captured_params_store_typed_store_param_prefix
                env captured (fn_captures fcall) Hcaptured_params_typed)
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
  { eapply captured_params_store_typed_prefix_frame.
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
              env
              (bind_params (fn_params fcall) vs (captured ++ s_args))
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall ++ fn_captures fcall) s_args
              Hprov_body Htyped_body Hcover_all Hroots_bind Hshadow_bind
              Hrn_params Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  destruct (proj1 Htyping_mutual
              env
              (bind_params (fn_params fcall) vs (captured ++ s_args))
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Hprov_body Hstore_bind_prefix Hroots_bind Hshadow_bind
              Hrn_params Htyped_body)
    as [Hstore_body [Hv_body [_ [Hroots_body [Hret_roots
        [Hshadow_body _]]]]]].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret _]].
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct Hparam_mutual as [Hscope_expr _].
  assert (Hscope_start :
    store_param_scope (fn_params fcall ++ fn_captures fcall)
      (bind_params (fn_params fcall) vs (captured ++ s_args)) s_args).
  { constructor. exact Hprefix_all. }
  destruct (Hscope_expr env
              (bind_params (fn_params fcall) vs (captured ++ s_args))
              (fn_body fcall) s_body ret Heval_body
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
              Hframe_scope Hscope_body Hv_body Hroots_body Hret_roots
              Hshadow_body Hsame_body Hcompat_body Hexclude_all
              Hexclude_env_all)
    as [Hstore_erased [Hv_erased [Hremoved_exact_all _]]].
  assert (Hfinal_exact :
    store_remove_params (fn_captures fcall)
      (store_remove_params (fn_params fcall) s_body) = s_args).
  { rewrite <- store_remove_params_app. exact Hremoved_exact_all. }
  repeat split.
  - rewrite <- store_remove_params_app. exact Hstore_erased.
  - rewrite <- store_remove_params_app. exact Hv_erased.
  - exact Hfinal_exact.
Qed.

Lemma eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core :
  (frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame)) ->
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame')) ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_fn s_args
    s_body callee args fname captured fdef fcall vs ret used' Rcap R_args
    Σ_args σ T_body Γ_out R_params R_body roots_body Heval_callee Hlookup
    Heval_args Hrename Heval_body Hframe_params_ready Htyped_args
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body
    Htyped_body Hcompat_body Hexclude_all Hexclude_env_all.
  split.
  - eapply Eval_CallExpr; eassumption.
  - destruct
      (eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
        Hframe_mutual Htyping_mutual Hparam_mutual
        env Ω captured Rcap s_args R_args Σ_args fdef fcall σ
        s_body vs ret used' T_body Γ_out R_params R_body roots_body
        Hframe_params_ready Htyped_args Hrename Hargs_fcall
        Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body
        Htyped_body Hcompat_body Hexclude_all Hexclude_env_all
        Heval_body)
      as [Hstore [Hv _]].
    split; assumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured Rcap
    s_args R_args Σ_args fdef fcall σ s_body vs ret used' T_body
    Γ_out R_params R_body roots_body Hframe_ready Htyped_args Hrename
    Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_params
    Hprov_body Htyped_body Hcompat_body Hexclude_ret Hexclude_env
    Heval_body.
  eapply (eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core
            Hframe_mutual Htyping_mutual Hparam_mutual);
    try eassumption.
  eapply captured_call_frame_store_typed; eassumption.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
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
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω s s_fn s_args
    s_body callee args fname captured fdef fcall vs ret used' Rcap R_args
    Σ_args σ T_body Γ_out R_params R_body roots_body Heval_callee Hlookup
    Heval_args Hrename Heval_body Hframe_ready Htyped_args Hargs_fcall
    Hroots_bind Hshadow_bind Hrn_params Hcover_params Hprov_body
    Htyped_body Hcompat_body Hexclude_ret Hexclude_env.
  split.
  - eapply Eval_CallExpr; eassumption.
  - eapply (eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core
              Hframe_mutual Htyping_mutual Hparam_mutual);
      eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
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
      Hframe_mutual Htyping_mutual Hparam_mutual
      env Ω captured Rcap s_args R_args Σ_args fdef fcall σ s_body vs
      ret used' T_body Γ_out R_params R_body roots_body Hframe_ready
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
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
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
              Hframe_mutual Htyping_mutual Hparam_mutual);
      eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
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
      Hframe_mutual Htyping_mutual Hparam_mutual
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

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core :
  (frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame)) ->
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame')) ->
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
  eapply
    (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
      Hframe_mutual Htyping_mutual Hparam_mutual);
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto_with_preservation_core :
  (frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame)) ->
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame')) ->
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
  eapply
    (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
      Hframe_mutual Htyping_mutual Hparam_mutual);
    eassumption.
Qed.
