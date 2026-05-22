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

Record typed_rooted_args_result
    (env : global_env) (Ω : outlives_ctx) (s s' : store)
    (vs : list value) (ps : list param) (Σ' : sctx)
    (R' : root_env) (roots : list root_set) : Prop := {
  typed_rooted_args_store_prefix : store_typed_prefix env s' Σ';
  typed_rooted_args_values_types :
    eval_args_values_have_types env Ω s' vs ps;
  typed_rooted_args_refs_preserved : store_ref_targets_preserved env s s';
  typed_rooted_args_roots : rooted_args_result R' s' roots vs
}.

Record typed_rooted_fields_result
    (env : global_env) (s s' : store) (lts : list lifetime)
    (args : list Ty) (values : list (string * value))
    (defs : list field_def) (Σ' : sctx) (R' : root_env)
    (roots : root_set) : Prop := {
  typed_rooted_fields_store_prefix : store_typed_prefix env s' Σ';
  typed_rooted_fields_values_types :
    struct_fields_have_type env s' lts args values defs;
  typed_rooted_fields_refs_preserved : store_ref_targets_preserved env s s';
  typed_rooted_fields_roots : rooted_fields_result R' s' roots values
}.

Definition eval_preserves_typing_roots_ready_prefix_mutual_package_statement
    : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_rooted_eval_result env s s' v T Σ' R' roots) /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      typed_rooted_args_result env Ω s s' vs ps Σ' R' roots) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      typed_rooted_fields_result env s s' lts args values defs Σ' R' roots).

Lemma eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement.
Proof.
  intros [Hexpr [Hargs Hfields]].
  split.
  - intros env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a T_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
    destruct (Hexpr env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a
                Σ_a T_a Σ_b R_b roots_a
                Hprov Hprefix Hroots Hshadow Hrn Htyped)
      as [Hprefix' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    constructor.
    + exact Hprefix'.
    + exact Hv.
    + exact Hpres.
    + constructor; assumption.
  - split.
    + intros env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
      destruct (Hargs env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a
                  ps_a Σ_b R_b roots_a
                  Hprov Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' [Hvs [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
      constructor.
      * exact Hprefix'.
      * exact Hvs.
      * exact Hpres.
      * constructor; assumption.
    + intros env_a st_a fields_a defs_a st_b values_a Heval Ω_a n_a lts_a
      ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow
      Hrn Htyped.
      destruct (Hfields env_a st_a fields_a defs_a st_b values_a Heval Ω_a
                  n_a lts_a ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov
                  Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' [Hvalues [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
      constructor.
      * exact Hprefix'.
      * exact Hvalues.
      * exact Hpres.
      * constructor; assumption.
Qed.

Lemma eval_preserves_typing_roots_ready_prefix_mutual_package_statement_to_plain :
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement.
Proof.
  intros [Hexpr [Hargs Hfields]].
  split.
  - intros env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a T_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
    destruct (Hexpr env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a
                Σ_a T_a Σ_b R_b roots_a
                Hprov Hprefix Hroots Hshadow Hrn Htyped)
      as [Hprefix' Hv Hpres Hrooted].
    destruct Hrooted as [Hroots' Hvroots Hshadow' Hrn'].
    repeat split; assumption.
  - split.
    + intros env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
      destruct (Hargs env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a
                  ps_a Σ_b R_b roots_a
                  Hprov Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' Hvs Hpres Hrooted].
      destruct Hrooted as [Hroots' Hvroots Hshadow' Hrn'].
      repeat split; assumption.
    + intros env_a st_a fields_a defs_a st_b values_a Heval Ω_a n_a lts_a
      ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow
      Hrn Htyped.
      destruct (Hfields env_a st_a fields_a defs_a st_b values_a Heval Ω_a
                  n_a lts_a ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov
                  Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' Hvalues Hpres Hrooted].
      destruct Hrooted as [Hroots' Hvroots Hshadow' Hrn'].
      repeat split; assumption.
Qed.

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
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
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
  pose proof (proj1 Htyping_mutual
                env (bind_params (fn_params fcall) vs frame)
                (fn_body fcall) s_body ret Heval_body
                (fn_outlives fcall) (fn_lifetimes fcall)
                R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
                T_body (sctx_of_ctx Γ_out) R_body roots_body
                Hprov_body Hstore_bind Hroots_bind Hshadow_bind Hrn_params
                Htyped_body) as Hbody_package.
  destruct (typed_rooted_eval_roots _ _ _ _ _ _ _ _ Hbody_package)
    as [Hroots_body Hret_roots Hshadow_body Hrn_body].
  destruct Hbody_package as [Hstore_body Hv_body Hpres_body _].
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
