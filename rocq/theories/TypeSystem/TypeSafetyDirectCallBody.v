From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyDirectCallSetup.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma direct_call_type_lookup_path_global_env_with_local_bounds :
  forall env bounds T path,
    type_lookup_path (global_env_with_local_bounds env bounds) T path =
    type_lookup_path env T path.
Proof.
  intros env bounds T path.
  revert env bounds T.
  induction path as [| field rest IH]; intros env bounds T; simpl; auto.
  destruct T as [u core]; simpl.
  destruct core; try reflexivity.
  change (lookup_struct s (global_env_with_local_bounds env bounds))
    with (lookup_struct s env).
  destruct (lookup_struct s env) as [sdef |]; [| reflexivity].
  destruct (lookup_field field (struct_fields sdef)); [apply IH | reflexivity].
Qed.

Lemma direct_call_value_has_type_global_env_with_local_bounds :
  forall env bounds s v T,
    value_has_type env s v T ->
    value_has_type (global_env_with_local_bounds env bounds) s v T
with direct_call_struct_fields_have_type_global_env_with_local_bounds :
  forall env bounds s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    struct_fields_have_type (global_env_with_local_bounds env bounds)
      s lts args fields defs.
Proof.
  - intros env bounds s v T H.
    induction H;
      try solve
        [ econstructor; simpl in *; eauto;
          rewrite ?direct_call_type_lookup_path_global_env_with_local_bounds;
          eauto ].
  - intros env bounds s lts args fields defs H.
    induction H; try solve [econstructor; eauto].
Qed.

Lemma direct_call_value_has_type_clear_global_env_local_bounds :
  forall env bounds s v T,
    value_has_type (global_env_with_local_bounds env bounds) s v T ->
    value_has_type env s v T
with direct_call_struct_fields_have_type_clear_global_env_local_bounds :
  forall env bounds s lts args fields defs,
    struct_fields_have_type (global_env_with_local_bounds env bounds)
      s lts args fields defs ->
    struct_fields_have_type env s lts args fields defs.
Proof.
  - intros env bounds s v T H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq;
      try solve
        [ subst; econstructor; simpl in *; eauto;
          rewrite ?direct_call_type_lookup_path_global_env_with_local_bounds in *;
          eauto ].
    all: try
      (subst; econstructor; simpl in *; eauto;
       rewrite ?direct_call_type_lookup_path_global_env_with_local_bounds in *;
       eauto).
  - intros env bounds s lts args fields defs H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq; try solve [econstructor; eauto].
    all: try (subst; eapply SFHT_Cons; eauto;
      eapply direct_call_value_has_type_clear_global_env_local_bounds; eauto).
Qed.

Lemma direct_call_store_entry_typed_global_env_with_local_bounds :
  forall env bounds s entry ce,
    store_entry_typed env s entry ce ->
    store_entry_typed (global_env_with_local_bounds env bounds) s entry ce.
Proof.
  unfold store_entry_typed.
  intros env bounds s entry ce H.
  destruct entry as [sx sT sv sst], ce as [[[cx cT] cst] cm]; simpl in *.
  destruct H as (Hx & HT & Hst & Hv).
  repeat split; auto.
  eapply direct_call_value_has_type_global_env_with_local_bounds. exact Hv.
Qed.

Lemma direct_call_store_typed_prefix_global_env_with_local_bounds :
  forall env bounds s Σ,
    store_typed_prefix env s Σ ->
    store_typed_prefix (global_env_with_local_bounds env bounds) s Σ.
Proof.
  unfold store_typed_prefix.
  intros env bounds s Σ (entries & frame & Hs & Htyped).
  exists entries, frame. repeat split; auto.
  eapply Forall2_impl; [| exact Htyped].
  intros entry ce Hentry.
  eapply direct_call_store_entry_typed_global_env_with_local_bounds.
  exact Hentry.
Qed.

Lemma direct_call_store_typed_prefix_clear_global_env_local_bounds :
  forall env bounds s Σ,
    store_typed_prefix (global_env_with_local_bounds env bounds) s Σ ->
    store_typed_prefix env s Σ.
Proof.
  unfold store_typed_prefix, store_entry_typed.
  intros env bounds s Σ (entries & frame & Hs & Htyped).
  exists entries, frame. repeat split; auto.
  eapply Forall2_impl; [| exact Htyped].
  intros entry ce Hentry.
  destruct entry as [sx sT sv sst], ce as [[[cx cT] cst] cm]; simpl in *.
  destruct Hentry as (Hx & HT & Hst & Hv).
  repeat split; auto.
  eapply direct_call_value_has_type_clear_global_env_local_bounds. exact Hv.
Qed.

Lemma direct_call_store_ref_targets_preserved_clear_global_env_local_bounds :
  forall env bounds s s',
    store_ref_targets_preserved (global_env_with_local_bounds env bounds) s s' ->
    store_ref_targets_preserved env s s'.
Proof.
  unfold store_ref_targets_preserved.
  intros env bounds s s' Hpres x path se v T Hlookup Hval Hpath.
  destruct (Hpres x path se v T Hlookup Hval) as (se' & v' & Hlookup' & Hval' & Hpath').
  { rewrite direct_call_type_lookup_path_global_env_with_local_bounds.
    exact Hpath. }
  exists se', v'. repeat split; auto.
  rewrite <- (direct_call_type_lookup_path_global_env_with_local_bounds
    env bounds (se_ty se') path).
  exact Hpath'.
Qed.

Lemma direct_call_eval_global_env_with_local_bounds :
  forall env bounds s e s' v,
    eval env s e s' v ->
    eval (global_env_with_local_bounds env bounds) s e s' v
with direct_call_eval_args_global_env_with_local_bounds :
  forall env bounds s args s' vs,
    eval_args env s args s' vs ->
    eval_args (global_env_with_local_bounds env bounds) s args s' vs
with direct_call_eval_struct_fields_global_env_with_local_bounds :
  forall env bounds s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    eval_struct_fields (global_env_with_local_bounds env bounds)
      s fields defs s' values.
Proof.
  - intros env bounds s e s' v Heval.
    induction Heval;
      try solve
        [ econstructor; simpl in *; eauto;
          rewrite ?direct_call_type_lookup_path_global_env_with_local_bounds;
          eauto ].
  - intros env bounds s args s' vs Hargs.
    induction Hargs; try solve [econstructor; eauto].
  - intros env bounds s fields defs s' values Hfields.
    induction Hfields; try solve [econstructor; eauto].
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
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
  intros Htyping_ready Htyping_prefix_ready env Ω n Σ Σ_args fname args
    fdef fcall σ s s_args s_body vs ret used' T_body Γ_out Hstore
    Hready_args Htyped_args Heval_args Hlookup Henv_checked Henv_ready
    Hrename Htyped_body Hcompat_body Heval_body.
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore Htyped_args)
    as [Hstore_args [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
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
      (fn_body fcall) s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hready_body : preservation_ready_expr (fn_body fcall)).
  { eapply lookup_alpha_rename_fn_def_preservation_ready_body; eassumption. }
  destruct (proj1 Htyping_prefix_ready
              env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out)
              Hready_body Hstore_bind Htyped_body)
    as [Hstore_body [Hv_body Hpres_body]].
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  repeat split; try assumption.
  eapply value_has_type_apply_lt_ty. exact Hv_ret_fdef.
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix_from_lookup_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
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
  intros Htyping_ready Htyping_prefix_ready env Ω n Σ Σ_args fname args
    fdef fcall σ s s_args s_body vs ret used' T_body Γ_out Hstore Hready_args
    Htyped_args Heval_args Hlookup Henv_checked Henv_ready Hrename
    Htyped_body Hcompat_body Hcaps_call Heval_body.
  exists Γ_out.
  eapply eval_direct_call_body_preserves_typing_prefix_with_preservation_core;
    eassumption.
Qed.

Lemma eval_direct_call_body_cleanup_preserves_value_and_refs_core :
  forall env (Ω : outlives_ctx) s s_args Σ_args fdef fcall σ s_body vs ret
      used' T_body Γ_out R_body roots_body frame_final,
    store_typed env s_args Σ_args ->
    store_ref_targets_preserved env s s_args ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    eval_args_values_have_types env Ω s_args vs (fn_params fcall) ->
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx Γ_out) s_body s_args ->
    store_param_scope (fn_params fcall) s_body frame_final ->
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) ->
    value_has_type env s_body ret T_body ->
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body ->
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
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body) /\
    exists locals,
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = s_args /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω s s_args Σ_args fdef fcall σ s_body vs ret used' T_body
    Γ_out R_body roots_body frame_final Hstore_args Hpres_args Hrename
    Hargs_fcall Hframe_scope Hscope_body Hstore_body Hv_body Hpres_body
    Hroots_body Hret_roots Hshadow_body Hrn_body Hsame_body Hcompat_body
    Hexclude_ret Hexclude_env.
  destruct (eval_call_body_cleanup_preserves_value_and_refs_frame_core
              env Ω s_args Σ_args fdef fcall σ s_body vs ret used' T_body
              Γ_out R_body roots_body frame_final Hstore_args Hrename
              Hargs_fcall Hframe_scope Hscope_body Hstore_body Hv_body
              Hpres_body Hroots_body Hret_roots Hshadow_body Hrn_body
              Hsame_body Hcompat_body Hexclude_ret Hexclude_env)
    as [Hstore_final Hcleanup].
  destruct Hcleanup as [Hstore_prefix Hcleanup].
  destruct Hcleanup as [Hroots_final Hcleanup].
  destruct Hcleanup as [Hshadow_final Hcleanup].
  destruct Hcleanup as [Hrn_final Hcleanup].
  destruct Hcleanup as [Hv_final Hcleanup].
  destruct Hcleanup as [Hpres_args_final [locals Hcleanup]].
  destruct Hcleanup as [Hremoved [Hret_exclude
    [Hstore_exclude [Hremoved_exact Hret_roots_final]]]].
  repeat split; try assumption.
  - eapply store_ref_targets_preserved_trans; eassumption.
  - exists locals. repeat split; assumption.
Qed.

Lemma eval_direct_call_body_cleanup_preserves_value_and_refs_with_preservation_core :
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
      store_ref_targets_preserved env s s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
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
      frame_scope_roots_ready_result ps R' Σ' s' frame) ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
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
      exists frame', store_param_scope ps s' frame') ->
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
  intros Htyping_ready Hroots_ready Hframe_scope_ready
    Htyping_roots_prefix_ready Hparam_scope_ready env Ω n R Σ Σ_args
    R_args arg_roots fname args fdef fcall σ s s_args s_body vs ret
    used' T_body Γ_out R_params R_body roots_body Hstore Hroots Hshadow
    Hrn Hprov_args Hready_args Htyped_args Heval_args Hrename Hroots_bind
    Hshadow_bind Hrn_params Hcover_params Hprov_body Htyped_body
    Hcompat_body Hexclude_ret Hexclude_env Heval_body.
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [Hstore_args [Hargs_subst Hpres_args]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hroots Hshadow Hrn Htyped_args)
    as [_ [_ [Hshadow_args _]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
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
      (fn_body fcall) s_body ret).
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
  destruct (proj1 Hframe_scope_ready
              body_env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body
              Hcover_params Hroots_bind Hshadow_bind Hrn_params
              Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  pose proof (proj1 Htyping_roots_prefix_ready
                body_env (bind_params (fn_params fcall) vs s_args)
                (fn_body fcall) s_body ret Heval_body_body_env
                (fn_outlives fcall) (fn_lifetimes fcall)
                R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
                T_body (sctx_of_ctx Γ_out) R_body roots_body
                Hprov_body Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_params
                Htyped_body) as Hbody_package.
  destruct (typed_rooted_eval_roots _ _ _ _ _ _ _ _ Hbody_package)
    as [Hroots_body Hret_roots Hshadow_body Hrn_body].
  destruct Hbody_package as [Hstore_body Hv_body Hpres_body _].
  assert (Hstore_body_env : store_typed_prefix env s_body (sctx_of_ctx Γ_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct Hparam_scope_ready as [Hscope_expr _].
  assert (Hscope_start :
    store_param_scope (fn_params fcall)
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_param_scope_bind_params. exact Hargs_fcall. }
  destruct (Hscope_expr body_env
              (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body)
              as [frame_final Hscope_body].
  { exact Hcover_params. }
  { exact Hscope_start. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  destruct (eval_direct_call_body_cleanup_preserves_value_and_refs_core
              env Ω s s_args Σ_args fdef fcall σ s_body vs ret used'
              T_body Γ_out R_body roots_body frame_final Hstore_args
              Hpres_args Hrename Hargs_fcall Hframe_scope Hscope_body
              Hstore_body_env Hv_body_env Hpres_body_env Hroots_body Hret_roots
              Hshadow_body Hrn_body Hsame_body Hcompat_body Hexclude_ret
              Hexclude_env)
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

Lemma eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
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
      frame_scope_roots_ready_result ps R' Σ' s' frame) ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
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
      exists frame', store_param_scope ps s' frame') ->
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
    (exists T_body Γ_out R_body roots_body,
      provenance_ready_expr (fn_body fcall) /\
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body).
Proof.
  intros Htyping_ready Hroots_ready Hframe_scope_ready
    Htyping_roots_prefix_ready Hparam_scope_ready env Ω n R Σ Σ_args
    R_args arg_roots args fdef fcall σ s s_args s_body vs ret used'
    Hstore Hroots Hshadow Hrn Hprov_args Hready_args Htyped_args
    Heval_args Hrename Hcaps Hbody_ready Heval_body.
  destruct Hbody_ready
    as (T_body & Γ_out & R_body & roots_body &
        Hprov_body & Htyped_body & Hcompat_body &
        Hexclude_ret & Hexclude_env).
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
              (fn_params fcall) Heval_args Hprov_args Htyped_args
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
               (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
      roots_body Hcaps_call Htyped_body) as Htyped_body_params.
  destruct (eval_direct_call_body_cleanup_preserves_value_and_refs_with_preservation_core
              Htyping_ready Hroots_ready Hframe_scope_ready
              Htyping_roots_prefix_ready Hparam_scope_ready
              env Ω n R Σ Σ_args R_args arg_roots (fn_name fdef) args fdef
              fcall σ s s_args s_body vs ret used' T_body Γ_out
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              R_body roots_body Hstore Hroots Hshadow Hrn Hprov_args
              Hready_args Htyped_args Heval_args Hrename Hroots_bind
              Hshadow_bind Hrn_params Hcover_params Hprov_body
              Htyped_body_params Hcompat_body Hexclude_ret Hexclude_env
              Heval_body)
    as [_ [Hstore_final [_ [_ [_ [_ [Hv_final [Hpres_final _]]]]]]]].
  repeat split; assumption.
Qed.

Lemma eval_args_root_subst_images_exclude_names_for_fresh_call_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
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
  intros Hroot_names env Ω n R Σ ps_typed Σ_args R_args arg_roots
    args s s_args vs fdef fcall used' Heval_args Hprov_args Hstore
    Hroots Hshadow Hrn Hnamed Htyped_args Hrename.
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Hnamed Htyped_args)
    as [_ Harg_roots_named].
  eapply alpha_rename_fn_def_body_root_subst_images_exclude_names_from_store_roots;
    eassumption.
Qed.

Lemma eval_args_root_keys_exclude_names_for_fresh_call_with_preservation_core :
  eval_preserves_root_keys_named_ready_mutual_statement ->
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
  intros Hroot_keys env Ω n R Σ ps_typed Σ_args R_args arg_roots
    args s s_args vs fdef fcall used' Heval_args Hprov_args Hstore
    Hroots Hshadow Hrn Hnamed Htyped_args Hrename x Hin.
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
                R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
                Hnamed Htyped_args)
    as Harg_keys_named.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                  (store_names s_args) fdef fcall used' Hrename)
      as Hfresh_names.
    apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  eapply root_env_store_keys_named_lookup_excludes_name.
  - exact Harg_keys_named.
  - exact Hfresh_x.
Qed.

Lemma eval_args_root_tail_fresh_names_for_fresh_call_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
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
  unfold root_env_tail_fresh_names.
  intros Hroot_names Hroot_keys env Ω n R Σ ps_typed Σ_args R_args
    arg_roots args s s_args vs fdef fcall used' Heval_args Hprov_args
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped_args Hrename x Hin.
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Hnamed Htyped_args)
    as [Harg_roots_named _].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
                R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
                Hkeys Htyped_args)
    as Harg_keys_named.
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names s_args) fdef fcall used' Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes.
    + eapply typed_args_roots_no_shadow; eassumption.
    + exact Hexcl.
Qed.

Lemma eval_args_root_names_excludes_params_ready_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
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
  intros Hroot_names env s args s_args vs Ω n R Σ ps Σ_args R_args
    arg_roots ps_bind Heval Hready Hstore Hroots Hnodup Hrn Hnamed
    Htyped Hfresh.
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval Ω n R Σ ps Σ_args R_args
              arg_roots Hready Hstore Hroots Hnodup Hrn Hnamed Htyped)
    as [Hnamed_args _].
  eapply root_env_store_roots_named_excludes_params; eassumption.
Qed.

Lemma eval_args_root_sets_union_excludes_fresh_name_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
  ((forall env s e s' v,
    eval env s e s' v ->
    preservation_ready_expr e ->
    store_names s' = store_names s) /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    preservation_ready_args args ->
    store_names s' = store_names s) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    preservation_ready_fields fields ->
    store_names s' = store_names s)) ->
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
  intros Hroot_names Hstore_names env s args s_args vs Ω n R Σ ps Σ_args
    R_args arg_roots x Heval Hready Hstore Hroots Hnodup Hrn Hnamed
    Htyped Hfresh.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready) as Hprov.
  pose proof (proj1 (proj2 Hstore_names)
              env s args s_args vs Heval Hready) as Hnames.
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval Ω n R Σ ps Σ_args R_args
              arg_roots Hprov Hstore Hroots Hnodup Hrn Hnamed Htyped)
    as [_ Harg_roots_named].
  eapply root_sets_union_store_roots_named_excludes_name.
  - exact Harg_roots_named.
  - rewrite Hnames. exact Hfresh.
Qed.
