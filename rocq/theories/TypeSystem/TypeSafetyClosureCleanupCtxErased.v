From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyClosureCleanupFrame.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma cleanup_type_lookup_path_global_env_with_local_bounds :
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

Lemma cleanup_value_has_type_global_env_with_local_bounds :
  forall env bounds s v T,
    value_has_type env s v T ->
    value_has_type (global_env_with_local_bounds env bounds) s v T
with cleanup_struct_fields_have_type_global_env_with_local_bounds :
  forall env bounds s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    struct_fields_have_type (global_env_with_local_bounds env bounds)
      s lts args fields defs
with cleanup_enum_values_have_type_global_env_with_local_bounds :
  forall env bounds s values tys,
    enum_values_have_type env s values tys ->
    enum_values_have_type (global_env_with_local_bounds env bounds)
      s values tys.
Proof.
  - intros env bounds s v T H.
    induction H;
      try solve
        [ econstructor; simpl in *; eauto;
          rewrite ?cleanup_type_lookup_path_global_env_with_local_bounds;
          eauto ].
  - intros env bounds s lts args fields defs H.
    induction H; try solve [econstructor; eauto].
  - intros env bounds s values tys H.
    induction H; try solve [econstructor; eauto].
Qed.

Lemma cleanup_value_has_type_clear_global_env_local_bounds :
  forall env bounds s v T,
    value_has_type (global_env_with_local_bounds env bounds) s v T ->
    value_has_type env s v T
with cleanup_struct_fields_have_type_clear_global_env_local_bounds :
  forall env bounds s lts args fields defs,
    struct_fields_have_type (global_env_with_local_bounds env bounds)
      s lts args fields defs ->
    struct_fields_have_type env s lts args fields defs
with cleanup_enum_values_have_type_clear_global_env_local_bounds :
  forall env bounds s values tys,
    enum_values_have_type (global_env_with_local_bounds env bounds)
      s values tys ->
    enum_values_have_type env s values tys.
Proof.
  - intros env bounds s v T H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq;
      try solve
        [ subst; econstructor; simpl in *; eauto;
          rewrite ?cleanup_type_lookup_path_global_env_with_local_bounds in *;
          eauto ].
    all: try
      (subst; econstructor; simpl in *; eauto;
       rewrite ?cleanup_type_lookup_path_global_env_with_local_bounds in *;
       eauto).
  - intros env bounds s lts args fields defs H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq; try solve [econstructor; eauto].
    all: try (subst; eapply SFHT_Cons; eauto;
      eapply cleanup_value_has_type_clear_global_env_local_bounds; eauto).
  - intros env bounds s values tys H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq; try solve [econstructor; eauto].
    all: try (subst; eapply EVHT_Cons; eauto;
      eapply cleanup_value_has_type_clear_global_env_local_bounds; eauto).
Qed.

Lemma cleanup_store_entry_typed_global_env_with_local_bounds :
  forall env bounds s entry ce,
    store_entry_typed env s entry ce ->
    store_entry_typed (global_env_with_local_bounds env bounds) s entry ce.
Proof.
  unfold store_entry_typed.
  intros env bounds s entry ce H.
  destruct entry as [sx sT sv sst], ce as [[[cx cT] cst] cm]; simpl in *.
  destruct H as (Hx & HT & Hst & Hv).
  repeat split; auto.
  eapply cleanup_value_has_type_global_env_with_local_bounds. exact Hv.
Qed.

Lemma cleanup_store_typed_prefix_global_env_with_local_bounds :
  forall env bounds s Σ,
    store_typed_prefix env s Σ ->
    store_typed_prefix (global_env_with_local_bounds env bounds) s Σ.
Proof.
  unfold store_typed_prefix.
  intros env bounds s Σ (entries & frame & Hs & Htyped).
  exists entries, frame. repeat split; auto.
  eapply Forall2_impl; [| exact Htyped].
  intros entry ce Hentry.
  eapply cleanup_store_entry_typed_global_env_with_local_bounds.
  exact Hentry.
Qed.

Lemma cleanup_eval_global_env_with_local_bounds :
  forall env bounds s e s' v,
    eval env s e s' v ->
    eval (global_env_with_local_bounds env bounds) s e s' v
with cleanup_eval_args_global_env_with_local_bounds :
  forall env bounds s args s' vs,
    eval_args env s args s' vs ->
    eval_args (global_env_with_local_bounds env bounds) s args s' vs
with cleanup_eval_struct_fields_global_env_with_local_bounds :
  forall env bounds s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    eval_struct_fields (global_env_with_local_bounds env bounds)
      s fields defs s' values.
Proof.
  - intros env bounds s e s' v Heval.
    induction Heval;
      try solve
        [ econstructor; simpl in *; eauto;
          rewrite ?cleanup_type_lookup_path_global_env_with_local_bounds;
          eauto ].
  - intros env bounds s args s' vs Hargs.
    induction Hargs; try solve [econstructor; eauto].
  - intros env bounds s fields defs s' values Hfields.
    induction Hfields; try solve [econstructor; eauto].
Qed.

Lemma value_roots_within_stores_subset_cleanup :
  (forall roots v,
    value_roots_within roots v ->
    forall roots',
      root_set_stores_subset roots roots' ->
      value_roots_within roots' v) /\
  (forall R se,
    store_entry_roots_within R se -> True) /\
  (forall R s,
    store_roots_within R s -> True) /\
  (forall roots fields,
    value_fields_roots_within roots fields ->
    forall roots',
      root_set_stores_subset roots roots' ->
      value_fields_roots_within roots' fields).
Proof.
  apply value_roots_within_mutind; intros; try solve [constructor; eauto].
  - constructor.
    intros root Hexclude.
    match goal with
    | Hvalue : forall root, roots_exclude root _ -> _ |- _ =>
        apply Hvalue
    end.
    unfold roots_exclude in *.
    intros Hin.
    apply Hexclude.
    apply H. exact Hin.
  - constructor.
    intros root Hexclude.
    match goal with
    | Hvalue : forall root, roots_exclude root _ -> _ |- _ =>
        apply Hvalue
    end.
    unfold roots_exclude in *.
    intros Hin.
    apply Hexclude.
    apply H. exact Hin.
Qed.

Lemma value_roots_within_store_subset_cleanup :
  forall roots v roots',
    value_roots_within roots v ->
    root_set_stores_subset roots roots' ->
    value_roots_within roots' v.
Proof.
  intros roots v roots' Hwithin Hsubset.
  exact (proj1 value_roots_within_stores_subset_cleanup
    roots v Hwithin roots' Hsubset).
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
    value_roots_within roots_body ret /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  intros env Ω s_args_hidden s_args Σ_args x T_hidden hidden fdef fcall σ
    s_body ret T_body Γ_out R_body roots_body frame_final Hhidden
    Htyped_args Hret Hnodup_all Hframe_scope Hscope_body Hv_body
    Hroots_body Hret_roots Hshadow_body Hsame_body Hcompat_body
    Hexclude_all Hroot_exclude_x.
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  assert (Hret_exclude :
    value_refs_exclude_params
      (fn_params fcall ++ fn_captures fcall) ret).
  { eapply value_roots_exclude_params; eassumption. }
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
  - exact Hret_roots.
  - exact Hfinal_exact.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) captured s_args_hidden s_args
      Σ_args x T_hidden hidden fdef fcall σ s_body vs ret used'
      T_body Γ_out R_params R_body roots_body,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    captured_params_store_typed_in_frame env captured s_args_hidden
      (fn_captures fcall) ->
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
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
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
    value_roots_within roots_body ret /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured
    s_args_hidden s_args Σ_args x T_hidden hidden fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body Hhidden
    Hcaptured_params_typed Htyped_args Hrename Hargs_fcall Hroots_bind
    Hshadow_bind Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body
    Hexclude_all Hroot_exclude_x Heval_body.
  pose proof (captured_params_store_typed_in_frame_store_param_prefix
                env captured s_args_hidden (fn_captures fcall)
                Hcaptured_params_typed)
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
  { eapply captured_params_store_typed_in_frame_prefix_frame.
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
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Hstore_bind_prefix_body_env :
    store_typed_prefix body_env
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      (sctx_of_ctx (fn_body_ctx fcall))).
  { subst body_env.
    eapply cleanup_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_prefix. }
  assert (Heval_body_body_env :
    eval body_env (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) (fn_body fcall) s_body ret).
  { subst body_env.
    eapply cleanup_eval_global_env_with_local_bounds.
    exact Heval_body. }
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
              body_env
              (bind_params (fn_params fcall) vs
                (captured ++ s_args_hidden))
              (fn_body fcall) s_body ret Heval_body_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (fn_body_ctx fcall))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall ++ fn_captures fcall) s_args_hidden
              Hprov_body Htyped_body Hcover_all Hroots_bind Hshadow_bind
              Hrn_params Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  pose proof (proj1 Htyping_mutual
                body_env
                (bind_params (fn_params fcall) vs
                  (captured ++ s_args_hidden))
                (fn_body fcall) s_body ret Heval_body_body_env
                (fn_outlives fcall) (fn_lifetimes fcall)
                R_params (sctx_of_ctx (fn_body_ctx fcall))
                T_body (sctx_of_ctx Γ_out) R_body roots_body
                Hprov_body Hstore_bind_prefix_body_env Hroots_bind Hshadow_bind
                Hrn_params Htyped_body) as Hbody_package.
  destruct (typed_rooted_eval_roots _ _ _ _ _ _ _ _ Hbody_package)
    as [Hroots_body Hret_roots Hshadow_body _].
  destruct Hbody_package as [_ Hv_body _ _].
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
  destruct (Hscope_expr body_env
              (bind_params (fn_params fcall) vs
                (captured ++ s_args_hidden))
              (fn_body fcall) s_body ret Heval_body_body_env
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
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply cleanup_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  destruct (eval_call_body_ctx_cleanup_hidden_frame_erased_core
              env Ω s_args_hidden s_args Σ_args x T_hidden hidden fdef
              fcall σ s_body ret T_body Γ_out R_body roots_body
              frame_final Hhidden Htyped_args Hret Hnodup_all
              Hframe_scope Hscope_body Hv_body_env Hroots_body Hret_roots
              Hshadow_body Hsame_body Hcompat_body Hexclude_all
              Hroot_exclude_x)
    as [Hstore_final [Hv_final [Hret_roots_final Hfinal]]].
  repeat split; assumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) captured s_args_hidden s_args
      Σ_args x T_hidden hidden fdef fcall σ s_body vs ret used'
      T_body Γ_out R_params R_body roots_body roots_bound,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    captured_params_store_typed_in_frame env captured s_args_hidden
      (fn_captures fcall) ->
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
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
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
    value_roots_within roots_bound ret /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  intros Hframe_mutual Htyping_mutual Hparam_mutual env Ω captured
    s_args_hidden s_args Σ_args x T_hidden hidden fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body roots_bound
    Hhidden Hcaptured_params_typed Htyped_args Hrename Hargs_fcall
    Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body Htyped_body
    Hcompat_body Hexclude_all Hsubset Hroot_exclude_bound Heval_body.
  assert (Hroot_exclude_body : roots_exclude x roots_body).
  { eapply roots_exclude_stores_subset; eassumption. }
  destruct (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core
              Hframe_mutual
              Htyping_mutual
              Hparam_mutual
              env Ω captured s_args_hidden s_args Σ_args x T_hidden hidden
              fdef fcall σ s_body vs ret used' T_body Γ_out R_params
              R_body roots_body Hhidden Hcaptured_params_typed Htyped_args
              Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
              Hcover_all Hprov_body Htyped_body Hcompat_body Hexclude_all
              Hroot_exclude_body Heval_body)
    as [Hstore_final [Hv_final [Hret_roots Hfinal]]].
  repeat split.
  - exact Hstore_final.
  - exact Hv_final.
  - eapply value_roots_within_store_subset_cleanup; eassumption.
  - exact Hfinal.
Qed.

Lemma eval_let_make_closure_captured_call_hidden_cleanup_package_with_preservation_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
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
        captured_params_store_typed_in_frame env captured s_args_hidden
          (fn_captures fcall) ->
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
        typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
          (fn_outlives fcall) (fn_lifetimes fcall)
          R_params (sctx_of_ctx (fn_body_ctx fcall))
          (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
        ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
        roots_exclude_params (fn_params fcall ++ fn_captures fcall)
          roots_body ->
        root_set_stores_subset roots_body roots_bound ->
        roots_exclude x roots_bound ->
        store_typed env s_final Σ_args /\
        value_has_type env s_final ret (apply_lt_ty sigma_result (fn_ret fdef)) /\
        value_roots_within roots_bound ret /\
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
    Hsubset Hroot_exclude_bound.
  subst s_final.
  eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset_with_preservation_core
            Hframe_mutual
            Htyping_mutual
            Hparam_mutual);
    eassumption.
Qed.
