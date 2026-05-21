From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma bind_params_head_fresh_in_tail :
  forall env Ω s p ps vs,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    params_fresh_in_store (p :: ps) s ->
    eval_args_values_have_types env Ω s vs ps ->
    ~ In (param_name p) (store_names (bind_params ps vs s)).
Proof.
  intros env Ω s p ps vs Hnodup Hfresh Hargs.
  rewrite (store_names_bind_params env Ω s vs ps Hargs).
  rewrite in_app_iff.
  intros [Hin_params | Hin_store].
  - exact (params_ctx_names_nodup_head_not_tail p ps Hnodup Hin_params).
  - exact (params_fresh_in_store_head p ps s Hfresh Hin_store).
Qed.

Lemma bind_params_store_no_shadow :
  forall env Ω s vs ps,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_no_shadow s ->
    store_no_shadow (bind_params ps vs s).
Proof.
  intros env Ω s vs ps Hnodup Hfresh Hargs Hshadow.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - exact Hshadow.
  - simpl.
    apply store_no_shadow_add.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma bind_params_store_roots_within_call_param_root_env :
  forall env Ω s vs ps R_tail arg_roots,
    eval_args_values_have_types env Ω s vs ps ->
    Forall2 value_roots_within arg_roots vs ->
    store_roots_within R_tail s ->
    store_no_shadow s ->
    root_env_no_shadow R_tail ->
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    store_roots_within (call_param_root_env ps arg_roots R_tail)
      (bind_params ps vs s).
Proof.
  intros env Ω s vs ps R_tail arg_roots Hargs Hvalues Hroots Hshadow
    Hrn Hnodup Hfresh.
  revert R_tail arg_roots Hroots Hrn Hnodup Hfresh Hvalues.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH];
    intros R_tail arg_roots Hroots Hrn Hnodup Hfresh Hvalues; simpl in *.
  - inversion Hvalues; subst. exact Hroots.
  - inversion Hvalues as [| ? ? ? ? Hvalue Hvalues_tail]; subst.
    rename l into arg_roots_tail.
    inversion Hnodup as [| ? ? Hnotin_tail Hnodup_tail]; subst.
    assert (Htail_roots_base :
      store_roots_within (root_env_remove (param_name p) R_tail) s).
    { apply store_roots_within_remove_env.
      - exact Hroots.
      - intros se Hin Heq.
        pose proof (store_entry_name_in_store_names se s Hin) as Hse_name.
        rewrite Heq in Hse_name.
        exact (params_fresh_in_store_head p ps s Hfresh Hse_name). }
    assert (Htail_roots :
      store_roots_within
        (call_param_root_env ps arg_roots_tail
          (root_env_remove (param_name p) R_tail))
        (bind_params ps vs s)).
    { apply IH.
      - exact Htail_roots_base.
      - apply root_env_no_shadow_remove. exact Hrn.
      - exact Hnodup_tail.
      - eapply params_fresh_in_store_tail. exact Hfresh.
      - exact Hvalues_tail. }
    assert (Hparam_fresh_root :
      root_env_lookup (param_name p)
        (call_param_root_env ps arg_roots_tail
          (root_env_remove (param_name p) R_tail)) = None).
    { unfold call_param_root_env.
      rewrite root_env_add_params_roots_lookup_not_in.
      - rewrite root_env_lookup_remove_params_not_in.
        + apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
        + exact Hnotin_tail.
      - exact Hnotin_tail. }
    apply store_add_roots_within.
    + exact Htail_roots.
    + exact Hparam_fresh_root.
    + exact Hvalue.
Qed.

Lemma eval_args_bind_params_call_param_root_env_ready :
  forall env s args s_args vs Ω n R Σ ps_typed Σ_args R_args arg_roots
      ps_bind,
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    NoDup (ctx_names (params_ctx ps_bind)) ->
    params_fresh_in_store ps_bind s_args ->
    eval_args_values_have_types env Ω s_args vs ps_bind ->
    store_roots_within (call_param_root_env ps_bind arg_roots R_args)
      (bind_params ps_bind vs s_args) /\
    store_no_shadow (bind_params ps_bind vs s_args) /\
    root_env_no_shadow (call_param_root_env ps_bind arg_roots R_args) /\
    root_env_covers_params ps_bind
      (call_param_root_env ps_bind arg_roots R_args).
Proof.
  intros env s args s_args vs Ω n R Σ ps_typed Σ_args R_args arg_roots
    ps_bind
    Heval_args Hready Htyped_args Hroots Hshadow Hrn Hnodup Hfresh
    Hargs_values.
  destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hready Hroots Hshadow Hrn Htyped_args)
    as [Hroots_args [Hvalues [Hshadow_args Hrn_args]]].
  repeat split.
  - eapply bind_params_store_roots_within_call_param_root_env; eassumption.
  - eapply bind_params_store_no_shadow; eassumption.
  - apply call_param_root_env_no_shadow; assumption.
  - apply call_param_root_env_covers_params.
    + exact Hnodup.
    + rewrite (Forall2_length Hvalues).
      eapply eval_args_values_have_types_length. exact Hargs_values.
Qed.

Lemma captured_call_bind_params_call_param_root_env_ready :
  forall env captured Rcap s_args R_args ps_bind vs Ω arg_roots,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    NoDup (ctx_names (params_ctx ps_bind)) ->
    params_fresh_in_store ps_bind (captured ++ s_args) ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs ps_bind ->
    Forall2 value_roots_within arg_roots vs ->
    store_roots_within (call_param_root_env ps_bind arg_roots
      (Rcap ++ R_args)) (bind_params ps_bind vs (captured ++ s_args)) /\
    store_no_shadow (bind_params ps_bind vs (captured ++ s_args)) /\
    root_env_no_shadow (call_param_root_env ps_bind arg_roots
      (Rcap ++ R_args)) /\
    root_env_covers_params ps_bind
      (call_param_root_env ps_bind arg_roots (Rcap ++ R_args)).
Proof.
  intros env captured Rcap s_args R_args ps_bind vs Ω arg_roots
    Hframe Hnodup Hfresh Hargs_values Hvalue_roots.
  unfold captured_call_frame_ready in Hframe.
  destruct Hframe as [Hcap_ready [Hroots_args [Hshadow_frame
    [Hrn_frame _]]]].
  unfold captured_store_runtime_ready in Hcap_ready.
  destruct Hcap_ready as [_ [Hroots_cap _]].
  assert (Hroots_frame :
    store_roots_within (Rcap ++ R_args) (captured ++ s_args)).
  { eapply store_roots_within_app.
    - exact Hroots_cap.
    - exact Hroots_args.
    - intros x roots Hlookup_args.
      eapply root_env_no_shadow_app_lookup_right_none; eassumption. }
  repeat split.
  - eapply (bind_params_store_roots_within_call_param_root_env
      env Ω (captured ++ s_args) vs ps_bind (Rcap ++ R_args)
      arg_roots); eassumption.
  - eapply bind_params_store_no_shadow; eassumption.
  - apply call_param_root_env_no_shadow; assumption.
  - apply call_param_root_env_covers_params.
    + exact Hnodup.
    + rewrite (Forall2_length Hvalue_roots).
      eapply eval_args_values_have_types_length. exact Hargs_values.
Qed.

Lemma captured_call_frame_args_values_have_types :
  forall env captured Rcap s_args R_args Ω vs ps,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    eval_args_values_have_types env Ω s_args vs ps ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs ps.
Proof.
  intros env captured Rcap s_args R_args Ω vs ps Hframe Hargs.
  unfold captured_call_frame_ready in Hframe.
  destruct Hframe as [_ [_ [Hshadow_frame _]]].
  eapply eval_args_values_have_types_store_preserved.
  - exact Hargs.
  - apply store_ref_targets_preserved_app_right.
    intros x Hin.
    eapply store_no_shadow_app_lookup_right_none; eassumption.
Qed.

Lemma captured_hidden_frame_args_values_have_types :
  forall env captured s_args_hidden s_args Ω vs ps x T hidden,
    s_args_hidden = store_add x T hidden s_args ->
    store_no_shadow (captured ++ s_args_hidden) ->
    ~ In x (store_names s_args) ->
    eval_args_values_have_types env Ω s_args vs ps ->
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs ps.
Proof.
  intros env captured s_args_hidden s_args Ω vs ps x T hidden Hhidden
    Hshadow Hfresh Hargs.
  subst s_args_hidden.
  eapply eval_args_values_have_types_store_preserved.
  - eapply eval_args_values_have_types_store_preserved.
    + exact Hargs.
    + apply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names. exact Hfresh.
  - apply store_ref_targets_preserved_app_right.
    intros y Hin.
    eapply store_no_shadow_app_lookup_right_none.
    + exact Hshadow.
    + exact Hin.
Qed.

Lemma eval_args_store_names_fresh :
  forall env s args s_args vs x,
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    ~ In x (store_names s) ->
    ~ In x (store_names s_args).
Proof.
  intros env s args s_args vs x Heval Hready Hfresh.
  rewrite (proj1 (proj2 preservation_ready_eval_store_names_mutual)
             env s args s_args vs Heval Hready).
  exact Hfresh.
Qed.

Lemma store_no_shadow_app_store_add_right :
  forall captured s_args x T hidden,
    store_no_shadow (captured ++ s_args) ->
    ~ In x (store_names captured) ->
    ~ In x (store_names s_args) ->
    store_no_shadow (captured ++ store_add x T hidden s_args).
Proof.
  intros captured s_args x T hidden Hshadow Hfresh_captured Hfresh_args.
  unfold store_no_shadow in *.
  rewrite store_names_app in *.
  rewrite store_names_add.
  apply NoDup_app_from_Forall.
  - eapply NoDup_app_left_ts. exact Hshadow.
  - constructor.
    + exact Hfresh_args.
    + eapply NoDup_app_right_ts. exact Hshadow.
  - apply Forall_forall. intros y Hy Hin.
    simpl in Hin. destruct Hin as [Hyx | Hy_args].
    + subst y. contradiction.
    + eapply (NoDup_app_not_in_right_ts
                (store_names captured) (store_names s_args) y Hshadow);
        eassumption.
Qed.

Lemma captured_call_frame_ready_store_add_right :
  forall env captured Rcap s_args R_args x T hidden,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    value_roots_within [] hidden ->
    ~ In x (store_names captured) ->
    ~ In x (store_names s_args) ->
    root_env_lookup x R_args = None ->
    captured_call_frame_ready env captured Rcap
      (store_add x T hidden s_args) (root_env_add x [] R_args).
Proof.
  intros env captured Rcap s_args R_args x T hidden Hframe Hnamed_args
    Hkeys_args Hhidden_roots Hfresh_cap Hfresh_args Hlookup_args_x.
  unfold captured_call_frame_ready in *.
  destruct Hframe as [Hcap_ready [Hroots_args [Hshadow_frame
    [Hrn_frame [Hnamed_frame Hkeys_frame]]]]].
  unfold captured_store_runtime_ready in Hcap_ready.
  destruct Hcap_ready as [Htyped_cap [Hroots_cap [Hshadow_cap
    [Hrn_cap [Hnamed_cap Hkeys_cap]]]]].
  assert (Hlookup_cap_x : root_env_lookup x Rcap = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_frame.
    eapply NoDup_app_right_ts. exact Hrn_frame. }
  assert (Hroots_hidden_args :
    store_roots_within (root_env_add x [] R_args)
      (store_add x T hidden s_args)).
  { eapply store_add_roots_within; eassumption. }
  assert (Hshadow_hidden :
    store_no_shadow (captured ++ store_add x T hidden s_args)).
  { eapply store_no_shadow_app_store_add_right; eassumption. }
  assert (Hrn_hidden_args :
    root_env_no_shadow (root_env_add x [] R_args)).
  { apply root_env_no_shadow_add; assumption. }
  assert (Hrn_hidden_frame :
    root_env_no_shadow (Rcap ++ root_env_add x [] R_args)).
  { apply root_env_no_shadow_app; try assumption.
    intros y.
    destruct (root_env_lookup y Rcap) as [roots_cap |] eqn:Hlookup_cap.
    - right.
      unfold root_env_add. simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      + apply ident_eqb_eq in Hyx. subst y.
        rewrite Hlookup_cap_x in Hlookup_cap. discriminate.
      + destruct (root_env_lookup y R_args) as [roots_args |]
          eqn:Hlookup_args; try reflexivity.
        pose proof (root_env_no_shadow_app_lookup_right_none
                      Rcap R_args y roots_args Hrn_frame Hlookup_args)
          as Hnone_cap.
        rewrite Hlookup_cap in Hnone_cap. discriminate.
    - left. reflexivity. }
  assert (Hnamed_hidden_args :
    root_env_store_roots_named (root_env_add x [] R_args)
      (store_add x T hidden s_args)).
  { eapply root_env_store_roots_named_add_env_store_add.
    - exact Hnamed_args.
    - apply root_set_store_roots_named_nil. }
  assert (Hkeys_hidden_args :
    root_env_store_keys_named (root_env_add x [] R_args)
      (store_add x T hidden s_args)).
  { eapply root_env_store_keys_named_add_env_store_add.
    exact Hkeys_args. }
  split.
  - repeat split; assumption.
  - split; [exact Hroots_hidden_args|].
    split; [exact Hshadow_hidden|].
    split; [exact Hrn_hidden_frame|].
    split.
    + eapply root_env_store_roots_named_app; try eassumption.
    intros y roots Hlookup_hidden.
    unfold root_env_add in Hlookup_hidden. simpl in Hlookup_hidden.
    destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        inversion Hlookup_hidden; subst.
        exact Hlookup_cap_x.
      * destruct (root_env_lookup y R_args) as [roots_args |]
          eqn:Hlookup_args; try discriminate.
        exact (root_env_no_shadow_app_lookup_right_none
          Rcap R_args y roots_args Hrn_frame Hlookup_args).
    + apply root_env_store_keys_named_app; assumption.
Qed.

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
