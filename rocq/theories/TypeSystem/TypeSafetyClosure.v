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

Lemma copy_capture_store_as_captured_call_frame_ready :
  forall Ω env s Σ captures caps captured captured_tys args s_args vs R_args,
    store_typed env s Σ ->
    NoDup (ctx_names (params_ctx caps)) ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    copy_capture_store_as captures caps s = Some captured ->
    preservation_ready_args args ->
    eval_args env s args s_args vs ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    captured_call_frame_ready env captured
      (empty_root_env_for_store captured) s_args R_args.
Proof.
  intros Ω env s Σ captures caps captured captured_tys args s_args vs R_args
    Hstore Hnodup Hcheck Hcopy Hready_args Heval_args Hroots_args
    Hshadow_args Hrn_args Hnamed_args Hkeys_args.
  pose proof
    (copy_capture_store_as_captured_store_runtime_ready
      Ω env s Σ captures caps captured captured_tys
      Hstore Hnodup Hcopy Hcheck) as Hcap_ready.
  pose proof
    (check_make_closure_captures_exact_sctx_params_fresh_in_store
      env Ω s Σ captures caps captured_tys Hstore Hcheck) as Hfresh_caps.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                env s args s_args vs Heval_args Hready_args)
    as Hargs_names.
  assert (Hstore_disj :
    forall x, In x (store_names captured) -> ~ In x (store_names s_args)).
  { intros x Hin_captured Hin_args.
    rewrite (copy_capture_store_as_store_names captures caps s captured Hcopy)
      in Hin_captured.
    rewrite Hargs_names in Hin_args.
    exact (Hfresh_caps x Hin_captured Hin_args). }
  eapply captured_call_frame_ready_compose; try eassumption.
  intros x.
  destruct (root_env_lookup x (empty_root_env_for_store captured))
    as [roots |] eqn:Hlookup_cap.
  - right.
    destruct (root_env_lookup x R_args) as [roots_args |] eqn:Hlookup_args;
      try reflexivity.
    exfalso.
    eapply Hstore_disj.
    + rewrite <- root_env_names_empty_root_env_for_store.
      eapply root_env_lookup_some_in_names. exact Hlookup_cap.
    + apply Hkeys_args.
      eapply root_env_lookup_some_in_names. exact Hlookup_args.
  - left. reflexivity.
Qed.

Lemma eval_make_closure_exact_captured_call_frame_params_ready :
  forall env (Ω : outlives_ctx) s Σ fname captures captured fdef fcall
      used' Rcap s_args R_args captured_tys,
    store_typed env s Σ ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures (fn_captures fdef) =
      infer_ok captured_tys ->
    captured_call_frame_ready env captured Rcap s_args R_args ->
    captured_call_frame_params_ready env captured Rcap s_args R_args
      (fn_captures fcall).
Proof.
  intros env Ω s Σ fname captures captured fdef fcall used' Rcap s_args
    R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck
    Hframe_ready.
  dependent destruction Heval_make.
  assert (Hsame : fdef0 = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef0.
  split.
  - exact Hframe_ready.
  - rewrite (alpha_rename_fn_def_captures
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename).
    eapply copy_capture_store_exact_params_store_typed.
    + exact Hstore.
    + unfold captured_call_frame_ready, captured_store_runtime_ready
        in Hframe_ready.
      exact (proj1 (proj1 Hframe_ready)).
    + exact H0.
    + exact Hcheck.
Qed.

Lemma eval_make_closure_exact_captured_call_frame_params_ready_auto :
  forall env (Ω : outlives_ctx) s Σ fname captures captured fdef fcall
      used' args s_args vs R_args captured_tys,
    store_typed env s Σ ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures (fn_captures fdef) =
      infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    eval_args env s args s_args vs ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args R_args
      (fn_captures fcall).
Proof.
  intros env Ω s Σ fname captures captured fdef fcall used' args s_args vs
    R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck Hnodup
    Hready_args Heval_args Hroots_args Hshadow_args Hrn_args Hnamed_args
    Hkeys_args.
  dependent destruction Heval_make.
  assert (Hsame : fdef0 = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef0.
  pose proof
    (copy_capture_store_as_captured_call_frame_ready
      Ω env s Σ captures (fn_captures fdef) captured captured_tys args
      s_args vs R_args Hstore Hnodup Hcheck H0 Hready_args Heval_args
      Hroots_args Hshadow_args Hrn_args Hnamed_args Hkeys_args)
    as Hframe_ready.
  split.
  - exact Hframe_ready.
  - rewrite (alpha_rename_fn_def_captures
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename).
    eapply copy_capture_store_exact_params_store_typed.
    + exact Hstore.
    + unfold captured_call_frame_ready, captured_store_runtime_ready
        in Hframe_ready.
      exact (proj1 (proj1 Hframe_ready)).
    + exact H0.
    + exact Hcheck.
Qed.

Lemma eval_make_closure_captured_call_runtime_args_ready_core :
  forall env Ω captured fdef fcall used' s_args vs R_args Σ_args
      arg_roots,
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args R_args
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fdef) ->
    Forall2 value_roots_within arg_roots vs ->
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
  intros env Ω captured fdef fcall used' s_args vs R_args Σ_args
    arg_roots Hrename Hframe_params_ready Hstore_args Hargs_fdef_frame
    Hvalue_roots.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_fcall :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (captured_call_bind_params_call_param_root_env_ready
      env captured (empty_root_env_for_store captured) s_args R_args
      (fn_params fcall) vs Ω arg_roots Hframe_ready Hnodup_fcall
      Hfresh_fcall Hargs_fcall Hvalue_roots)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  split.
  - split; assumption.
  - split; [exact Hstore_args |].
    split; [exact Hargs_fcall |].
    split; [exact Hvalue_roots |].
    split; [exact Hroots_bind |].
    split; [exact Hshadow_bind |].
    split; [exact Hrn_bind | exact Hcover_bind].
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_core :
  forall env Ω fname captured fdef fcall used' s_args_hidden s_args vs
      R_args Σ_args arg_roots x T,
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    captured_call_frame_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω s_args vs (fn_params fdef) ->
    Forall2 value_roots_within arg_roots vs ->
    ~ In x (store_names s_args) ->
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
  intros env Ω fname captured fdef fcall used' s_args_hidden s_args vs
    R_args Σ_args arg_roots x T Hhidden Hrename Hframe_hidden
    Hframe_params_ready Hstore_args Hargs_fdef_sargs Hvalue_roots
    Hfresh_s_args.
  assert (Hshadow_hidden_frame :
    store_no_shadow (captured ++ s_args_hidden)).
  { unfold captured_call_frame_ready in Hframe_hidden.
    destruct Hframe_hidden as [_ [_ [Hshadow_hidden_frame _]]].
    exact Hshadow_hidden_frame. }
  pose proof
    (captured_hidden_frame_args_values_have_types
      env captured s_args_hidden s_args Ω vs (fn_params fdef) x T
      (VClosure fname captured) Hhidden Hshadow_hidden_frame Hfresh_s_args
      Hargs_fdef_sargs) as Hargs_fdef_hidden.
  pose proof (alpha_rename_fn_def_shape
                (store_names (captured ++ s_args_hidden)) fdef fcall used'
                Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_fcall :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args_hidden)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (captured_call_bind_params_call_param_root_env_ready
      env captured (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_params fcall) vs Ω arg_roots
      Hframe_hidden Hnodup_fcall Hfresh_fcall Hargs_fcall Hvalue_roots)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  split.
  - exact Hframe_params_ready.
  - split; [exact Hstore_args |].
    split; [exact Hargs_fcall |].
    split; [exact Hvalue_roots |].
    split; [exact Hroots_bind |].
    split; [exact Hshadow_bind |].
    split; [exact Hrn_bind | exact Hcover_bind].
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

Lemma eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core :
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
