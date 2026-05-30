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

Lemma root_env_store_roots_named_weaken_store_names :
  forall R s s',
    root_env_store_roots_named R s ->
    (forall x, In x (store_names s) -> In x (store_names s')) ->
    root_env_store_roots_named R s'.
Proof.
  unfold root_env_store_roots_named.
  intros R s s' Hnamed Hsub x roots z Hlookup Hin.
  apply Hsub. eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_weaken_store_names :
  forall R s s',
    root_env_store_keys_named R s ->
    (forall x, In x (store_names s) -> In x (store_names s')) ->
    root_env_store_keys_named R s'.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros R s s' Hkeys Hsub x Hin.
  apply Hsub. apply Hkeys. exact Hin.
Qed.

Lemma root_set_store_roots_named_weaken_store_names :
  forall roots s s',
    root_set_store_roots_named roots s ->
    (forall x, In x (store_names s) -> In x (store_names s')) ->
    root_set_store_roots_named roots s'.
Proof.
  unfold root_set_store_roots_named.
  intros roots s s' Hnamed Hsub x Hin.
  apply Hsub. apply Hnamed. exact Hin.
Qed.

Lemma root_env_store_roots_named_remove_params :
  forall ps R s,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named (root_env_remove_params ps R) s.
Proof.
  induction ps as [| p ps IH]; intros R s Hrn Hnamed; simpl.
  - exact Hnamed.
  - apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + eapply root_env_store_roots_named_remove_env; eassumption.
Qed.

Lemma root_env_store_keys_named_remove_params :
  forall ps R s,
    root_env_store_keys_named R s ->
    root_env_store_keys_named (root_env_remove_params ps R) s.
Proof.
  induction ps as [| p ps IH]; intros R s Hkeys; simpl.
  - exact Hkeys.
  - apply IH.
    unfold root_env_store_keys_named in *.
    apply root_env_keys_named_remove. exact Hkeys.
Qed.

Lemma root_env_store_roots_named_call_param_bind_params :
  forall env Ω s vs ps arg_roots R_tail,
    eval_args_values_have_types env Ω s vs ps ->
    Forall (fun roots => root_set_store_roots_named roots s) arg_roots ->
    root_env_no_shadow R_tail ->
    root_env_store_roots_named R_tail s ->
    root_env_store_roots_named
      (call_param_root_env ps arg_roots R_tail) (bind_params ps vs s).
Proof.
  intros env Ω s vs ps arg_roots R_tail Hargs Hroots Hrn Hnamed.
  unfold call_param_root_env.
  revert arg_roots R_tail Hroots Hrn Hnamed.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Htail IH];
    intros arg_roots R_tail Hroots Hrn Hnamed; simpl.
  - eapply root_env_store_roots_named_weaken_store_names.
    + exact Hnamed.
    + intros x Hin. exact Hin.
  - destruct arg_roots as [| roots arg_roots].
    + eapply root_env_store_roots_named_weaken_store_names.
      * eapply (root_env_store_roots_named_remove_params (p :: ps)); eassumption.
      * intros x Hin. simpl. right.
        rewrite (store_names_bind_params env Ω s vs ps Htail).
        apply in_or_app. right. exact Hin.
    + inversion Hroots as [| ? ? Hroots_head Hroots_tail]; subst.
      assert (Hroots_head_bind :
        root_set_store_roots_named roots (bind_params ps vs s)).
      { eapply root_set_store_roots_named_weaken_store_names.
        - exact Hroots_head.
        - intros x Hin.
          rewrite (store_names_bind_params env Ω s vs ps Htail).
          apply in_or_app. right. exact Hin. }
      eapply root_env_store_roots_named_add_env_store_add.
      * eapply IH.
        -- exact Hroots_tail.
        -- apply root_env_no_shadow_remove. exact Hrn.
        -- eapply root_env_store_roots_named_remove_env; eassumption.
      * exact Hroots_head_bind.
Qed.

Lemma root_env_store_keys_named_call_param_bind_params :
  forall env Ω s vs ps arg_roots R_tail,
    eval_args_values_have_types env Ω s vs ps ->
    root_env_store_keys_named R_tail s ->
    root_env_store_keys_named
      (call_param_root_env ps arg_roots R_tail) (bind_params ps vs s).
Proof.
  intros env Ω s vs ps arg_roots R_tail Hargs Hkeys.
  unfold call_param_root_env.
  revert arg_roots R_tail Hkeys.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Htail IH];
    intros arg_roots R_tail Hkeys; simpl.
  - exact Hkeys.
  - destruct arg_roots as [| roots arg_roots].
    + eapply root_env_store_keys_named_weaken_store_names.
      * eapply (root_env_store_keys_named_remove_params (p :: ps)). exact Hkeys.
      * intros x Hin. simpl. right.
        rewrite (store_names_bind_params env Ω s vs ps Htail).
        apply in_or_app. right. exact Hin.
    + eapply root_env_store_keys_named_add_env_store_add.
      eapply IH.
      unfold root_env_store_keys_named in *.
      apply root_env_keys_named_remove. exact Hkeys.
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

Lemma captured_call_bind_params_call_param_root_env_ready_in_frame :
  forall env captured Rcap s_args R_args ps_bind vs Ω arg_roots,
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
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
  unfold captured_call_frame_ready_in_frame in Hframe.
  destruct Hframe as [Hcap_ready [Hroots_args [Hshadow_frame
    [Hrn_frame _]]]].
  unfold captured_store_runtime_ready_in_frame in Hcap_ready.
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

Lemma captured_call_frame_args_values_have_types_in_frame :
  forall env captured Rcap s_args R_args Ω vs ps,
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    eval_args_values_have_types env Ω s_args vs ps ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs ps.
Proof.
  intros env captured Rcap s_args R_args Ω vs ps Hframe Hargs.
  unfold captured_call_frame_ready_in_frame in Hframe.
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

Lemma captured_closure_roots_within_capture_store_root_sets :
  forall fname captured,
    Forall
      (fun se =>
        value_roots_within (capture_value_roots (se_val se)) (se_val se))
      captured ->
    value_roots_within (root_sets_union (capture_store_root_sets captured))
      (VClosure fname captured).
Proof.
  intros fname captured Hvalues.
  constructor.
  intros root Hexclude.
  induction Hvalues as [| se rest Hvalue _ IH]; simpl in *.
  - constructor.
  - constructor.
    + destruct se as [sx sT sv sst]. simpl in *.
      constructor.
      eapply value_roots_exclude_root.
      * exact Hvalue.
      * unfold roots_exclude in *.
        intros Hin. apply Hexclude. apply root_set_union_in_l. exact Hin.
    + apply IH.
      unfold roots_exclude in *.
      intros Hin. apply Hexclude. apply root_set_union_in_r. exact Hin.
Qed.

Lemma capture_store_root_sets_union_store_roots_named_in_store_runtime :
  forall env target captured,
    Forall2 (store_entry_typed env target)
      captured (sctx_of_store captured) ->
    root_set_store_roots_named (root_sets_union (capture_store_root_sets captured))
      target.
Proof.
  intros env target captured Htyped.
  apply root_sets_store_roots_named_union.
  induction Htyped as [| se ce captured_tail Σ_tail Hentry _ IH].
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [_ Hvalue]]].
    simpl. constructor.
    + eapply capture_value_roots_store_roots_named. exact Hvalue.
    + exact IH.
Qed.

Lemma captured_call_frame_ready_in_frame_store_add_right_roots :
  forall env captured Rcap s_args R_args x T hidden roots,
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    root_set_store_roots_named roots
      (captured ++ store_add x T hidden s_args) ->
    root_env_store_keys_named R_args s_args ->
    value_roots_within roots hidden ->
    ~ In x (store_names captured) ->
    ~ In x (store_names s_args) ->
    root_env_lookup x R_args = None ->
    captured_call_frame_ready_in_frame env captured Rcap
      (store_add x T hidden s_args) (root_env_add x roots R_args).
Proof.
  intros env captured Rcap s_args R_args x T hidden roots Hframe
    Hhidden_named Hkeys_args Hhidden_roots Hfresh_cap Hfresh_args
    Hlookup_args_x.
  unfold captured_call_frame_ready_in_frame in *.
  destruct Hframe as [Hcap_ready [Hroots_args [Hshadow_frame
    [Hrn_frame [Hnamed_frame Hkeys_frame]]]]].
  unfold captured_store_runtime_ready_in_frame in Hcap_ready.
  destruct Hcap_ready as [Htyped_cap [Hroots_cap [Hshadow_cap
    [Hrn_cap [Hnamed_cap Hkeys_cap]]]]].
  assert (Hin_hidden :
    forall z,
      In z (store_names (captured ++ s_args)) ->
      In z (store_names (captured ++ store_add x T hidden s_args))).
  { intros z Hin.
    rewrite store_names_app in *.
    apply in_app_or in Hin.
    apply in_or_app.
    destruct Hin as [Hin | Hin].
    - left. exact Hin.
    - right. simpl. right. exact Hin. }
  assert (Hlookup_cap_x : root_env_lookup x Rcap = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_frame.
    eapply NoDup_app_right_ts. exact Hrn_frame. }
  assert (Hroots_hidden_args :
    store_roots_within (root_env_add x roots R_args)
      (store_add x T hidden s_args)).
  { eapply store_add_roots_within; eassumption. }
  assert (Hshadow_hidden :
    store_no_shadow (captured ++ store_add x T hidden s_args)).
  { eapply store_no_shadow_app_store_add_right; eassumption. }
  assert (Hrn_hidden_args :
    root_env_no_shadow (root_env_add x roots R_args)).
  { apply root_env_no_shadow_add; assumption. }
  assert (Hrn_hidden_frame :
    root_env_no_shadow (Rcap ++ root_env_add x roots R_args)).
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
  assert (Hnamed_hidden_frame :
    root_env_store_roots_named (Rcap ++ root_env_add x roots R_args)
      (captured ++ store_add x T hidden s_args)).
  { unfold root_env_store_roots_named in *.
    intros y roots_y z Hlookup Hin.
    destruct (root_env_lookup y Rcap) as [roots_cap |] eqn:Hlookup_cap.
    - rewrite (root_env_lookup_app_left y Rcap (root_env_add x roots R_args)
        roots_cap Hlookup_cap) in Hlookup.
      inversion Hlookup; subst roots_cap.
      apply Hin_hidden.
      eapply Hnamed_frame.
      * apply root_env_lookup_app_left. exact Hlookup_cap.
      * exact Hin.
    - rewrite (root_env_lookup_app_right y Rcap
        (root_env_add x roots R_args) Hlookup_cap) in Hlookup.
      unfold root_env_add in Hlookup. simpl in Hlookup.
      destruct (ident_eqb y x) eqn:Hyx.
      + inversion Hlookup; subst roots_y.
        eapply Hhidden_named. exact Hin.
      + destruct (root_env_lookup y R_args) as [roots_args |]
          eqn:Hlookup_args; try discriminate.
        inversion Hlookup; subst roots_args.
        apply Hin_hidden.
        eapply Hnamed_frame.
        * rewrite (root_env_lookup_app_right y Rcap R_args Hlookup_cap).
          exact Hlookup_args.
        * exact Hin. }
  assert (Hkeys_hidden_args :
    root_env_store_keys_named (root_env_add x roots R_args)
      (store_add x T hidden s_args)).
  { eapply root_env_store_keys_named_add_env_store_add.
    exact Hkeys_args. }
  assert (Hpres_frame_hidden :
    store_ref_targets_preserved env (captured ++ s_args)
      (captured ++ store_add x T hidden s_args)).
  { unfold store_ref_targets_preserved.
    intros y path se v Ty Hlookup Hvalue Htype.
    exists se, v. repeat split; try assumption.
    destruct (store_lookup y captured) as [se_cap |] eqn:Hlookup_cap.
    - rewrite (store_lookup_app_some y captured s_args se_cap Hlookup_cap)
        in Hlookup.
      inversion Hlookup; subst se_cap.
      apply store_lookup_app_some. exact Hlookup_cap.
    - rewrite (store_lookup_app_none y captured s_args Hlookup_cap)
        in Hlookup.
      rewrite (store_lookup_app_none y captured
        (store_add x T hidden s_args) Hlookup_cap).
      simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      + apply ident_eqb_eq in Hyx. subst y.
        rewrite (store_lookup_not_in_names x s_args Hfresh_args) in Hlookup.
        discriminate.
      + exact Hlookup. }
  assert (Htyped_cap_hidden :
    Forall2 (store_entry_typed env
      (captured ++ store_add x T hidden s_args))
      captured (sctx_of_store captured)).
  { eapply store_typed_entries_store_preserved; eassumption. }
  split.
  - unfold captured_store_runtime_ready_in_frame.
    split; [exact Htyped_cap_hidden|].
    split; [exact Hroots_cap|].
    split; [exact Hshadow_cap|].
    split; [exact Hrn_cap|].
    split.
    + eapply root_env_store_roots_named_weaken_store; eassumption.
    + exact Hkeys_cap.
  - split; [exact Hroots_hidden_args|].
    split; [exact Hshadow_hidden|].
    split; [exact Hrn_hidden_frame|].
    split.
    + exact Hnamed_hidden_frame.
    + apply root_env_store_keys_named_app; assumption.
Qed.

Lemma captured_call_frame_ready_in_frame_store_add_right :
  forall env captured Rcap s_args R_args x T hidden hidden_roots,
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    value_roots_within hidden_roots hidden ->
    root_set_store_roots_named hidden_roots
      (captured ++ store_add x T hidden s_args) ->
    ~ In x (store_names captured) ->
    ~ In x (store_names s_args) ->
    root_env_lookup x R_args = None ->
    captured_call_frame_ready_in_frame env captured Rcap
      (store_add x T hidden s_args)
      (root_env_add x hidden_roots R_args).
Proof.
  intros env captured Rcap s_args R_args x T hidden hidden_roots Hframe
    Hnamed_args Hkeys_args Hhidden_roots Hhidden_named Hfresh_cap
    Hfresh_args Hlookup_args_x.
  eapply captured_call_frame_ready_in_frame_store_add_right_roots;
    eassumption.
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

Lemma copy_capture_store_as_captured_call_frame_ready_with_env :
  forall Ω env s Σ captures caps captured env_lt captured_tys
      s_args R_args,
    store_typed env s Σ ->
    store_ref_targets_preserved env s (captured ++ s_args) ->
    NoDup (ctx_names (params_ctx caps)) ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    copy_capture_store_as captures caps s = Some captured ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    (forall x, In x (store_names captured) -> ~ In x (store_names s_args)) ->
    (forall x, root_env_lookup x (capture_store_root_env captured) = None \/
      root_env_lookup x R_args = None) ->
    captured_call_frame_ready_in_frame env captured
      (capture_store_root_env captured) s_args R_args.
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys s_args R_args
    Hstore Hpres Hnodup Hcheck Hcopy Hroots_args Hshadow_args Hrn_args
    Hnamed_args Hkeys_args Hstore_disj Hroot_disj.
  pose proof
    (copy_capture_store_as_captured_store_runtime_ready_in_frame_with_env
      Ω env s Σ captures caps captured env_lt captured_tys s_args
      Hstore Hpres Hnodup Hcopy Hcheck) as Hcap_ready.
  eapply captured_call_frame_ready_in_frame_compose; eassumption.
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

Lemma eval_make_closure_exact_captured_call_frame_params_ready_auto_with_env :
  forall env (Ω : outlives_ctx) s Σ fname captures captured fdef fcall
      used' args s_args vs R_args env_lt captured_tys,
    store_typed env s Σ ->
    store_ref_targets_preserved env s (captured ++ s_args) ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    eval_args env s args s_args vs ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    captured_call_frame_params_ready_in_frame env captured
      (capture_store_root_env captured) s_args R_args
      (fn_captures fcall).
Proof.
  intros env Ω s Σ fname captures captured fdef fcall used' args s_args vs
    R_args env_lt captured_tys Hstore Hpres Heval_make Hlookup Hrename
    Hcheck Hnodup Hready_args Heval_args Hroots_args Hshadow_args Hrn_args
    Hnamed_args Hkeys_args.
  dependent destruction Heval_make.
  assert (Hsame : fdef0 = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef0.
  pose proof
    (check_make_closure_captures_exact_sctx_with_env_params_fresh_in_store
      env Ω s Σ captures (fn_captures fdef) env_lt captured_tys
      Hstore Hcheck) as Hfresh_caps.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                env s args s_args vs Heval_args Hready_args)
    as Hargs_names.
  assert (Hstore_disj :
    forall x, In x (store_names captured) -> ~ In x (store_names s_args)).
  { intros x Hin_captured Hin_args.
    rewrite (copy_capture_store_as_store_names captures (fn_captures fdef)
               s captured H0) in Hin_captured.
    rewrite Hargs_names in Hin_args.
    exact (Hfresh_caps x Hin_captured Hin_args). }
  assert (Hroot_disj :
    forall x,
      root_env_lookup x (capture_store_root_env captured) = None \/
      root_env_lookup x R_args = None).
  { intros x.
    destruct (root_env_lookup x (capture_store_root_env captured))
      as [roots |] eqn:Hlookup_cap.
    - right.
      eapply root_env_store_keys_named_lookup_excludes_name.
      + exact Hkeys_args.
      + intros Hin_args.
        eapply Hstore_disj.
        * rewrite <- capture_store_root_env_names.
          eapply root_env_lookup_some_in_names. exact Hlookup_cap.
        * exact Hin_args.
    - left. reflexivity. }
  pose proof
    (copy_capture_store_as_captured_call_frame_ready_with_env
      Ω env s Σ captures (fn_captures fdef) captured env_lt captured_tys
      s_args R_args Hstore Hpres Hnodup Hcheck H0 Hroots_args
      Hshadow_args Hrn_args Hnamed_args Hkeys_args Hstore_disj Hroot_disj)
    as Hframe_ready.
  split.
  - exact Hframe_ready.
  - rewrite (alpha_rename_fn_def_captures
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename).
    eapply copy_capture_store_exact_with_env_params_store_typed_in_frame;
      eassumption.
Qed.
