From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCore.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCapture.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma copy_capture_store_exact_params_store_typed :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    captured_store_typed env captured ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    captured_params_store_typed env captured caps.
Proof.
  intros Ω env s Σ captures caps captured captured_tys
    Hstore Hcaptured Hcopy Hcheck.
  eapply captured_store_typed_as_params.
  - exact Hcaptured.
  - eapply (copy_capture_store_exact_sctx_of_store
      Ω env s Σ captures caps captured captured_tys); eassumption.
Qed.

Lemma copy_capture_store_as_store_names :
  forall captures caps s captured,
    copy_capture_store_as captures caps s = Some captured ->
    store_names captured = ctx_names (params_ctx caps).
Proof.
  induction captures as [| x captures IH]; intros caps s captured Hcopy;
    destruct caps as [| cap caps]; simpl in Hcopy; try discriminate.
  - injection Hcopy as <-. reflexivity.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    simpl. rewrite (IH caps s captured_rest Hcopy_rest). reflexivity.
Qed.

Lemma store_names_app_hfb :
  forall s1 s2,
    store_names (s1 ++ s2) = store_names s1 ++ store_names s2.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma store_roots_within_lookup_value_hfb :
  forall R s x se roots,
    store_roots_within R s ->
    store_lookup x s = Some se ->
    root_env_lookup x R = Some roots ->
    value_roots_within roots (se_val se).
Proof.
  intros R s x se roots Hwithin.
  revert x se roots.
  induction Hwithin as [R | R se_head rest Hentry Hrest IH];
    intros x se roots Hlookup_store Hlookup_roots;
    simpl in Hlookup_store; try discriminate.
  destruct se_head as [sx sT sv sst].
  inversion Hentry as [R0 sx0 sT0 sv0 sst0 roots0 Hlookup_head Hvalue];
    subst.
  simpl in Hlookup_store.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    inversion Hlookup_store; subst se.
    rewrite Hlookup_roots in Hlookup_head.
    inversion Hlookup_head; subst roots0.
    exact Hvalue.
  - eapply IH; eassumption.
Qed.

Lemma store_roots_within_weaken_lookup_hfb :
  forall R R' s,
    store_roots_within R s ->
    (forall x roots,
      In x (store_names s) ->
      root_env_lookup x R = Some roots ->
      root_env_lookup x R' = Some roots) ->
    store_roots_within R' s.
Proof.
  intros R R' s Hroots.
  induction Hroots as [R | R se rest Hentry Hrest IH]; intros Hpreserve.
  - constructor.
  - inversion Hentry as [R0 sx sT sv sst roots Hlookup Hvalue]; subst.
    constructor.
    + econstructor.
      * apply Hpreserve.
        -- simpl. left. reflexivity.
        -- exact Hlookup.
      * exact Hvalue.
    + apply IH.
      intros x roots_x Hname Hlookup_x.
      apply Hpreserve.
      * simpl. right. exact Hname.
      * exact Hlookup_x.
Qed.

Lemma copy_capture_store_as_roots_within_copied_roots :
  forall captures caps s captured R Rcap,
    copy_capture_store_as captures caps s = Some captured ->
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    store_roots_within R s ->
    store_roots_within Rcap captured.
Proof.
  induction captures as [| x captures IH]; intros caps s captured R Rcap
    Hcopy_store Hcopy_roots Hnodup Hwithin;
    destruct caps as [| cap caps]; simpl in Hcopy_store, Hcopy_roots;
    try discriminate.
  - injection Hcopy_store as <-. constructor.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup_store;
      try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_store_tail; try discriminate.
    destruct (root_env_lookup x R) as [roots |] eqn:Hlookup_roots;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Hcopy_roots_tail; try discriminate.
    injection Hcopy_store as <-.
    injection Hcopy_roots as <-.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    constructor.
    + econstructor.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * eapply store_roots_within_lookup_value_hfb; eassumption.
    + eapply store_roots_within_weaken_lookup_hfb.
      * eapply IH; eassumption.
      * intros y roots_y Hin Hlookup_y.
        simpl.
        destruct (ident_eqb y (param_name cap)) eqn:Heq.
        -- apply ident_eqb_eq in Heq. subst y.
           exfalso. apply Hnotin.
           rewrite <- (copy_capture_store_as_store_names
             captures caps s captured_rest Hcopy_store_tail).
           exact Hin.
        -- exact Hlookup_y.
Qed.

Lemma copy_capture_roots_store_as_keys_named :
  forall captures caps R Rcap s captured,
    copy_capture_roots_as captures caps R = Some Rcap ->
    copy_capture_store_as captures caps s = Some captured ->
    root_env_store_keys_named Rcap captured.
Proof.
  intros captures caps R Rcap s captured Hcopy_roots Hcopy_store.
  unfold root_env_store_keys_named, root_env_keys_named.
  rewrite (copy_capture_roots_as_names captures caps R Rcap Hcopy_roots).
  rewrite (copy_capture_store_as_store_names captures caps s captured
    Hcopy_store).
  intros x Hin. exact Hin.
Qed.

Lemma copy_capture_roots_as_store_roots_named_in_frame :
  forall captures caps R Rcap s captured frame,
    copy_capture_store_as captures caps s = Some captured ->
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    root_env_store_roots_named R frame ->
    root_env_store_roots_named Rcap (captured ++ frame).
Proof.
  induction captures as [| x captures IH]; intros caps R Rcap s captured
    frame Hcopy_store Hcopy_roots Hnodup Hnamed;
    destruct caps as [| cap caps]; simpl in Hcopy_store, Hcopy_roots;
    try discriminate.
  - injection Hcopy_store as <-. injection Hcopy_roots as <-.
    unfold root_env_store_roots_named.
    intros y roots z Hlookup _. simpl in Hlookup. discriminate.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup_store;
      try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_store_tail; try discriminate.
    destruct (root_env_lookup x R) as [roots_x |] eqn:Hlookup_roots;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Hcopy_roots_tail; try discriminate.
    injection Hcopy_store as <-.
    injection Hcopy_roots as <-.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    unfold root_env_store_roots_named in *.
    intros y roots z Hlookup Hin.
    simpl in Hlookup.
    destruct (ident_eqb y (param_name cap)) eqn:Heq.
    + injection Hlookup as <-.
      simpl. right. rewrite store_names_app_hfb. apply in_or_app. right.
      eapply Hnamed; eassumption.
    + simpl. right.
      eapply IH.
      * exact Hcopy_store_tail.
      * exact Hcopy_roots_tail.
      * exact Hnodup_tail.
      * exact Hnamed.
      * exact Hlookup.
      * exact Hin.
Qed.

Lemma copy_capture_store_as_captured_entries_typed_rootless :
  forall Ω env s_target s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    Forall2 (store_entry_typed env s_target) captured (sctx_of_store captured) /\
    Forall (fun se => value_roots_within [] (se_val se)) captured.
Proof.
  intros Ω env s_target s Σ captures.
  revert s_target.
  induction captures as [| x captures IH]; intros s_target caps captured captured_tys
    Hstore Hcopy Hcheck;
    destruct caps as [| cap caps]; simpl in Hcopy, Hcheck; try discriminate.
  - injection Hcopy as <-.
    split; constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest_tys | err] eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [Hrefines Hvalue]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    assert (Hrootless_T : runtime_rootless_ty env T).
    { apply capture_ref_free_ty_b_runtime_rootless. exact Href_free. }
    assert (Hrootless : runtime_rootless_ty env (se_ty se)).
    { rewrite <- H0. exact Hrootless_T. }
    assert (Hvalue_target : value_has_type env s_target (se_val se) (se_ty se)).
    { eapply value_has_type_runtime_rootless_store_any.
      - exact Hvalue.
      - exact Hrootless. }
    destruct (IH s_target caps captured_rest captured_rest_tys
                Hstore Hcopy_rest Hrest_check)
      as [Htyped_tail Hroots_tail].
    split.
    + simpl. constructor.
      * exact (conj eq_refl
          (conj eq_refl
            (conj (binding_state_refines_refl (se_state se))
              Hvalue_target))).
      * exact Htyped_tail.
    + simpl. constructor.
      * eapply value_has_type_runtime_rootless_empty_roots.
        -- exact Hvalue_target.
        -- exact Hrootless.
      * exact Hroots_tail.
Qed.

Lemma copy_capture_store_as_captured_entries_typed_with_env_base_preserved :
  forall Ω env s_target s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    store_ref_targets_preserved env s s_target ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env_base env Ω Σ captures caps =
      infer_ok captured_tys ->
    Forall2 (store_entry_typed env s_target) captured (sctx_of_store captured).
Proof.
  intros Ω env s_target s Σ captures.
  induction captures as [| x captures IH]; intros caps captured captured_tys
    Hstore Hpres Hcopy Hcheck;
    destruct caps as [| cap caps]; simpl in Hcopy, Hcheck; try discriminate.
  - injection Hcopy as <-. constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest_tys | err]
      eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    injection Hcheck as <-.
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [Hrefines Hvalue]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    simpl. constructor.
    + exact (conj eq_refl
        (conj eq_refl
          (conj (binding_state_refines_refl (se_state se))
            (value_has_type_store_preserved env s (se_val se) (se_ty se)
              Hvalue s_target Hpres)))).
    + eapply IH; eassumption.
Qed.

Lemma copy_capture_store_as_captured_entries_typed_with_env_preserved :
  forall Ω env s_target s Σ captures caps captured env_lt captured_tys,
    store_typed env s Σ ->
    store_ref_targets_preserved env s s_target ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    Forall2 (store_entry_typed env s_target) captured (sctx_of_store captured).
Proof.
  intros Ω env s_target s Σ captures caps captured env_lt captured_tys
    Hstore Hpres Hcopy Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  eapply copy_capture_store_as_captured_entries_typed_with_env_base_preserved;
    eassumption.
Qed.

Lemma copy_capture_store_as_captured_values_canonical_roots_with_env :
  forall Ω env s Σ captures caps captured env_lt captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    Forall (fun se =>
      value_roots_within (capture_value_roots (se_val se)) (se_val se))
      captured.
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys
    Hstore Hcopy Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  clear Henv.
  revert caps captured captured_tys0 Hcopy Hbase Hallowed.
  induction captures as [| x captures IH]; intros caps captured captured_tys0
    Hcopy Hbase Hallowed;
    destruct caps as [| cap caps]; simpl in Hcopy, Hbase; try discriminate.
  - injection Hcopy as <-. constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hbase;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest_tys | err]
      eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    injection Hbase as <-.
    simpl in Hallowed.
    apply andb_true_iff in Hallowed as [Hallowed_head Hallowed_tail].
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [Hrefines Hvalue]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    simpl. constructor.
    + apply capture_value_roots_sound.
      unfold closure_capture_allowed_b in Hallowed_head.
      apply orb_true_iff in Hallowed_head as [Hfree | Href].
      * left.
        assert (Hrootless_T : runtime_rootless_ty env T).
        { apply capture_ref_free_ty_b_runtime_rootless. exact Hfree. }
        assert (Hrootless : runtime_rootless_ty env (se_ty se)).
        { rewrite <- H0. exact Hrootless_T. }
        eapply value_has_type_runtime_rootless_empty_roots.
        -- exact Hvalue.
        -- exact Hrootless.
      * right.
        destruct T as [u core]. simpl in Href.
        destruct core; try discriminate.
        destruct r; try discriminate.
        eapply value_has_type_ref_ty_value.
        rewrite H0. exact Hvalue.
    + eapply IH; eassumption.
Qed.

Lemma copy_capture_store_as_captured_store_typed_rootless :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    captured_store_typed env captured /\
    Forall (fun se => value_roots_within [] (se_val se)) captured.
Proof.
  intros Ω env s Σ captures caps captured captured_tys Hstore Hcopy Hcheck.
  unfold captured_store_typed.
  eapply copy_capture_store_as_captured_entries_typed_rootless; eassumption.
Qed.
