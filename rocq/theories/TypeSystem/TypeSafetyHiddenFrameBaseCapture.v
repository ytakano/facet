From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCore.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma capture_value_roots_sound :
  forall v,
    value_roots_within [] v \/
    (exists x path, v = VRef x path) ->
    value_roots_within (capture_value_roots v) v.
Proof.
  intros v Hcase.
  destruct Hcase as [Hrootless | [x [path Href]]].
  - destruct v; simpl in *; try exact Hrootless.
    inversion Hrootless; subst.
    contradiction.
  - subst v. simpl. constructor. simpl. left. reflexivity.
Qed.

Lemma ty_compatible_expected_ref_actual_ref :
  forall Ω T_actual u l rk T,
    ty_compatible Ω T_actual (MkTy u (TRef l rk T)) ->
    exists u_actual l_actual T_actual_inner,
      T_actual = MkTy u_actual (TRef l_actual rk T_actual_inner).
Proof.
  intros Ω T_actual u l rk T Hcompat.
  remember (MkTy u (TRef l rk T)) as T_expected eqn:Hexpected.
  induction Hcompat; inversion Hexpected; subst; try discriminate.
  - subst. eauto.
  - eauto.
  - eauto.
Qed.

Lemma ty_lifetime_equiv_expected_ref_actual_ref :
  forall T_actual u l rk T,
    ty_lifetime_equiv T_actual (MkTy u (TRef l rk T)) ->
    exists l_actual T_actual_inner,
      T_actual = MkTy u (TRef l_actual rk T_actual_inner).
Proof.
  intros T_actual u l rk T Hequiv.
  remember (MkTy u (TRef l rk T)) as T_expected eqn:Hexpected.
  induction Hequiv; inversion Hexpected; subst; try discriminate.
  eauto.
Qed.

Lemma value_has_type_ref_ty_value_aux :
  forall env s v T_final,
    value_has_type env s v T_final ->
    forall u l rk T,
      T_final = MkTy u (TRef l rk T) ->
      exists x path, v = VRef x path.
Proof.
  intros env s v T_final Htype.
  induction Htype; intros u_ref l_ref rk_ref T_ref Href;
    inversion Href; subst; try discriminate.
  - eauto.
  - unfold fn_value_ty, fn_signature_ty_with_usage in Href.
    destruct (fn_type_params fdef) eqn:Htypeparams;
      destruct (fn_lifetimes fdef) eqn:Hlifetimes;
      try discriminate.
  - unfold fn_value_ty, fn_signature_ty_with_usage in Href.
    destruct (fn_type_params fdef) eqn:Htypeparams;
      destruct (fn_lifetimes fdef) eqn:Hlifetimes;
      try discriminate.
  - destruct (ty_compatible_expected_ref_actual_ref
      Ω T_actual u_ref l_ref rk_ref T_ref H)
      as [u_actual [l_actual [T_inner Hactual]]].
    eapply IHHtype. exact Hactual.
  - destruct (ty_lifetime_equiv_expected_ref_actual_ref
      T_actual u_ref l_ref rk_ref T_ref H)
      as [l_actual [T_inner Hactual]].
    eapply IHHtype. exact Hactual.
Qed.

Lemma value_has_type_ref_ty_value :
  forall env s v u l rk T,
    value_has_type env s v (MkTy u (TRef l rk T)) ->
    exists x path, v = VRef x path.
Proof.
  intros env s v u l rk T Htype.
  eapply value_has_type_ref_ty_value_aux.
  - exact Htype.
  - reflexivity.
Qed.

Lemma capture_store_root_env_store_keys_named :
  forall captured,
    root_env_store_keys_named
      (capture_store_root_env captured) captured.
Proof.
  intros captured.
  unfold root_env_store_keys_named, root_env_keys_named.
  rewrite capture_store_root_env_names.
  intros x Hin. exact Hin.
Qed.

Lemma copy_capture_roots_as_length :
  forall captures caps R Rcap,
    copy_capture_roots_as captures caps R = Some Rcap ->
    List.length captures = List.length caps.
Proof.
  intros captures.
  induction captures as [| x captures IH]; intros caps R Rcap Hcopy;
    destruct caps as [| cap caps]; simpl in Hcopy; try discriminate;
    simpl.
  - reflexivity.
  - destruct (root_env_lookup x R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Htail; try discriminate.
    injection Hcopy as <-.
    f_equal. eapply IH. exact Htail.
Qed.

Lemma copy_capture_roots_as_names :
  forall captures caps R Rcap,
    copy_capture_roots_as captures caps R = Some Rcap ->
    root_env_names Rcap = ctx_names (params_ctx caps).
Proof.
  intros captures.
  induction captures as [| x captures IH]; intros caps R Rcap Hcopy;
    destruct caps as [| cap caps]; simpl in Hcopy; try discriminate.
  - injection Hcopy as <-. reflexivity.
  - destruct (root_env_lookup x R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Htail; try discriminate.
    injection Hcopy as <-.
    simpl. rewrite (IH caps R Rtail Htail). reflexivity.
Qed.

Lemma copy_capture_roots_as_no_shadow :
  forall captures caps R Rcap,
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    root_env_no_shadow Rcap.
Proof.
  intros captures caps R Rcap Hcopy Hnodup.
  unfold root_env_no_shadow.
  rewrite (copy_capture_roots_as_names captures caps R Rcap Hcopy).
  exact Hnodup.
Qed.

Lemma param_name_nth_error_in_params_ctx :
  forall caps n cap,
    nth_error caps n = Some cap ->
    In (param_name cap) (ctx_names (params_ctx caps)).
Proof.
  induction caps as [| cap0 caps IH]; intros n cap Hnth;
    destruct n as [| n]; simpl in Hnth; try discriminate.
  - injection Hnth as <-. simpl. left. reflexivity.
  - simpl. right. eapply IH. exact Hnth.
Qed.

Lemma copy_capture_roots_as_lookup_nth :
  forall captures caps R Rcap n src cap roots,
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    nth_error captures n = Some src ->
    nth_error caps n = Some cap ->
    root_env_lookup src R = Some roots ->
    root_env_lookup (param_name cap) Rcap = Some roots.
Proof.
  intros captures.
  induction captures as [| x captures IH];
    intros caps R Rcap n src cap roots Hcopy Hnodup Hsrc Hcap Hlookup_src;
    destruct caps as [| cap0 caps]; simpl in Hcopy; try discriminate.
  - destruct n; simpl in Hsrc; discriminate.
  - destruct (root_env_lookup x R) as [roots0 |] eqn:Hlookup_x;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Htail; try discriminate.
    injection Hcopy as <-.
    destruct n as [| n].
    + simpl in Hsrc, Hcap.
      injection Hsrc as <-. injection Hcap as <-.
      rewrite Hlookup_src in Hlookup_x. injection Hlookup_x as <-.
      simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl in Hsrc, Hcap.
      simpl.
      inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
      destruct (ident_eqb (param_name cap) (param_name cap0)) eqn:Heq.
      * apply ident_eqb_eq in Heq.
        exfalso.
        apply Hnotin.
        rewrite <- Heq.
        eapply param_name_nth_error_in_params_ctx. exact Hcap.
      * eapply IH; eassumption.
Qed.

Lemma copy_capture_roots_as_lookup_head :
  forall x captures cap caps R Rcap roots,
    copy_capture_roots_as (x :: captures) (cap :: caps) R = Some Rcap ->
    NoDup (ctx_names (params_ctx (cap :: caps))) ->
    root_env_lookup x R = Some roots ->
    root_env_lookup (param_name cap) Rcap = Some roots.
Proof.
  intros x captures cap caps R Rcap roots Hcopy Hnodup Hlookup.
  eapply copy_capture_roots_as_lookup_nth with
    (captures := x :: captures) (caps := cap :: caps)
    (n := 0) (src := x) (cap := cap); eauto.
Qed.

Lemma check_make_closure_captures_exact_sctx_sound :
  forall env Ω Σ captures caps captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    typed_captures Ω Σ LStatic captures caps captured_tys /\
    captured_tys = map param_ty caps.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys Hcheck;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - injection Hcheck as <-.
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
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    destruct (IH caps captured_rest Hrest) as [Htyped_tail Htys_tail].
    assert (Havailable : binding_available_b st [] = true).
    { unfold binding_available_b.
      rewrite Hconsumed, Hmoved. reflexivity. }
    assert (HTeq : T = param_ty cap).
    { apply ty_eqb_true. exact Hty_eq. }
    subst T.
    split.
    + eapply TCap_Cons.
      * unfold sctx_lookup in Hlookup.
        eapply ctx_lookup_state_available_nil_lookup; eassumption.
      * exact Hmut.
      * apply usage_eqb_true. exact Husage.
      * apply CCap_RefFree.
        apply (capture_ref_free_ty_b_ty_ref_free env (param_ty cap)).
        exact Href_free.
      * apply ty_compatible_refl.
      * exact Htyped_tail.
    + simpl. rewrite Htys_tail. reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_base_sound :
  forall env Ω Σ captures caps captured_tys env_lt,
    check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps = infer_ok captured_tys ->
    closure_captures_allowed_b env Ω env_lt captured_tys = true ->
    typed_captures Ω Σ env_lt captures caps captured_tys /\
    captured_tys = map param_ty caps.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys env_lt
    Hcheck Hallowed;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - injection Hcheck as <-.
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
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq Hcompat].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest | err] eqn:Hrest;
      try discriminate.
    injection Hcheck as <-.
    simpl in Hallowed.
    apply andb_true_iff in Hallowed as [Hallowed_head Hallowed_tail].
    destruct (IH caps captured_rest env_lt Hrest Hallowed_tail)
      as [Htyped_tail Htys_tail].
    assert (Havailable : binding_available_b st [] = true).
    { unfold binding_available_b.
      rewrite Hconsumed, Hmoved. reflexivity. }
    assert (HTeq : T = param_ty cap).
    { apply ty_eqb_true. exact Hty_eq. }
    subst T.
    split.
    + eapply TCap_Cons.
      * unfold sctx_lookup in Hlookup.
        eapply ctx_lookup_state_available_nil_lookup; eassumption.
      * exact Hmut.
      * apply usage_eqb_true. exact Husage.
      * eapply closure_capture_allowed_b_sound. exact Hallowed_head.
      * apply ty_compatible_b_sound. exact Hcompat.
      * exact Htyped_tail.
    + simpl. rewrite Htys_tail. reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_sound :
  forall env Ω Σ captures caps env_lt captured_tys,
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    typed_captures Ω Σ env_lt captures caps captured_tys /\
    captured_tys = map param_ty caps.
Proof.
  intros env Ω Σ captures caps env_lt captured_tys Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  eapply check_make_closure_captures_exact_sctx_with_env_base_sound;
    eassumption.
Qed.

Lemma binding_available_nil_fresh :
  forall st,
    binding_available_b st [] = true ->
    st = binding_state_of_bool false.
Proof.
  intros [consumed moved] Havailable.
  unfold binding_available_b in Havailable.
  destruct consumed; simpl in Havailable; try discriminate.
  destruct moved as [| p moved']; simpl in Havailable; try discriminate.
  reflexivity.
Qed.

Lemma copy_capture_store_exact_sctx_of_store :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    sctx_of_store captured = sctx_of_ctx (params_ctx caps).
Proof.
  intros Ω env s Σ captures.
  induction captures as [| x captures IH]; intros caps captured captured_tys
    Hstore Hcopy Hcheck;
    destruct caps as [| cap caps]; simpl in Hcopy, Hcheck; try discriminate.
  - injection Hcopy as <-. reflexivity.
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
    apply andb_true_iff in Hcopy_ok.
    destruct Hcopy_ok as [Hruntime_available _].
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [_ _]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    apply binding_available_nil_fresh in Hruntime_available.
    simpl.
    rewrite Hruntime_available.
    change (sctx_of_ctx (param_ctx_entry cap :: params_ctx caps)) with
      ((param_name cap, param_ty cap, binding_state_of_bool false,
        param_mutability cap) :: sctx_of_ctx (params_ctx caps)).
    rewrite Hcap_mut.
    rewrite (IH caps captured_rest captured_rest_tys Hstore Hcopy_rest
      Hrest_check).
    reflexivity.
Qed.

Lemma copy_capture_store_exact_with_env_sctx_of_store :
  forall Ω env s Σ captures caps captured env_lt captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    sctx_of_store captured = sctx_of_ctx (params_ctx caps).
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
  clear Henv Hallowed.
  revert caps captured captured_tys0 Hcopy Hbase.
  induction captures as [| x captures IH]; intros caps captured captured_tys0
    Hcopy Hbase;
    destruct caps as [| cap caps]; simpl in Hcopy, Hbase; try discriminate.
  - injection Hcopy as <-. reflexivity.
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
    apply andb_true_iff in Hcopy_ok.
    destruct Hcopy_ok as [Hruntime_available _].
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [_ _]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    apply binding_available_nil_fresh in Hruntime_available.
    simpl.
    rewrite Hruntime_available.
    change (sctx_of_ctx (param_ctx_entry cap :: params_ctx caps)) with
      ((param_name cap, param_ty cap, binding_state_of_bool false,
        param_mutability cap) :: sctx_of_ctx (params_ctx caps)).
    rewrite Hcap_mut.
    rewrite (IH caps captured_rest captured_rest_tys Hcopy_rest Hrest_check).
    reflexivity.
Qed.

Lemma captured_store_typed_as_params :
  forall env captured caps,
    captured_store_typed env captured ->
    sctx_of_store captured = sctx_of_ctx (params_ctx caps) ->
    captured_params_store_typed env captured caps.
Proof.
  intros env captured caps Htyped Heq.
  unfold captured_store_typed, captured_params_store_typed in *.
  rewrite <- Heq.
  split; [exact Htyped | reflexivity].
Qed.
