From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyDirectCall.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma params_ctx_length_ts :
  forall ps,
    List.length (params_ctx ps) = List.length ps.
Proof.
  induction ps as [| p ps IH]; simpl; auto.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_base_of_exact_sctx :
  forall env Ω Σ captures caps captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps = infer_ok captured_tys.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys Hcheck;
    destruct caps as [| cap caps]; simpl in *; try discriminate.
  - exact Hcheck.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup;
      try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free;
      try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    simpl.
    try rewrite Hcap_mut.
    try rewrite Hcap_lookup.
    try rewrite Hlookup.
    try rewrite Hconsumed.
    try rewrite Hmoved.
    try rewrite Hmut.
    try rewrite Husage.
    rewrite (IH caps captured_rest Hrest).
    reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_ref_free :
  forall env Ω Σ captures caps captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    Forall (fun T => capture_ref_free_ty_b env T = true) captured_tys.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys Hcheck;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - injection Hcheck as <-. constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup;
      try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free;
      try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    constructor; [exact Href_free | eapply IH; exact Hrest].
Qed.

Lemma shared_ref_lifetime_of_capture_ref_free_ty :
  forall env T,
    capture_ref_free_ty_b env T = true ->
    shared_ref_lifetime_of_ty T = None.
Proof.
  intros env T Hfree.
  apply capture_ref_free_ty_b_ty_ref_free in Hfree.
  destruct T as [u core].
  destruct core; simpl in *; try reflexivity; try discriminate.
Qed.

Lemma collect_shared_ref_lifetimes_capture_ref_free :
  forall env captured_tys,
    Forall (fun T => capture_ref_free_ty_b env T = true) captured_tys ->
    collect_shared_ref_lifetimes captured_tys = [].
Proof.
  intros env captured_tys Hfree.
  induction Hfree as [| T rest Hfree_T _ IH]; simpl.
  - reflexivity.
  - rewrite (shared_ref_lifetime_of_capture_ref_free_ty env T Hfree_T).
    exact IH.
Qed.

Lemma closure_captures_allowed_b_capture_ref_free :
  forall env Ω env_lt captured_tys,
    Forall (fun T => capture_ref_free_ty_b env T = true) captured_tys ->
    closure_captures_allowed_b env Ω env_lt captured_tys = true.
Proof.
  intros env Ω env_lt captured_tys Hfree.
  induction Hfree as [| T rest Hfree_T _ IH]; simpl.
  - reflexivity.
  - unfold closure_capture_allowed_b.
    rewrite Hfree_T. simpl. exact IH.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_of_exact_sctx :
  forall env Ω Σ captures caps captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    check_make_closure_captures_exact_sctx_with_env
      env Ω Σ captures caps = infer_ok (LStatic, captured_tys).
Proof.
  intros env Ω Σ captures caps captured_tys Hcheck.
  pose proof
    (check_make_closure_captures_exact_sctx_with_env_base_of_exact_sctx
      env Ω Σ captures caps captured_tys Hcheck) as Hbase.
  pose proof
    (check_make_closure_captures_exact_sctx_ref_free
      env Ω Σ captures caps captured_tys Hcheck) as Hfree.
  unfold check_make_closure_captures_exact_sctx_with_env.
  rewrite Hbase.
  unfold infer_closure_env_lifetime.
  rewrite (collect_shared_ref_lifetimes_capture_ref_free env captured_tys Hfree).
  rewrite (closure_captures_allowed_b_capture_ref_free
    env Ω LStatic captured_tys Hfree).
  reflexivity.
Qed.

Lemma capture_store_root_env_equiv_root_env_add_params_roots_in_frame :
  forall env captured frame caps,
    captured_params_store_typed_in_frame env captured frame caps ->
    root_env_equiv (capture_store_root_env captured)
      (root_env_add_params_roots caps
        (capture_store_root_sets captured) []).
Proof.
  intros env captured frame caps Htyped.
  pose proof (captured_params_store_typed_in_frame_store_param_prefix
                env captured frame caps Htyped) as Hprefix.
  eapply capture_store_root_env_store_param_prefix_equiv.
  exact Hprefix.
Qed.

Lemma capture_store_root_sets_store_roots_named_in_frame :
  forall env captured frame caps,
    captured_params_store_typed_in_frame env captured frame caps ->
    Forall
      (fun roots => root_set_store_roots_named roots (captured ++ frame))
      (capture_store_root_sets captured).
Proof.
  intros env captured frame caps Htyped.
  unfold captured_params_store_typed_in_frame in Htyped.
  destruct Htyped as [Htyped _].
  assert (Hentries :
    forall entries Σ,
      Forall2 (store_entry_typed env (captured ++ frame)) entries Σ ->
      Forall
        (fun roots => root_set_store_roots_named roots (captured ++ frame))
        (capture_store_root_sets entries)).
  { intros entries Σ Hentries.
    induction Hentries as [| se ce entries_tail Σ_tail Hentry _ IH].
    - constructor.
  - destruct se as [sx sT sv sst].
      destruct ce as [[[cx cT] cst] cm].
      simpl in Hentry.
      destruct Hentry as [Hname [HT [_ Hvalue]]].
      simpl. constructor.
      + eapply capture_value_roots_store_roots_named. exact Hvalue.
      + exact IH. }
  eapply Hentries. exact Htyped.
Qed.

Lemma capture_store_root_sets_store_roots_named_in_store :
  forall env target captured,
    Forall2 (store_entry_typed env target)
      captured (sctx_of_store captured) ->
    Forall
      (fun roots => root_set_store_roots_named roots target)
      (capture_store_root_sets captured).
Proof.
  intros env target captured Htyped.
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

Lemma value_roots_within_nil_capture_value_roots :
  forall v,
    value_roots_within [] v ->
    capture_value_roots v = [].
Proof.
  intros v Hroots.
  destruct v; simpl; try reflexivity.
  inversion Hroots; subst. contradiction.
Qed.

Lemma capture_store_root_sets_empty_from_rootless :
  forall captured,
    Forall (fun se => value_roots_within [] (se_val se)) captured ->
    capture_store_root_sets captured = repeat [] (List.length captured).
Proof.
  intros captured Hrootless.
  induction Hrootless as [| se rest Hse _ IH]; simpl.
  - reflexivity.
  - rewrite (value_roots_within_nil_capture_value_roots (se_val se) Hse).
    rewrite IH. reflexivity.
Qed.

Lemma capture_value_roots_stores_subset :
  forall roots v,
    value_roots_within roots v ->
    root_set_stores_subset (capture_value_roots v) roots.
Proof.
  intros roots v Hwithin.
  unfold root_set_stores_subset.
  destruct v; simpl; intros z0 Hin; try contradiction.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin; subst.
  inversion Hwithin; subst.
  assumption.
Qed.

Lemma capture_store_root_sets_bound_from_capture_root_bound :
  forall R s captures caps captured capture_roots,
    copy_capture_store_as captures caps s = Some captured ->
    store_roots_within R s ->
    capture_root_bound R captures caps = Some capture_roots ->
    root_set_stores_subset
      (root_sets_union (capture_store_root_sets captured))
      capture_roots.
Proof.
  intros R s captures.
  induction captures as [| x captures IH];
    intros caps captured capture_roots Hcopy Hroots Hbound;
    destruct caps as [| cap caps]; simpl in *; try discriminate.
  - inversion Hcopy; subst captured.
    inversion Hbound; subst capture_roots.
    unfold root_set_stores_subset.
    intros z Hin. contradiction.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Havailable; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_tail |]
      eqn:Hcopy_tail; try discriminate.
    destruct (root_env_lookup x R) as [roots_x |] eqn:Hroot_lookup;
      try discriminate.
    destruct (capture_root_bound R captures caps) as [capture_roots_tail |]
      eqn:Hbound_tail; try discriminate.
    inversion Hcopy; subst captured.
    inversion Hbound; subst capture_roots.
    unfold root_set_stores_subset.
    intros z Hin.
    apply root_set_union_in_inv in Hin.
    destruct Hin as [Hin_head | Hin_tail].
    + apply root_set_union_in_l.
      pose proof (store_roots_within_lookup_value
        R s x se roots_x Hroots Hlookup Hroot_lookup) as Hvalue_roots.
      eapply capture_value_roots_stores_subset; eassumption.
    + apply root_set_union_in_r.
      eapply IH; eassumption.
Qed.

Lemma captured_call_runtime_root_env_covers_params_captures_with_roots :
  forall ps caps arg_roots cap_roots Rcap R_tail,
    NoDup (ctx_names (params_ctx (ps ++ caps))) ->
    List.length arg_roots = List.length ps ->
    List.length cap_roots = List.length caps ->
    root_env_equiv Rcap (root_env_add_params_roots caps cap_roots []) ->
    (forall x, In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x Rcap = None) ->
    root_env_covers_params (ps ++ caps)
      (call_param_root_env ps arg_roots (Rcap ++ R_tail)).
Proof.
  intros ps caps arg_roots cap_roots Rcap R_tail Hnodup Hlen_args
    Hlen_caps Hequiv_cap Hfresh_cap.
  apply root_env_covers_params_app.
  - apply call_param_root_env_covers_params.
    + rewrite params_ctx_app, ctx_names_app in Hnodup.
      eapply NoDup_app_left_ts. exact Hnodup.
    + exact Hlen_args.
  - assert (Hcovers_cap :
      root_env_covers_params caps Rcap).
    { eapply root_env_covers_params_equiv.
      - apply root_env_equiv_sym. exact Hequiv_cap.
      - apply root_env_covers_params_add_params_roots.
        + rewrite params_ctx_app, ctx_names_app in Hnodup.
          eapply NoDup_app_right_ts. exact Hnodup.
        + exact Hlen_caps. }
    unfold root_env_covers_params in *.
    intros x Hin_caps.
    assert (Hnotin_ps : ~ In x (ctx_names (params_ctx ps))).
    { rewrite params_ctx_app, ctx_names_app in Hnodup.
      intros Hin_ps.
      pose proof
        (NoDup_app_not_in_right_ts (ctx_names (params_ctx ps))
          (ctx_names (params_ctx caps)) x Hnodup Hin_ps) as Hnotin_caps.
      exact (Hnotin_caps Hin_caps). }
    destruct (Hcovers_cap x Hin_caps) as [roots Hlookup_cap].
    exists roots.
    unfold call_param_root_env.
    rewrite root_env_add_params_roots_lookup_not_in by exact Hnotin_ps.
    rewrite root_env_lookup_remove_params_not_in by exact Hnotin_ps.
    eapply root_env_lookup_app_left. exact Hlookup_cap.
Qed.

Lemma eval_make_closure_copy_capture_store_as_ts :
  forall env s fname captures captured fdef,
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured.
Proof.
  intros env s fname captures captured fdef Heval Hlookup.
  dependent destruction Heval.
  assert (Hsame : fdef0 = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef0.
  exact H0.
Qed.

Lemma captured_call_runtime_args_tail_fresh_names_for_fresh_call_in_frame :
  forall env captured Rcap s_args R_args fdef fcall used',
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env captured Rcap s_args R_args fdef fcall used'
    Hframe Hrename x Hin.
  unfold captured_call_frame_ready_in_frame in Hframe.
  destruct Hframe as [_ [_ [_ [Hrn_tail [Hnamed_tail Hkeys_tail]]]]].
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_tail.
    eapply NoDup_app_right_ts. exact Hrn_tail. }
  assert (Hnamed_args :
    root_env_store_roots_named R_args (captured ++ s_args)).
  { unfold root_env_store_roots_named in *.
    intros y roots z Hlookup_args Hin_root.
    eapply Hnamed_tail.
    - assert (Hlookup_cap : root_env_lookup y Rcap = None).
      { eapply root_env_no_shadow_app_lookup_right_none; eassumption. }
      rewrite (root_env_lookup_app_right y Rcap R_args Hlookup_cap).
      exact Hlookup_args.
    - exact Hin_root. }
  assert (Hkeys_args :
    root_env_store_keys_named R_args (captured ++ s_args)).
  { unfold root_env_store_keys_named, root_env_keys_named in *.
    intros y Hin_names.
    apply Hkeys_tail.
    rewrite root_env_names_app.
    apply in_or_app. right. exact Hin_names. }
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names (captured ++ s_args))).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes; assumption.
Qed.
