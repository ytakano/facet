From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCore.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCapture.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCopyStore.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma captured_store_runtime_ready_empty :
  forall env,
    captured_store_runtime_ready env [] [].
Proof.
  intros env.
  unfold captured_store_runtime_ready.
  repeat split.
  - unfold captured_store_typed, store_typed. constructor.
  - constructor.
  - unfold store_no_shadow. constructor.
  - unfold root_env_no_shadow. constructor.
  - unfold root_env_store_roots_named.
    intros x roots z Hlookup _. simpl in Hlookup. discriminate.
  - unfold root_env_store_keys_named, root_env_keys_named.
    intros x Hin. simpl in Hin. contradiction.
Qed.

Lemma captured_call_frame_ready_empty :
  forall env s_args R_args,
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    captured_call_frame_ready env [] [] s_args R_args.
Proof.
  intros env s_args R_args Hroots Hshadow Hrn Hnamed Hkeys.
  unfold captured_call_frame_ready.
  split.
  - apply captured_store_runtime_ready_empty.
  - repeat split.
    + exact Hroots.
    + simpl. exact Hshadow.
    + simpl. exact Hrn.
    + simpl. exact Hnamed.
    + simpl. exact Hkeys.
Qed.

Fixpoint empty_root_env_for_store (s : store) : root_env :=
  match s with
  | [] => []
  | se :: rest => (se_name se, []) :: empty_root_env_for_store rest
  end.

Lemma root_env_lookup_empty_root_env_for_store :
  forall s x,
    In x (store_names s) ->
    root_env_lookup x (empty_root_env_for_store s) = Some [].
Proof.
  induction s as [| se rest IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst x. rewrite ident_eqb_refl. reflexivity.
    + destruct (ident_eqb x (se_name se)) eqn:Heq.
      * reflexivity.
      * apply IH. exact Hin.
Qed.

Lemma root_env_lookup_empty_root_env_for_store_none :
  forall s x,
    ~ In x (store_names s) ->
    root_env_lookup x (empty_root_env_for_store s) = None.
Proof.
  induction s as [| se rest IH]; intros x Hfresh; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    exfalso. apply Hfresh. left. reflexivity.
  - apply IH.
    intros Hin. apply Hfresh. right. exact Hin.
Qed.

Lemma root_env_names_empty_root_env_for_store :
  forall s,
    root_env_names (empty_root_env_for_store s) = store_names s.
Proof.
  induction s as [| se rest IH]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma root_env_no_shadow_empty_root_env_for_store :
  forall s,
    store_no_shadow s ->
    root_env_no_shadow (empty_root_env_for_store s).
Proof.
  unfold store_no_shadow, root_env_no_shadow.
  intros s Hshadow.
  rewrite root_env_names_empty_root_env_for_store.
  exact Hshadow.
Qed.

Lemma root_env_store_roots_named_empty_root_env_for_store :
  forall s,
    root_env_store_roots_named (empty_root_env_for_store s) s.
Proof.
  unfold root_env_store_roots_named.
  intros s x roots z Hlookup Hin.
  destruct s as [| se rest].
  - simpl in Hlookup. discriminate.
  - destruct roots as [| r roots].
    + contradiction.
    + assert (Hin_names : In x (store_names (se :: rest))).
      { rewrite <- root_env_names_empty_root_env_for_store.
        eapply root_env_lookup_some_in_names. exact Hlookup. }
      rewrite root_env_lookup_empty_root_env_for_store in Hlookup
        by exact Hin_names.
      inversion Hlookup.
Qed.

Lemma root_env_store_keys_named_empty_root_env_for_store :
  forall s,
    root_env_store_keys_named (empty_root_env_for_store s) s.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros s x Hin.
  rewrite root_env_names_empty_root_env_for_store in Hin.
  exact Hin.
Qed.

Lemma store_names_app :
  forall s1 s2,
    store_names (s1 ++ s2) = store_names s1 ++ store_names s2.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma store_no_shadow_app :
  forall s1 s2,
    store_no_shadow s1 ->
    store_no_shadow s2 ->
    (forall x, In x (store_names s1) -> ~ In x (store_names s2)) ->
    store_no_shadow (s1 ++ s2).
Proof.
  unfold store_no_shadow.
  intros s1.
  induction s1 as [| se rest IH]; intros s2 Hshadow1 Hshadow2 Hdisj;
    simpl in *.
  - exact Hshadow2.
  - inversion Hshadow1 as [| x xs Hnotin Hshadow_tail]; subst.
    constructor.
    + rewrite store_names_app.
      intros Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply Hnotin. exact Hin.
      * apply (Hdisj (se_name se)).
        -- simpl. left. reflexivity.
        -- exact Hin.
    + apply IH.
      * exact Hshadow_tail.
      * exact Hshadow2.
      * intros x Hin_rest.
        apply Hdisj. simpl. right. exact Hin_rest.
Qed.

Lemma store_roots_within_weaken_lookup :
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

Lemma store_roots_within_empty_root_env_for_store :
  forall s,
    store_no_shadow s ->
    Forall (fun se => value_roots_within [] (se_val se)) s ->
    store_roots_within (empty_root_env_for_store s) s.
Proof.
  induction s as [| se rest IH]; intros Hshadow Hvalues; simpl in *.
  - constructor.
  - inversion Hvalues as [| se0 rest0 Hvalue Htail]; subst.
    inversion Hshadow as [| x xs Hnotin Hshadow_tail]; subst.
    destruct se as [sx sT sv sst].
    constructor.
    + econstructor.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * exact Hvalue.
    + eapply store_roots_within_weaken_lookup.
      * apply IH; assumption.
      * intros x roots Hin Hlookup.
        simpl.
        destruct (ident_eqb x sx) eqn:Heq.
        -- apply ident_eqb_eq in Heq. subst x.
           exfalso. apply Hnotin. exact Hin.
        -- exact Hlookup.
Qed.

Lemma copy_capture_store_as_captured_store_runtime_ready :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    NoDup (ctx_names (params_ctx caps)) ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    captured_store_runtime_ready env captured
      (empty_root_env_for_store captured).
Proof.
  intros Ω env s Σ captures caps captured captured_tys
    Hstore Hnodup Hcopy Hcheck.
  destruct (copy_capture_store_as_captured_store_typed_rootless
              Ω env s Σ captures caps captured captured_tys
              Hstore Hcopy Hcheck)
    as [Htyped Hroots_values].
  assert (Hshadow : store_no_shadow captured).
  { unfold store_no_shadow.
    rewrite (copy_capture_store_as_store_names captures caps s captured Hcopy).
    exact Hnodup. }
  unfold captured_store_runtime_ready.
  repeat split.
  - exact Htyped.
  - apply store_roots_within_empty_root_env_for_store; assumption.
  - exact Hshadow.
  - apply root_env_no_shadow_empty_root_env_for_store. exact Hshadow.
  - apply root_env_store_roots_named_empty_root_env_for_store.
  - apply root_env_store_keys_named_empty_root_env_for_store.
Qed.

Lemma store_roots_with_empty_roots_exclude_root :
  forall R s root,
    store_roots_within R s ->
    (forall x roots,
      In x (store_names s) ->
      root_env_lookup x R = Some roots ->
      roots = []) ->
    store_refs_exclude_root root s.
Proof.
  intros R s root Hwithin Hempty.
  induction Hwithin as [R|R se rest Hentry Hrest IH].
  - constructor.
  - constructor.
    + inversion Hentry; subst.
      assert (Hroots_empty : roots = []).
      { eapply Hempty.
        - simpl. left. reflexivity.
        - exact H. }
      subst roots.
      constructor.
      eapply value_roots_exclude_root.
      * exact H0.
      * unfold roots_exclude. intros Hin. contradiction.
    + apply IH.
      intros x roots Hin Hlookup.
      eapply Hempty.
      * simpl. right. exact Hin.
      * exact Hlookup.
Qed.

Lemma store_roots_within_empty_root_env_refs_exclude_root :
  forall s root,
    store_roots_within (empty_root_env_for_store s) s ->
    store_refs_exclude_root root s.
Proof.
  intros s root Hwithin.
  eapply store_roots_with_empty_roots_exclude_root.
  - exact Hwithin.
  - intros x roots Hin Hlookup.
    rewrite (root_env_lookup_empty_root_env_for_store s x Hin) in Hlookup.
    inversion Hlookup. reflexivity.
Qed.

Lemma captured_store_runtime_ready_empty_refs_exclude_root :
  forall env captured root,
    captured_store_runtime_ready env captured
      (empty_root_env_for_store captured) ->
    store_refs_exclude_root root captured.
Proof.
  intros env captured root Hready.
  unfold captured_store_runtime_ready in Hready.
  destruct Hready as [_ [Hroots _]].
  eapply store_roots_within_empty_root_env_refs_exclude_root.
  exact Hroots.
Qed.

Lemma copied_captured_closure_roots_empty :
  forall Ω env s Σ fname captures fdef captured captured_tys,
    store_typed env s Σ ->
    lookup_fn fname (env_fns env) = Some fdef ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    value_roots_within [] (VClosure fname captured).
Proof.
  intros Ω env s Σ fname captures fdef captured captured_tys Hstore
    Hlookup Hnodup Hcopy Hcheck.
  constructor.
  intros root _.
  pose proof
    (copy_capture_store_as_captured_store_runtime_ready
      Ω env s Σ captures (fn_captures fdef) captured captured_tys
      Hstore Hnodup Hcopy Hcheck) as Hready.
  eapply captured_store_runtime_ready_empty_refs_exclude_root.
  exact Hready.
Qed.

Lemma root_env_store_roots_named_app :
  forall R1 R2 s1 s2,
    root_env_store_roots_named R1 s1 ->
    root_env_store_roots_named R2 s2 ->
    (forall x roots,
      root_env_lookup x R2 = Some roots ->
      root_env_lookup x R1 = None) ->
    root_env_store_roots_named (R1 ++ R2) (s1 ++ s2).
Proof.
  unfold root_env_store_roots_named.
  intros R1 R2 s1 s2 Hnamed1 Hnamed2 _ x roots z Hlookup Hin.
  destruct (root_env_lookup x R1) as [roots1 |] eqn:Hlookup1.
  - rewrite (root_env_lookup_app_left x R1 R2 roots1 Hlookup1)
      in Hlookup.
    inversion Hlookup; subst roots1.
    rewrite store_names_app. apply in_or_app. left.
    eapply Hnamed1; eassumption.
  - rewrite (root_env_lookup_app_right x R1 R2 Hlookup1) in Hlookup.
    rewrite store_names_app. apply in_or_app. right.
    eapply Hnamed2; eassumption.
Qed.

Lemma root_env_store_keys_named_app :
  forall R1 R2 s1 s2,
    root_env_store_keys_named R1 s1 ->
    root_env_store_keys_named R2 s2 ->
    root_env_store_keys_named (R1 ++ R2) (s1 ++ s2).
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros R1 R2 s1 s2 Hkeys1 Hkeys2 x Hin.
  rewrite root_env_names_app in Hin.
  rewrite store_names_app.
  apply in_app_or in Hin.
  apply in_or_app.
  destruct Hin as [Hin | Hin].
  - left. apply Hkeys1. exact Hin.
  - right. apply Hkeys2. exact Hin.
Qed.

Lemma store_roots_within_app :
  forall R1 R2 s1 s2,
    store_roots_within R1 s1 ->
    store_roots_within R2 s2 ->
    (forall x roots,
      root_env_lookup x R2 = Some roots ->
      root_env_lookup x R1 = None) ->
    store_roots_within (R1 ++ R2) (s1 ++ s2).
Proof.
  intros R1 R2 s1 s2 Hroots1.
  revert R2 s2.
  induction Hroots1 as [R1 | R1 se rest Hentry Hrest IH];
    intros R2 s2 Hroots2 Hdisj.
  - simpl.
    eapply store_roots_within_weaken_lookup.
    + exact Hroots2.
    + intros x roots _ Hlookup.
      specialize (Hdisj x roots Hlookup).
      rewrite (root_env_lookup_app_right x R1 R2 Hdisj).
      exact Hlookup.
  - simpl. constructor.
    + inversion Hentry as [R0 sx sT sv sst roots Hlookup Hvalue]; subst.
      econstructor.
      * eapply root_env_lookup_app_left. exact Hlookup.
      * exact Hvalue.
    + apply IH.
      * exact Hroots2.
      * intros x roots Hlookup2.
        specialize (Hdisj x roots Hlookup2).
        exact Hdisj.
  Unshelve.
  all: eauto.
Qed.

Lemma captured_call_frame_ready_compose :
  forall env captured Rcap s_args R_args,
    captured_store_runtime_ready env captured Rcap ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    (forall x, In x (store_names captured) -> ~ In x (store_names s_args)) ->
    (forall x, root_env_lookup x Rcap = None \/
      root_env_lookup x R_args = None) ->
    captured_call_frame_ready env captured Rcap s_args R_args.
Proof.
  intros env captured Rcap s_args R_args Hcap_ready Hroots_args
    Hshadow_args Hrn_args Hnamed_args Hkeys_args Hstore_disj Hroot_disj.
  unfold captured_store_runtime_ready in Hcap_ready.
  destruct Hcap_ready as
    [Hcap_typed
      [Hroots_cap
        [Hshadow_cap
          [Hrn_cap [Hnamed_cap Hkeys_cap]]]]].
  unfold captured_call_frame_ready, captured_store_runtime_ready.
  repeat split.
  - exact Hcap_typed.
  - exact Hroots_cap.
  - exact Hshadow_cap.
  - exact Hrn_cap.
  - exact Hnamed_cap.
  - exact Hkeys_cap.
  - exact Hroots_args.
  - apply store_no_shadow_app; assumption.
  - apply root_env_no_shadow_app; assumption.
  - unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    destruct (root_env_lookup x Rcap) as [roots_cap |] eqn:Hlookup_cap.
    + rewrite (root_env_lookup_app_left x Rcap R_args roots_cap
        Hlookup_cap) in Hlookup.
      inversion Hlookup; subst roots_cap.
      rewrite store_names_app.
      apply in_or_app. left.
      eapply Hnamed_cap; eassumption.
    + rewrite (root_env_lookup_app_right x Rcap R_args Hlookup_cap)
        in Hlookup.
      rewrite store_names_app.
      apply in_or_app. right.
      eapply Hnamed_args; eassumption.
  - apply root_env_store_keys_named_app; assumption.
Qed.
