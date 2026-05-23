From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCore.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCapture.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCopyStore.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseEmpty.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_lookup_some_in_store_names :
  forall x s se,
    store_lookup x s = Some se ->
    In x (store_names s).
Proof.
  intros x s.
  induction s as [| se_head rest IH]; intros se Hlookup;
    simpl in Hlookup; try discriminate.
  destruct (ident_eqb x (se_name se_head)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x. simpl. left. reflexivity.
  - simpl. right. eapply IH. exact Hlookup.
Qed.

Lemma capture_store_root_env_roots_within :
  forall captured,
    Forall
      (fun se =>
        value_roots_within (capture_value_roots (se_val se)) (se_val se))
      captured ->
    store_no_shadow captured ->
    store_roots_within (capture_store_root_env captured) captured.
Proof.
  intros captured Hvalues Hshadow.
  induction Hvalues as [| se rest Hvalue _ IH]; simpl in *.
  - constructor.
  - inversion Hshadow as [| ? ? Hnotin Hnodup_tail]; subst.
    constructor.
    + destruct se as [sx sT sv sst]. simpl in *.
      econstructor.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * exact Hvalue.
    + eapply store_roots_within_weaken_lookup_hfb.
      * apply IH. exact Hnodup_tail.
      * intros x roots Hin Hlookup. simpl.
        destruct (ident_eqb x (se_name se)) eqn:Heq.
        -- apply ident_eqb_eq in Heq. subst x.
           exfalso. apply Hnotin. exact Hin.
        -- exact Hlookup.
Qed.

Lemma value_has_type_ref_root_named :
  forall env s x path T,
    value_has_type env s (VRef x path) T ->
    In x (store_names s).
Proof.
  intros env s x path T Htype.
  remember (VRef x path) as v eqn:Hv.
  induction Htype; inversion Hv; subst; eauto.
  eapply store_lookup_some_in_store_names. exact H.
Qed.

Lemma capture_value_roots_store_roots_named :
  forall env s v T,
    value_has_type env s v T ->
    root_set_store_roots_named (capture_value_roots v) s.
Proof.
  intros env s v T Htype.
  destruct v; simpl; unfold root_set_store_roots_named;
    intros root_name Hin; simpl in Hin; try contradiction.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin; subst.
  eapply value_has_type_ref_root_named. exact Htype.
Qed.

Lemma capture_store_root_env_store_roots_named_in_store :
  forall env target captured,
    Forall2 (store_entry_typed env target)
      captured (sctx_of_store captured) ->
    root_env_store_roots_named
      (capture_store_root_env captured) target.
Proof.
  intros env target captured Htyped.
  induction Htyped as [| se ce captured_tail Σ_tail Hentry _ IH].
  - unfold root_env_store_roots_named.
    intros x roots z Hlookup _. simpl in Hlookup. discriminate.
  - simpl in *.
    destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [_ Hvalue]]].
    subst cx cT.
    unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    simpl in Hlookup.
    destruct (ident_eqb x sx) eqn:Heq.
    + inversion Hlookup; subst roots.
      eapply capture_value_roots_store_roots_named in Hvalue.
      unfold root_set_store_roots_named in Hvalue.
      exact (Hvalue z Hin).
    + eapply IH; eassumption.
Qed.

Lemma capture_store_root_env_store_roots_named :
  forall env captured frame,
    Forall2 (store_entry_typed env (captured ++ frame))
      captured (sctx_of_store captured) ->
    root_env_store_roots_named
      (capture_store_root_env captured) (captured ++ frame).
Proof.
  intros env captured frame Htyped.
  eapply capture_store_root_env_store_roots_named_in_store.
  exact Htyped.
Qed.

Lemma copy_capture_store_as_captured_store_runtime_ready_in_frame_with_env :
  forall Ω env s Σ captures caps captured env_lt captured_tys frame,
    store_typed env s Σ ->
    store_ref_targets_preserved env s (captured ++ frame) ->
    NoDup (ctx_names (params_ctx caps)) ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    captured_store_runtime_ready_in_frame env captured
      (capture_store_root_env captured) frame.
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys frame
    Hstore Hpres Hnodup Hcopy Hcheck.
  pose proof
    (copy_capture_store_as_captured_entries_typed_with_env_preserved
      Ω env (captured ++ frame) s Σ captures caps captured env_lt
      captured_tys Hstore Hpres Hcopy Hcheck) as Htyped.
  pose proof
    (copy_capture_store_as_captured_values_canonical_roots_with_env
      Ω env s Σ captures caps captured env_lt captured_tys
      Hstore Hcopy Hcheck) as Hvalues.
  assert (Hshadow : store_no_shadow captured).
  { unfold store_no_shadow.
    rewrite (copy_capture_store_as_store_names captures caps s captured Hcopy).
    exact Hnodup. }
  unfold captured_store_runtime_ready_in_frame.
  repeat split.
  - exact Htyped.
  - eapply capture_store_root_env_roots_within; eassumption.
  - exact Hshadow.
  - apply capture_store_root_env_no_shadow. exact Hshadow.
  - eapply capture_store_root_env_store_roots_named. exact Htyped.
  - apply capture_store_root_env_store_keys_named.
Qed.

Lemma captured_call_frame_ready_in_frame_compose :
  forall env captured Rcap s_args R_args,
    captured_store_runtime_ready_in_frame env captured Rcap s_args ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    (forall x, In x (store_names captured) -> ~ In x (store_names s_args)) ->
    (forall x, root_env_lookup x Rcap = None \/
      root_env_lookup x R_args = None) ->
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args.
Proof.
  intros env captured Rcap s_args R_args Hcap_ready Hroots_args
    Hshadow_args Hrn_args Hnamed_args Hkeys_args Hstore_disj Hroot_disj.
  unfold captured_store_runtime_ready_in_frame in Hcap_ready.
  destruct Hcap_ready as
    [Hcap_typed
      [Hroots_cap
        [Hshadow_cap
          [Hrn_cap [Hnamed_cap Hkeys_cap]]]]].
  unfold captured_call_frame_ready_in_frame,
    captured_store_runtime_ready_in_frame.
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
      eapply Hnamed_cap; eassumption.
    + rewrite (root_env_lookup_app_right x Rcap R_args Hlookup_cap)
        in Hlookup.
      rewrite store_names_app.
      apply in_or_app. right.
      eapply Hnamed_args; eassumption.
  - apply root_env_store_keys_named_app; assumption.
Qed.

Lemma store_ref_targets_preserved_app_left :
  forall env s1 s2,
    store_ref_targets_preserved env s1 (s1 ++ s2).
Proof.
  unfold store_ref_targets_preserved.
  intros env s1 s2 x path se v T Hlookup Hvalue Htype.
  exists se, v. repeat split; try assumption.
  apply store_lookup_app_some. exact Hlookup.
Qed.

Lemma store_ref_targets_preserved_app_right :
  forall env s1 s2,
    (forall x, In x (store_names s2) -> store_lookup x s1 = None) ->
    store_ref_targets_preserved env s2 (s1 ++ s2).
Proof.
  unfold store_ref_targets_preserved.
  intros env s1 s2 Hdisj x path se v T Hlookup Hvalue Htype.
  exists se, v. repeat split; try assumption.
  rewrite (store_lookup_app_none x s1 s2).
  - exact Hlookup.
  - apply Hdisj. eapply store_lookup_some_in_store_names. exact Hlookup.
Qed.

Lemma store_typed_entries_store_preserved :
  forall env s s' entries Σ,
    Forall2 (store_entry_typed env s) entries Σ ->
    store_ref_targets_preserved env s s' ->
    Forall2 (store_entry_typed env s') entries Σ.
Proof.
  intros env s s' entries Σ Htyped Hpres.
  induction Htyped as [| se ce entries_tail Σ_tail Hentry _ IH].
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hstate Hvalue]]].
    constructor.
    + simpl. repeat split; try assumption.
      eapply value_has_type_store_preserved; eassumption.
    + exact IH.
Qed.

Lemma captured_store_runtime_ready_in_frame_from_self :
  forall env captured Rcap frame,
    captured_store_runtime_ready env captured Rcap ->
    captured_store_runtime_ready_in_frame env captured Rcap frame.
Proof.
  intros env captured Rcap frame Hready.
  unfold captured_store_runtime_ready, captured_store_runtime_ready_in_frame
    in *.
  destruct Hready as
    [Htyped [Hroots [Hshadow [Hrn [Hnamed Hkeys]]]]].
  repeat split.
  - unfold captured_store_typed, store_typed in Htyped.
    eapply store_typed_entries_store_preserved.
    + exact Htyped.
    + apply store_ref_targets_preserved_app_left.
  - exact Hroots.
  - exact Hshadow.
  - exact Hrn.
  - unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    rewrite store_names_app.
    apply in_or_app. left.
    eapply Hnamed; eassumption.
  - exact Hkeys.
Qed.

Lemma captured_call_frame_ready_in_frame_from_self :
  forall env captured Rcap s_args R_args,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args.
Proof.
  intros env captured Rcap s_args R_args Hready.
  unfold captured_call_frame_ready, captured_call_frame_ready_in_frame in *.
  destruct Hready as [Hcap_ready Hrest].
  split.
  - eapply captured_store_runtime_ready_in_frame_from_self.
    exact Hcap_ready.
  - exact Hrest.
Qed.

Lemma store_typed_entries_app :
  forall env s entries1 Σ1 entries2 Σ2,
    Forall2 (store_entry_typed env s) entries1 Σ1 ->
    Forall2 (store_entry_typed env s) entries2 Σ2 ->
    Forall2 (store_entry_typed env s)
      (entries1 ++ entries2) (Σ1 ++ Σ2).
Proof.
  intros env s entries1 Σ1 entries2 Σ2 Htyped1 Htyped2.
  induction Htyped1 as [| se ce entries_tail Σ_tail Hentry _ IH].
  - exact Htyped2.
  - simpl. constructor; assumption.
Qed.

Lemma sctx_of_store_app :
  forall s1 s2,
    sctx_of_store (s1 ++ s2) = sctx_of_store s1 ++ sctx_of_store s2.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma store_typed_app :
  forall env s1 Σ1 s2 Σ2,
    store_typed env s1 Σ1 ->
    store_typed env s2 Σ2 ->
    store_ref_targets_preserved env s1 (s1 ++ s2) ->
    store_ref_targets_preserved env s2 (s1 ++ s2) ->
    store_typed env (s1 ++ s2) (Σ1 ++ Σ2).
Proof.
  unfold store_typed.
  intros env s1 Σ1 s2 Σ2 Htyped1 Htyped2 Hpres1 Hpres2.
  apply store_typed_entries_app.
  - eapply store_typed_entries_store_preserved; eassumption.
  - eapply store_typed_entries_store_preserved; eassumption.
Qed.

Lemma store_no_shadow_app_lookup_right_none :
  forall s1 s2 x,
    store_no_shadow (s1 ++ s2) ->
    In x (store_names s2) ->
    store_lookup x s1 = None.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2 x Hshadow Hin2;
    simpl in *.
  - reflexivity.
  - inversion Hshadow as [| ? ? Hnotin Hshadow_tail]; subst.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      exfalso. apply Hnotin.
      rewrite store_names_app. apply in_or_app. right. exact Hin2.
    + eapply IH; eassumption.
Qed.

Lemma captured_call_frame_store_typed :
  forall env captured Rcap s_args R_args Σ_args,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    store_typed env (captured ++ s_args)
      (sctx_of_store captured ++ Σ_args).
Proof.
  intros env captured Rcap s_args R_args Σ_args Hready Htyped_args.
  unfold captured_call_frame_ready, captured_store_runtime_ready in Hready.
  destruct Hready as
    [[Htyped_cap _] [_ [Hshadow_frame _]]].
  eapply store_typed_app.
  - exact Htyped_cap.
  - exact Htyped_args.
  - apply store_ref_targets_preserved_app_left.
  - apply store_ref_targets_preserved_app_right.
    intros x Hin.
    eapply store_no_shadow_app_lookup_right_none; eassumption.
Qed.

Lemma captured_call_frame_store_typed_in_frame :
  forall env captured Rcap s_args R_args Σ_args,
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    store_typed env (captured ++ s_args)
      (sctx_of_store captured ++ Σ_args).
Proof.
  intros env captured Rcap s_args R_args Σ_args Hready Htyped_args.
  unfold captured_call_frame_ready_in_frame,
    captured_store_runtime_ready_in_frame in Hready.
  destruct Hready as
    [[Htyped_cap _] [_ [Hshadow_frame _]]].
  unfold store_typed in *.
  apply store_typed_entries_app.
  - exact Htyped_cap.
  - eapply store_typed_entries_store_preserved.
    + exact Htyped_args.
    + apply store_ref_targets_preserved_app_right.
      intros x Hin.
      eapply store_no_shadow_app_lookup_right_none; eassumption.
Qed.

Lemma captured_call_frame_params_store_typed :
  forall env captured Rcap s_args R_args caps Σ_args,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    store_typed env (captured ++ s_args)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args).
Proof.
  intros env captured Rcap s_args R_args caps Σ_args Hready Htyped_args.
  destruct Hready as [Hframe_ready Htyped_cap].
  unfold captured_call_frame_ready in Hframe_ready.
  destruct Hframe_ready as [_ [_ [Hshadow_frame _]]].
  eapply store_typed_app.
  - exact Htyped_cap.
  - exact Htyped_args.
  - apply store_ref_targets_preserved_app_left.
  - apply store_ref_targets_preserved_app_right.
    intros x Hin.
    eapply store_no_shadow_app_lookup_right_none; eassumption.
Qed.

Lemma store_update_state_not_in_names :
  forall x f s,
    ~ In x (store_names s) ->
    store_update_state x f s = None.
Proof.
  intros x f s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_update_val_not_in_names :
  forall x v s,
    ~ In x (store_names s) ->
    store_update_val x v s = None.
Proof.
  intros x v s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_update_path_not_in_names :
  forall x path v s,
    ~ In x (store_names s) ->
    store_update_path x path v s = None.
Proof.
  intros x path v s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_mark_used_not_in_names :
  forall x s,
    ~ In x (store_names s) ->
    store_mark_used x s = s.
Proof.
  intros x s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_remove_not_in_names :
  forall x s,
    ~ In x (store_names s) ->
    store_remove x s = s.
Proof.
  intros x s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_lookup_store_add_same :
  forall x T v s,
    store_lookup x (store_add x T v s) =
    Some (MkStoreEntry x T v (binding_state_of_bool false)).
Proof.
  intros x T v s.
  unfold store_add. simpl. rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma store_lookup_store_add_diff :
  forall x y T v s,
    x <> y ->
    store_lookup x (store_add y T v s) = store_lookup x s.
Proof.
  intros x y T v s Hneq.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma store_mark_used_store_add_diff :
  forall x y T v s,
    x <> y ->
    store_mark_used x (store_add y T v s) =
    store_add y T v (store_mark_used x s).
Proof.
  intros x y T v s Hneq.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma store_update_state_store_add_diff :
  forall x y f T v s s',
    x <> y ->
    store_update_state x f s = Some s' ->
    store_update_state x f (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y f T v s s' Hneq Hupdate.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite Hupdate. reflexivity.
Qed.

Lemma store_update_val_store_add_diff :
  forall x y T v v_new s s',
    x <> y ->
    store_update_val x v_new s = Some s' ->
    store_update_val x v_new (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y T v v_new s s' Hneq Hupdate.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite Hupdate. reflexivity.
Qed.

Lemma store_update_path_store_add_diff :
  forall x y path T v v_new s s',
    x <> y ->
    store_update_path x path v_new s = Some s' ->
    store_update_path x path v_new (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y path T v v_new s s' Hneq Hupdate.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite Hupdate. reflexivity.
Qed.

Lemma store_restore_path_store_add_diff :
  forall x y path T v s s',
    x <> y ->
    store_restore_path x path s = Some s' ->
    store_restore_path x path (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y path T v s s' Hneq Hrestore.
  unfold store_restore_path in *.
  eapply store_update_state_store_add_diff; eassumption.
Qed.

Lemma store_update_state_store_add_inv :
  forall x y f T v s s_hidden',
    x <> y ->
    store_update_state x f (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_update_state x f s = Some s'.
Proof.
  intros x y f T v s s_hidden' Hneq Hupdate.
  unfold store_add in Hupdate. simpl in Hupdate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - destruct (store_update_state x f s) as [s' |] eqn:Hbase;
      try discriminate.
    inversion Hupdate; subst.
    exists s'. split; reflexivity.
Qed.

Lemma store_update_val_store_add_inv :
  forall x y T v v_new s s_hidden',
    x <> y ->
    store_update_val x v_new (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_update_val x v_new s = Some s'.
Proof.
  intros x y T v v_new s s_hidden' Hneq Hupdate.
  unfold store_add in Hupdate. simpl in Hupdate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - destruct (store_update_val x v_new s) as [s' |] eqn:Hbase;
      try discriminate.
    inversion Hupdate; subst.
    exists s'. split; reflexivity.
Qed.

Lemma store_update_path_store_add_inv :
  forall x y path T v v_new s s_hidden',
    x <> y ->
    store_update_path x path v_new (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_update_path x path v_new s = Some s'.
Proof.
  intros x y path T v v_new s s_hidden' Hneq Hupdate.
  unfold store_add in Hupdate. simpl in Hupdate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - destruct (store_update_path x path v_new s) as [s' |] eqn:Hbase;
      try discriminate.
    inversion Hupdate; subst.
    exists s'. split; reflexivity.
Qed.

Lemma store_restore_path_store_add_inv :
  forall x y path T v s s_hidden',
    x <> y ->
    store_restore_path x path (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_restore_path x path s = Some s'.
Proof.
  intros x y path T v s s_hidden' Hneq Hrestore.
  unfold store_restore_path in *.
  eapply store_update_state_store_add_inv; eassumption.
Qed.

Lemma store_consume_path_store_add_inv :
  forall x y path T v s s_hidden',
    x <> y ->
    store_consume_path x path (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_consume_path x path s = Some s'.
Proof.
  intros x y path T v s s_hidden' Hneq Hconsume.
  unfold store_consume_path in *.
  rewrite store_lookup_store_add_diff in Hconsume by exact Hneq.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_store_add_inv; eassumption.
Qed.

Lemma value_fields_refs_exclude_lookup :
  forall root fields fname v,
    value_fields_refs_exclude_root root fields ->
    (let fix lookup (fields0 : list (string * value)) : option value :=
       match fields0 with
       | [] => None
       | (name, fv) :: tail =>
           if String.eqb fname name then Some fv else lookup tail
       end in lookup fields) = Some v ->
    value_refs_exclude_root root v.
Proof.
  intros root fields.
  induction fields as [| [name fv] tail IH]; intros fname v Hfields Hlookup;
    simpl in Hlookup; try discriminate.
  inversion Hfields; subst.
  destruct (String.eqb fname name) eqn:Hname.
  - inversion Hlookup; subst. assumption.
  - eapply IH; eassumption.
Qed.

Lemma value_refs_exclude_lookup_ref_neq :
  forall root v path x rpath,
    value_refs_exclude_root root v ->
    value_lookup_path v path = Some (VRef x rpath) ->
    x <> root.
Proof.
  intros root v path.
  revert v.
  induction path as [| fname rest IH]; intros v x rpath Hexcl Hlookup.
  - simpl in Hlookup. inversion Hlookup; subst v.
    inversion Hexcl; subst.
    match goal with
    | Hneqb : ident_eqb root x = false |- _ =>
        apply ident_eqb_neq in Hneqb;
        intros Heq; apply Hneqb; symmetry; exact Heq
    end.
  - simpl in Hlookup.
    destruct v; try discriminate.
    inversion Hexcl; subst.
    destruct
      ((fix lookup (fields0 : list (string * value)) : option value :=
          match fields0 with
          | [] => None
          | (name, fv) :: tail =>
              if String.eqb fname name then Some fv else lookup tail
          end) l) as [fv |] eqn:Hfield; try discriminate.
    eapply IH.
    + eapply value_fields_refs_exclude_lookup; eassumption.
    + exact Hlookup.
Qed.

Lemma value_refs_exclude_lookup_path :
  forall root v path v_path,
    value_refs_exclude_root root v ->
    value_lookup_path v path = Some v_path ->
    value_refs_exclude_root root v_path.
Proof.
  intros root v path.
  revert v.
  induction path as [| fname rest IH]; intros v v_path Hexcl Hlookup.
  - simpl in Hlookup. inversion Hlookup; subst. exact Hexcl.
  - simpl in Hlookup.
    destruct v; try discriminate.
    inversion Hexcl; subst.
    destruct
      ((fix lookup (fields0 : list (string * value)) : option value :=
          match fields0 with
          | [] => None
          | (name, fv) :: tail =>
              if String.eqb fname name then Some fv else lookup tail
          end) l) as [fv |] eqn:Hfield; try discriminate.
    eapply IH.
    + eapply value_fields_refs_exclude_lookup; eassumption.
    + exact Hlookup.
Qed.

Lemma store_refs_exclude_lookup :
  forall root s y se,
    store_refs_exclude_root root s ->
    store_lookup y s = Some se ->
    store_entry_refs_exclude_root root se.
Proof.
  intros root s.
  induction s as [| se_head rest IH]; intros y se Hexcl Hlookup;
    simpl in Hlookup; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb y (se_name se_head)) eqn:Hy.
  - inversion Hlookup; subst. assumption.
  - eapply IH; eassumption.
Qed.

Lemma store_refs_exclude_lookup_value :
  forall root s y se,
    store_refs_exclude_root root s ->
    store_lookup y s = Some se ->
    value_refs_exclude_root root (se_val se).
Proof.
  intros root s y se Hrefs Hlookup.
  pose proof (store_refs_exclude_lookup root s y se Hrefs Hlookup) as Hentry.
  destruct se as [sx sT sv sst].
  inversion Hentry; subst. assumption.
Qed.

Lemma store_refs_exclude_lookup_ref_neq :
  forall root s y se path x rpath,
    store_refs_exclude_root root s ->
    store_lookup y s = Some se ->
    value_lookup_path (se_val se) path = Some (VRef x rpath) ->
    x <> root.
Proof.
  intros root s.
  induction s as [| [sx sT sv sst] rest IH]; intros y se path x rpath Hexcl
    Hlookup Hvalue; simpl in Hlookup; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb y sx) eqn:Hy.
  - inversion Hlookup; subst se.
    match goal with
    | Hentry : store_entry_refs_exclude_root root (MkStoreEntry sx sT sv sst) |- _ =>
        inversion Hentry; subst
    end.
    match goal with
    | Hvalue_excl : value_refs_exclude_root root sv |- _ =>
        eapply value_refs_exclude_lookup_ref_neq; eassumption
    end.
  - eapply IH; eassumption.
Qed.

Lemma store_mark_used_refs_exclude_root :
  forall root x s,
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (store_mark_used x s).
Proof.
  intros root x s Hexcl.
  induction Hexcl as [| [sx sT sv sst] rest Hentry Hrest IH];
    simpl; try constructor.
  inversion Hentry; subst.
  destruct (ident_eqb x sx).
  - constructor.
    + constructor. assumption.
    + exact Hrest.
  - constructor.
    + constructor. assumption.
    + exact IH.
Qed.

Lemma store_update_state_refs_exclude_root :
  forall root x f s s',
    store_refs_exclude_root root s ->
    store_update_state x f s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x f s.
  induction s as [| [sx sT sv sst] rest IH]; intros s' Hexcl Hupdate;
    simpl in Hupdate; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb x sx) eqn:Hx.
  - inversion Hupdate; subst.
    match goal with
    | Hentry : store_entry_refs_exclude_root root
        (MkStoreEntry sx sT sv sst) |- _ =>
        inversion Hentry; subst
    end.
    constructor.
    + constructor. assumption.
    + assumption.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma store_restore_path_refs_exclude_root :
  forall root x path s s',
    store_refs_exclude_root root s ->
    store_restore_path x path s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x path s s' Hexcl Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_update_state_refs_exclude_root; eassumption.
Qed.

Lemma store_consume_path_refs_exclude_root :
  forall root x path s s',
    store_refs_exclude_root root s ->
    store_consume_path x path s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x path s s' Hexcl Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_refs_exclude_root; eassumption.
Qed.

Lemma store_update_val_refs_exclude_root :
  forall root x v_new s s',
    value_refs_exclude_root root v_new ->
    store_refs_exclude_root root s ->
    store_update_val x v_new s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x v_new s.
  induction s as [| [sx sT sv sst] rest IH]; intros s' Hv Hexcl Hupdate;
    simpl in Hupdate; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb x sx) eqn:Hx.
  - inversion Hupdate; subst.
    constructor.
    + constructor. exact Hv.
    + assumption.
  - destruct (store_update_val x v_new rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma value_update_path_refs_exclude_root :
  forall root v path v_new v',
    value_refs_exclude_root root v ->
    value_refs_exclude_root root v_new ->
    value_update_path v path v_new = Some v' ->
    value_refs_exclude_root root v'.
Proof.
  intros root v path.
  revert v.
  induction path as [| fname rest IH]; intros v v_new v' Hv Hvnew Hupdate.
  - destruct v; simpl in Hupdate; inversion Hupdate; subst; exact Hvnew.
  - destruct v; simpl in Hupdate; try discriminate.
    inversion Hv; subst.
    destruct
      ((fix update (fields : list (string * value)) :
          option (list (string * value)) :=
          match fields with
          | [] => None
          | (name, fv) :: tail =>
              if String.eqb fname name
              then match value_update_path fv rest v_new with
                   | Some fv' => Some ((name, fv') :: tail)
                   | None => None
                   end
              else match update tail with
                   | Some tail' => Some ((name, fv) :: tail')
                   | None => None
                   end
          end) l) as [fields' |] eqn:Hfields; try discriminate.
    assert (Hfields_excl :
      forall fields fields',
        value_fields_refs_exclude_root root fields ->
        (fix update (fields0 : list (string * value)) :
            option (list (string * value)) :=
            match fields0 with
            | [] => None
            | (name, fv) :: tail =>
                if String.eqb fname name
                then match value_update_path fv rest v_new with
                     | Some fv' => Some ((name, fv') :: tail)
                     | None => None
                     end
                else match update tail with
                     | Some tail' => Some ((name, fv) :: tail')
                     | None => None
                     end
            end) fields = Some fields' ->
        value_fields_refs_exclude_root root fields').
    { clear Hfields.
      induction fields as [| [name fv] tail IHfields];
        intros fields_out Hfields_excl Hupd; simpl in Hupd; try discriminate.
      inversion Hfields_excl; subst.
      destruct (String.eqb fname name) eqn:Hname.
      - destruct (value_update_path fv rest v_new) as [fv' |] eqn:Hfv;
          try discriminate.
        inversion Hupd; subst.
        constructor.
        + eapply IH.
          * eassumption.
          * exact Hvnew.
          * exact Hfv.
        + assumption.
      - destruct
          ((fix update (fields0 : list (string * value)) :
              option (list (string * value)) :=
              match fields0 with
              | [] => None
              | (name0, fv0) :: tail0 =>
                  if String.eqb fname name0
                  then match value_update_path fv0 rest v_new with
                       | Some fv' => Some ((name0, fv') :: tail0)
                       | None => None
                       end
                  else match update tail0 with
                       | Some tail' => Some ((name0, fv0) :: tail')
                       | None => None
                       end
              end) tail) as [tail' |] eqn:Htail; try discriminate.
        inversion Hupd; subst.
        constructor.
        + assumption.
        + eapply IHfields.
          * eassumption.
          * reflexivity. }
    inversion Hupdate; subst.
    constructor.
    eapply Hfields_excl; eassumption.
Qed.

Lemma store_update_path_refs_exclude_root :
  forall root x path v_new s s',
    value_refs_exclude_root root v_new ->
    store_refs_exclude_root root s ->
    store_update_path x path v_new s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x path v_new s.
  induction s as [| [sx sT sv sst] rest IH]; intros s' Hv Hexcl Hupdate;
    simpl in Hupdate; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb x sx) eqn:Hx.
  - destruct (value_update_path sv path v_new) as [sv' |] eqn:Hvalue;
      try discriminate.
    inversion Hupdate; subst.
    match goal with
    | Hentry : store_entry_refs_exclude_root root
        (MkStoreEntry sx sT sv sst) |- _ =>
        inversion Hentry; subst
    end.
    constructor.
    + constructor.
      eapply value_update_path_refs_exclude_root.
      * eassumption.
      * exact Hv.
      * exact Hvalue.
    + assumption.
  - destruct (store_update_path x path v_new rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma eval_place_store_add_strip :
  forall s p y path x T hidden,
    place_name p <> x ->
    store_refs_exclude_root x s ->
    eval_place (store_add x T hidden s) p y path ->
    y <> x /\ eval_place s p y path.
Proof.
  intros s p.
  induction p as [z | p IH | p IH]; intros y path x T hidden
    Hplace_fresh Hrefs Heval.
  - inversion Heval; subst.
    simpl in Hplace_fresh.
    split; try assumption.
    eapply EvalPlace_Var.
    match goal with
    | Hlookup : store_lookup _ (store_add x T hidden s) = Some _ |- _ =>
        rewrite store_lookup_store_add_diff in Hlookup by exact Hplace_fresh;
        exact Hlookup
    end.
  - inversion Heval; subst.
    simpl in Hplace_fresh.
    match goal with
    | Hplace : eval_place (store_add x T hidden s) p ?r ?rpath |- _ =>
        destruct (IH r rpath x T hidden Hplace_fresh Hrefs Hplace)
          as [Hrneq Heval_base]
    end.
    match goal with
    | Hlookup : store_lookup ?r (store_add x T hidden s) = Some _ |- _ =>
        rewrite store_lookup_store_add_diff in Hlookup by exact Hrneq
    end.
    split.
    + eapply store_refs_exclude_lookup_ref_neq; eassumption.
    + eapply EvalPlace_Deref; eassumption.
  - inversion Heval; subst.
    simpl in Hplace_fresh.
    match goal with
    | Hplace : eval_place (store_add x T hidden s) p ?x0 ?path0 |- _ =>
        destruct (IH x0 path0 x T hidden Hplace_fresh Hrefs Hplace)
          as [Hneq Heval_base]
    end.
    split; try assumption.
    apply EvalPlace_Field. exact Heval_base.
Qed.
