From Facet.TypeSystem Require Import TypeSafetyRootsReadyStore.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyRootSets.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_update_state_names :
  forall s x f s',
    store_update_state x f s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x f s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate. reflexivity.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x f rest' Htail). reflexivity.
Qed.

Lemma store_update_val_names :
  forall s x v s',
    store_update_val x v s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x v s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate. reflexivity.
  - destruct (store_update_val x v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x v rest' Htail). reflexivity.
Qed.

Lemma store_update_path_names :
  forall s x path v s',
    store_update_path x path v s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x path v s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - destruct (value_update_path (se_val se) path v) as [v' |] eqn:Hvalue;
      try discriminate.
    inversion Hupdate. reflexivity.
  - destruct (store_update_path x path v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x path v rest' Htail). reflexivity.
Qed.

Lemma store_restore_path_names :
  forall s x path s',
    store_restore_path x path s = Some s' ->
    store_names s' = store_names s.
Proof.
  unfold store_restore_path.
  intros s x path s' Hrestore.
  eapply store_update_state_names. exact Hrestore.
Qed.

Lemma store_consume_path_names :
  forall s x path s',
    store_consume_path x path s = Some s' ->
    store_names s' = store_names s.
Proof.
  unfold store_consume_path.
  intros s x path s' Hconsume.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_names. exact Hconsume.
Qed.

Lemma root_env_store_roots_named_store_add :
  forall R s x T v,
    root_env_store_roots_named R s ->
    root_env_store_roots_named R (store_add x T v s).
Proof.
  intros R s x T v Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_set_store_roots_named_store_add :
  forall roots s x T v,
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots (store_add x T v s).
Proof.
  intros roots s x T v Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_store_roots_named_add_env_store_add :
  forall R s x roots T v,
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    root_env_store_roots_named (root_env_add x roots R)
      (store_add x T v s).
Proof.
  intros R s x roots T v Henv Hroots.
  unfold root_env_store_roots_named.
  intros y roots_y z Hlookup Hin.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - inversion Hlookup. subst roots_y. simpl. right.
    apply Hroots. exact Hin.
  - simpl. right. eapply Henv; eassumption.
Qed.

Lemma root_env_store_keys_named_add_env_store_add :
  forall R s x roots T v,
    root_env_store_keys_named R s ->
    root_env_store_keys_named (root_env_add x roots R)
      (store_add x T v s).
Proof.
  intros R s x roots T v Hkeys.
  unfold root_env_store_keys_named.
  apply root_env_keys_named_add.
  - simpl. left. reflexivity.
  - eapply root_env_keys_named_weaken.
    + exact Hkeys.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_store_roots_named_store_remove_excluding :
  forall R s x,
    (forall y roots,
      root_env_lookup y R = Some roots ->
      roots_exclude x roots) ->
    root_env_store_roots_named R s ->
    (forall z,
      In z (store_names s) ->
      z <> x ->
      In z (store_names (store_remove x s))) ->
    root_env_store_roots_named R (store_remove x s).
Proof.
  unfold root_env_store_roots_named.
  intros R s x Hexcludes Hnamed Hremain y roots z Hlookup Hin.
  apply Hremain.
  - eapply Hnamed; eassumption.
  - intros Heq. subst z.
    unfold roots_exclude in Hexcludes.
    eapply Hexcludes; eassumption.
Qed.

Lemma root_set_store_roots_named_store_remove_excluding :
  forall roots s x,
    roots_exclude x roots ->
    root_set_store_roots_named roots s ->
    (forall z,
      In z (store_names s) ->
      z <> x ->
      In z (store_names (store_remove x s))) ->
    root_set_store_roots_named roots (store_remove x s).
Proof.
  unfold root_set_store_roots_named, roots_exclude.
  intros roots s x Hexclude Hnamed Hremain z Hin.
  apply Hremain.
  - apply Hnamed. exact Hin.
  - intros Heq. subst z. apply Hexclude. exact Hin.
Qed.

Lemma root_env_store_roots_named_store_mark_used :
  forall R s x,
    root_env_store_roots_named R s ->
    root_env_store_roots_named R (store_mark_used x s).
Proof.
  intros R s x Hnamed.
  assert (Hincl :
    forall z,
      In z (store_names s) ->
      In z (store_names (store_mark_used x s))).
  {
    clear Hnamed.
    induction s as [| se rest IH]; intros z Hin; simpl in *; try contradiction.
    destruct (ident_eqb x (se_name se)); simpl in *.
    - exact Hin.
    - destruct Hin as [Hin | Hin].
      + left. exact Hin.
      + right. apply IH. exact Hin.
  }
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - exact Hincl.
Qed.

Lemma root_set_store_roots_named_store_mark_used :
  forall roots s x,
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots (store_mark_used x s).
Proof.
  intros roots s x Hnamed.
  assert (Hincl :
    forall z,
      In z (store_names s) ->
      In z (store_names (store_mark_used x s))).
  {
    clear roots Hnamed.
    induction s as [| se rest IH]; intros z Hin; simpl in *; try contradiction.
    destruct (ident_eqb x (se_name se)); simpl in *.
    - exact Hin.
    - destruct Hin as [Hin | Hin].
      + left. exact Hin.
      + right. apply IH. exact Hin.
  }
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - exact Hincl.
Qed.

Lemma root_sets_store_roots_named_store_add :
  forall sets s x T v,
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall
      (fun roots => root_set_store_roots_named roots (store_add x T v s))
      sets.
Proof.
  intros sets s x T v Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + apply root_set_store_roots_named_store_add. exact Hroot.
    + apply IH.
Qed.

Lemma root_sets_store_roots_named_store_mark_used :
  forall sets s x,
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall
      (fun roots => root_set_store_roots_named roots (store_mark_used x s))
      sets.
Proof.
  intros sets s x Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + apply root_set_store_roots_named_store_mark_used. exact Hroot.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_update_state :
  forall R s x f s',
    store_update_state x f s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x f s' Hupdate Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_state_names s x f s' Hupdate).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_update_state :
  forall roots s x f s',
    store_update_state x f s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x f s' Hupdate Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_state_names s x f s' Hupdate).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_update_state :
  forall sets s x f s',
    store_update_state x f s = Some s' ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s x f s' Hupdate Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_store_update_state; eassumption.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_update_val :
  forall R s x v s',
    store_update_val x v s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x v s' Hupdate Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_val_names s x v s' Hupdate).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_update_val :
  forall roots s x v s',
    store_update_val x v s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x v s' Hupdate Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_val_names s x v s' Hupdate).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_update_val :
  forall sets s x v s',
    store_update_val x v s = Some s' ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s x v s' Hupdate Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_store_update_val; eassumption.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_update_path :
  forall R s x path v s',
    store_update_path x path v s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x path v s' Hupdate Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_path_names s x path v s' Hupdate).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_update_path :
  forall roots s x path v s',
    store_update_path x path v s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x path v s' Hupdate Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_path_names s x path v s' Hupdate).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_update_path :
  forall sets s x path v s',
    store_update_path x path v s = Some s' ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s x path v s' Hupdate Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_store_update_path; eassumption.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_restore_path :
  forall R s x path s',
    store_restore_path x path s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x path s' Hrestore Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_restore_path_names s x path s' Hrestore).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_restore_path :
  forall roots s x path s',
    store_restore_path x path s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x path s' Hrestore Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_restore_path_names s x path s' Hrestore).
    exact Hin.
Qed.

Lemma root_env_store_roots_named_store_consume_path :
  forall R s x path s',
    store_consume_path x path s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x path s' Hconsume Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_consume_path_names s x path s' Hconsume).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_consume_path :
  forall roots s x path s',
    store_consume_path x path s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x path s' Hconsume Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_consume_path_names s x path s' Hconsume).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_remove_excluding :
  forall sets s x,
    Forall (roots_exclude x) sets ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    (forall z,
      In z (store_names s) ->
      z <> x ->
      In z (store_names (store_remove x s))) ->
    Forall
      (fun roots => root_set_store_roots_named roots (store_remove x s))
      sets.
Proof.
  intros sets s x Hexcludes Hsets Hremain.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - inversion Hexcludes as [| ? ? Hexclude Hrest_excludes]. subst.
    constructor.
    + eapply root_set_store_roots_named_store_remove_excluding; eassumption.
    + apply IH. exact Hrest_excludes.
Qed.

Lemma root_env_store_roots_named_add_env :
  forall R s x roots,
    root_env_store_roots_named R s ->
    (forall z, In (RStore z) roots -> In z (store_names s)) ->
    root_env_store_roots_named (root_env_add x roots R) s.
Proof.
  unfold root_env_store_roots_named.
  intros R s x roots Hnamed Hroots y roots_y z Hlookup Hin.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
  - eapply Hnamed; eassumption.
Qed.

Lemma root_env_ctx_roots_named_add_env :
  forall R Σ x roots,
    root_env_ctx_roots_named R Σ ->
    (forall z, In (RStore z) roots -> In z (ctx_names Σ)) ->
    root_env_ctx_roots_named (root_env_add x roots R) Σ.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ x roots Hnamed Hroots y roots_y z Hlookup Hin.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
  - eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_roots_named_add_env_named :
  forall R s x roots,
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    root_env_store_roots_named (root_env_add x roots R) s.
Proof.
  intros R s x roots Henv Hroots.
  apply root_env_store_roots_named_add_env.
  - exact Henv.
  - exact Hroots.
Qed.

Lemma root_env_ctx_roots_named_add_env_named :
  forall R Σ x roots,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named (root_env_add x roots R) Σ.
Proof.
  intros R Σ x roots Henv Hroots.
  apply root_env_ctx_roots_named_add_env.
  - exact Henv.
  - exact Hroots.
Qed.

Lemma root_env_store_roots_named_remove_env :
  forall R s x,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named (root_env_remove x R) s.
Proof.
  unfold root_env_store_roots_named.
  intros R s x Hnodup Hnamed y roots z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - apply ident_eqb_eq in Hxr. subst r.
    eapply Hnamed.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        exfalso. apply Hr_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup.
      * rewrite Hyx. exact Hlookup.
    + exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_ctx_roots_named_remove_env :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named (root_env_remove x R) Σ.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ x Hnodup Hnamed y roots z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - apply ident_eqb_eq in Hxr. subst r.
    eapply Hnamed.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        exfalso. apply Hr_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup.
      * rewrite Hyx. exact Hlookup.
    + exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_store_roots_named_update_env :
  forall R s x roots,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    (forall z, In (RStore z) roots -> In z (store_names s)) ->
    root_env_store_roots_named (root_env_update x roots R) s.
Proof.
  unfold root_env_store_roots_named.
  intros R s x roots Hnodup Hnamed Hroots y roots_y z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y.
      eapply Hnamed.
      * simpl. rewrite Hyp. reflexivity.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_ctx_roots_named_update_env :
  forall R Σ x roots,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    (forall z, In (RStore z) roots -> In z (ctx_names Σ)) ->
    root_env_ctx_roots_named (root_env_update x roots R) Σ.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ x roots Hnodup Hnamed Hroots y roots_y z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y.
      eapply Hnamed.
      * simpl. rewrite Hyp. reflexivity.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_store_roots_named_update_env_named :
  forall R s x roots,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    root_env_store_roots_named (root_env_update x roots R) s.
Proof.
  intros R s x roots Hrn Henv Hroots.
  apply root_env_store_roots_named_update_env; assumption.
Qed.

Lemma root_env_ctx_roots_named_update_env_named :
  forall R Σ x roots,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named (root_env_update x roots R) Σ.
Proof.
  intros R Σ x roots Hrn Henv Hroots.
  apply root_env_ctx_roots_named_update_env; assumption.
Qed.

Lemma store_roots_within_lookup_none :
  forall R s x,
    store_roots_within R s ->
    root_env_lookup x R = None ->
    store_lookup x s = None.
Proof.
  intros R s x Hwithin Hlookup_none.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - reflexivity.
  - inversion Hentry; subst.
    destruct (ident_eqb x sx) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst sx.
      rewrite Hlookup_none in H. discriminate.
    + simpl. rewrite Heq. apply IH. exact Hlookup_none.
Qed.

Lemma store_roots_within_lookup_value :
  forall R s x se roots,
    store_roots_within R s ->
    store_lookup x s = Some se ->
    root_env_lookup x R = Some roots ->
    value_roots_within roots (se_val se).
Proof.
  intros R s x se roots Hwithin Hlookup Hroot.
  revert x se roots Hlookup Hroot.
  induction Hwithin as [R | R se_head rest Hentry Hrest IH];
    intros x se roots Hlookup Hroot; simpl in Hlookup; try discriminate.
  destruct se_head as [sx sT sv sst].
  simpl in Hlookup.
  inversion Hentry; subst.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    inversion Hlookup; subst se.
    match goal with
    | Hlookup_se : root_env_lookup sx R = Some ?roots_se,
      Hvalue_se : value_roots_within ?roots_se sv |- _ =>
        rewrite Hroot in Hlookup_se;
        inversion Hlookup_se; subst;
        exact Hvalue_se
    end.
  - eapply IH; eassumption.
Qed.

Lemma value_lookup_path_roots_within :
  forall roots v path v_path,
    value_roots_within roots v ->
    value_lookup_path v path = Some v_path ->
    value_roots_within roots v_path.
Proof.
  intros roots v path.
  revert roots v.
  induction path as [| f rest IH]; intros roots v v_path Hwithin Hlookup;
    simpl in Hlookup.
  - inversion Hlookup; subst. exact Hwithin.
  - inversion Hwithin; subst; try discriminate.
    simpl in Hlookup.
    remember (
      fix lookup (fields0 : list (string * value)) : option value :=
        match fields0 with
        | [] => None
        | (name, fv) :: tail =>
            if String.eqb f name then Some fv else lookup tail
        end) as lookup.
    assert (Hfields :
      forall fs fv,
        value_fields_roots_within roots fs ->
        lookup fs = Some fv ->
        value_roots_within roots fv).
    { intros fs. subst lookup.
      induction fs as [| [fname fv] tail IHfields]; intros fv_path
        Hfields_roots Hfields_lookup; simpl in Hfields_lookup; try discriminate.
      inversion Hfields_roots; subst.
      destruct (String.eqb f fname) eqn:Hname.
      - inversion Hfields_lookup; subst. assumption.
      - eapply IHfields; eassumption. }
    destruct (lookup fields) as [fv |] eqn:Hfield_lookup; try discriminate.
    eapply IH.
    + eapply Hfields; eassumption.
    + exact Hlookup.
Qed.

Lemma store_roots_within_add_env :
  forall R s x roots,
    store_roots_within R s ->
    root_env_lookup x R = None ->
    store_roots_within (root_env_add x roots R) s.
Proof.
  intros R s x roots Hwithin Hfresh.
  induction Hwithin as [R | R se rest Hentry Hrest IH].
  - constructor.
  - inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry.
      * rewrite (root_env_lookup_add_neq x sx roots R).
        -- exact H.
        -- intros Heq. subst sx. rewrite Hfresh in H. discriminate.
      * exact H0.
    + apply IH. exact Hfresh.
Qed.

Lemma store_add_roots_within :
  forall R s x T v roots,
    store_roots_within R s ->
    root_env_lookup x R = None ->
    value_roots_within roots v ->
    store_roots_within (root_env_add x roots R) (store_add x T v s).
Proof.
  intros R s x T v roots Hstore Hfresh Hvalue.
  unfold store_add.
  constructor.
  - exact (SERW_Entry (root_env_add x roots R) x T v
      (binding_state_of_bool false) roots
      (root_env_lookup_add_eq x roots R) Hvalue).
  - apply store_roots_within_add_env; assumption.
Qed.

Lemma store_add_fresh_ref_targets_preserved :
  forall env s x T v,
    store_lookup x s = None ->
    store_ref_targets_preserved env s (store_add x T v s).
Proof.
  unfold store_ref_targets_preserved.
  intros env s x T v Hfresh y path se v_old T_old Hlookup Hvalue Htype.
  exists se, v_old.
  repeat split; try assumption.
  unfold store_add. simpl.
  destruct (ident_eqb y x) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    rewrite Hlookup in Hfresh. discriminate.
  - exact Hlookup.
Qed.

Lemma store_roots_within_remove_env :
  forall R s x,
    store_roots_within R s ->
    (forall se, In se s -> se_name se <> x) ->
    store_roots_within (root_env_remove x R) s.
Proof.
  intros R s x Hwithin Hnames.
  induction Hwithin as [R | R se rest Hentry Hrest IH].
  - constructor.
  - inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry.
      * rewrite (root_env_lookup_remove_neq x sx R).
        -- exact H.
        -- intros Hsame. subst sx.
           apply (Hnames (MkStoreEntry x sT sv sst)).
           ++ simpl. left. reflexivity.
           ++ reflexivity.
      * exact H0.
    + apply IH.
      intros se Hin. apply Hnames. simpl. right. exact Hin.
Qed.

Lemma store_remove_roots_within :
  forall R s x,
    store_roots_within R s ->
    (forall se, In se (store_remove x s) -> se_name se <> x) ->
    store_roots_within (root_env_remove x R) (store_remove x s).
Proof.
  intros R s x Hwithin Hnames.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - constructor.
  - destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply store_roots_within_remove_env.
      * exact Hrest.
      * intros se0 Hin. apply Hnames. simpl. rewrite Heq. exact Hin.
    + constructor.
      * inversion Hentry; subst.
        eapply SERW_Entry.
        -- rewrite (root_env_lookup_remove_neq x sx R).
           ++ exact H.
           ++ intros Hsame. subst sx.
              rewrite ident_eqb_refl in Heq. discriminate.
        -- exact H0.
      * apply IH.
        intros se0 Hin. apply Hnames. simpl.
        rewrite Heq. right. exact Hin.
Qed.

Lemma store_update_state_roots_within :
  forall R s x f s',
    store_roots_within R s ->
    store_update_state x f s = Some s' ->
    store_roots_within R s'.
Proof.
  intros R s x f s' Hwithin Hupdate.
  revert s' Hupdate.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; intros s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate; subst. inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry; eassumption.
    + exact Hrest.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma store_mark_used_roots_within :
  forall R s x,
    store_roots_within R s ->
    store_roots_within R (store_mark_used x s).
Proof.
  intros R s x Hwithin.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - constructor.
  - destruct (ident_eqb x (se_name se)); inversion Hentry; subst.
    + constructor.
      * econstructor; eassumption.
      * exact Hrest.
    + constructor.
      * econstructor; eassumption.
      * exact IH.
Qed.
