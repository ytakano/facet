From Facet.TypeSystem Require Import TypeSafetyRootsReadyStore.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_roots_within_named_fresh_refs_exclude_root :
  forall R s root,
    store_roots_within R s ->
    root_env_store_roots_named R s ->
    ~ In root (store_names s) ->
    store_refs_exclude_root root s.
Proof.
  intros R s root Hroots Hnamed Hfresh.
  eapply store_roots_exclude_root.
  - exact Hroots.
  - unfold root_env_store_roots_named, root_env_excludes, roots_exclude in *.
    intros y roots Hlookup _ Hin.
    apply Hfresh. eapply Hnamed; eassumption.
  - intros se Hin Heq. apply Hfresh.
    rewrite <- Heq. apply store_names_in_store_entry. exact Hin.
Qed.

Lemma root_set_union_in_right :
  forall x roots_left roots_right,
    In x roots_right ->
    In x (root_set_union roots_left roots_right).
Proof.
  intros x roots_left roots_right Hin.
  induction roots_left as [| y ys IH]; simpl; try assumption.
  destruct (existsb (root_atom_eqb y) roots_right).
  - apply IH.
  - right. apply IH.
Qed.

Lemma root_set_union_in_left :
  forall x roots_left roots_right,
    In x roots_left ->
    In x (root_set_union roots_left roots_right).
Proof.
  intros x roots_left roots_right Hin.
  induction roots_left as [| y ys IH]; simpl in *; try contradiction.
  destruct Hin as [Hin | Hin].
  - subst y.
    destruct (existsb (root_atom_eqb x) roots_right) eqn:Hexists.
    + apply root_set_union_in_right.
      apply existsb_exists in Hexists.
      destruct Hexists as [z [Hz_in Hz_eq]].
      apply root_atom_eqb_eq in Hz_eq. subst z. exact Hz_in.
    + simpl. left. reflexivity.
  - destruct (existsb (root_atom_eqb y) roots_right).
    + apply IH. exact Hin.
    + simpl. right. apply IH. exact Hin.
Qed.

Lemma value_roots_within_weaken :
  (forall roots v,
    value_roots_within roots v ->
    forall roots',
      (forall x, In x roots -> In x roots') ->
      value_roots_within roots' v) /\
  (forall R se,
    store_entry_roots_within R se ->
    forall R',
      (forall x roots, root_env_lookup x R = Some roots ->
        exists roots', root_env_lookup x R' = Some roots' /\
          forall y, In y roots -> In y roots') ->
      store_entry_roots_within R' se) /\
  (forall R s,
    store_roots_within R s ->
    forall R',
      (forall x roots, root_env_lookup x R = Some roots ->
        exists roots', root_env_lookup x R' = Some roots' /\
          forall y, In y roots -> In y roots') ->
      store_roots_within R' s) /\
  (forall roots fields,
    value_fields_roots_within roots fields ->
    forall roots',
      (forall x, In x roots -> In x roots') ->
      value_fields_roots_within roots' fields).
Proof.
  apply value_roots_within_mutind; intros; try solve [constructor; eauto].
  - constructor.
    intros root Hexclude.
    match goal with
    | Henum : forall root, roots_exclude root _ -> _ |- _ =>
        apply Henum
    end.
    unfold roots_exclude in *.
    intros Hin.
    apply Hexclude.
    apply H. exact Hin.
  - constructor.
    intros root Hexclude.
    match goal with
    | Hclosure : forall root, roots_exclude root _ -> _ |- _ =>
        apply Hclosure
    end.
    unfold roots_exclude in *.
    intros Hin.
    apply Hexclude.
    apply H. exact Hin.
  - match goal with
    | Hlookup : root_env_lookup ?x ?R = Some ?roots,
      Hweaken : forall x roots,
          root_env_lookup x ?R = Some roots ->
          exists roots', root_env_lookup x ?R' = Some roots' /\
            forall y, In y roots -> In y roots',
      IH : forall roots', (forall x, In x ?roots -> In x roots') -> _ |- _ =>
        destruct (Hweaken x roots Hlookup) as [roots' [Hlookup' Hincl]];
        eapply SERW_Entry; [exact Hlookup' | eapply IH; exact Hincl]
    end.
Qed.

Lemma root_env_store_roots_named_weaken_store :
  forall R s s',
    root_env_store_roots_named R s ->
    (forall z, In z (store_names s) -> In z (store_names s')) ->
    root_env_store_roots_named R s'.
Proof.
  unfold root_env_store_roots_named.
  intros R s s' Hnamed Hincl x roots z Hlookup Hin.
  apply Hincl. eapply Hnamed; eassumption.
Qed.

Lemma root_env_ctx_roots_named_weaken_ctx :
  forall R Σ Σ',
    root_env_ctx_roots_named R Σ ->
    (forall z, In z (ctx_names Σ) -> In z (ctx_names Σ')) ->
    root_env_ctx_roots_named R Σ'.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ Σ' Hnamed Hincl x roots z Hlookup Hin.
  apply Hincl. eapply Hnamed; eassumption.
Qed.

Lemma root_set_store_roots_named_weaken_store :
  forall roots s s',
    root_set_store_roots_named roots s ->
    (forall z, In z (store_names s) -> In z (store_names s')) ->
    root_set_store_roots_named roots s'.
Proof.
  unfold root_set_store_roots_named.
  intros roots s s' Hnamed Hincl z Hin.
  apply Hincl. apply Hnamed. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_weaken_ctx :
  forall roots Σ Σ',
    root_set_ctx_roots_named roots Σ ->
    (forall z, In z (ctx_names Σ) -> In z (ctx_names Σ')) ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots Σ Σ' Hnamed Hincl z Hin.
  apply Hincl. apply Hnamed. exact Hin.
Qed.

Lemma root_set_store_roots_named_nil :
  forall s,
    root_set_store_roots_named [] s.
Proof.
  unfold root_set_store_roots_named.
  intros s z Hin. contradiction.
Qed.

Lemma root_set_ctx_roots_named_nil :
  forall Σ,
    root_set_ctx_roots_named [] Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros Σ z Hin. contradiction.
Qed.

Lemma root_set_store_roots_named_single :
  forall s x,
    In x (store_names s) ->
    root_set_store_roots_named [RStore x] s.
Proof.
  unfold root_set_store_roots_named.
  intros s x Hin_store z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin. subst z. exact Hin_store.
Qed.

Lemma root_set_ctx_roots_named_single :
  forall Σ x,
    In x (ctx_names Σ) ->
    root_set_ctx_roots_named [RStore x] Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros Σ x Hin_ctx z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin. subst z. exact Hin_ctx.
Qed.

Lemma root_set_store_roots_named_param_single :
  forall s x,
    root_set_store_roots_named [RParam x] s.
Proof.
  unfold root_set_store_roots_named.
  intros s x z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - inversion Hin.
  - contradiction.
Qed.

Lemma root_set_ctx_roots_named_param_single :
  forall Σ x,
    root_set_ctx_roots_named [RParam x] Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros Σ x z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - inversion Hin.
  - contradiction.
Qed.

Lemma root_set_store_roots_named_equiv :
  forall roots roots' s,
    root_set_equiv roots roots' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots' s.
Proof.
  unfold root_set_store_roots_named.
  intros roots roots' s Heq Hnamed z Hin.
  apply Hnamed. apply Heq. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_equiv :
  forall roots roots' Σ,
    root_set_equiv roots roots' ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots' Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots roots' Σ Heq Hnamed z Hin.
  apply Hnamed. apply Heq. exact Hin.
Qed.

Lemma store_roots_within_equiv :
  forall R R' s,
    root_env_equiv R R' ->
    store_roots_within R s ->
    store_roots_within R' s.
Proof.
  intros R R' s Heq Hroots.
  eapply (proj2 (proj2 value_roots_within_weaken)).
  - exact Hroots.
  - intros x roots Hlookup.
    destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
      as [roots' [Hlookup' Hroots_equiv]].
    exists roots'. split.
    + exact Hlookup'.
    + intros atom Hin.
      apply Hroots_equiv. exact Hin.
Qed.

Lemma root_set_store_roots_named_union :
  forall roots_left roots_right s,
    root_set_store_roots_named roots_left s ->
    root_set_store_roots_named roots_right s ->
    root_set_store_roots_named
      (root_set_union roots_left roots_right) s.
Proof.
  unfold root_set_store_roots_named.
  intros roots_left roots_right s Hleft Hright z Hin.
  apply root_set_union_in_inv in Hin.
  destruct Hin as [Hin | Hin].
  - apply Hleft. exact Hin.
  - apply Hright. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_union :
  forall roots_left roots_right Σ,
    root_set_ctx_roots_named roots_left Σ ->
    root_set_ctx_roots_named roots_right Σ ->
    root_set_ctx_roots_named
      (root_set_union roots_left roots_right) Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots_left roots_right Σ Hleft Hright z Hin.
  apply root_set_union_in_inv in Hin.
  destruct Hin as [Hin | Hin].
  - apply Hleft. exact Hin.
  - apply Hright. exact Hin.
Qed.

Lemma root_set_store_roots_named_union_inv_l :
  forall roots_left roots_right s,
    root_set_store_roots_named (root_set_union roots_left roots_right) s ->
    root_set_store_roots_named roots_left s.
Proof.
  unfold root_set_store_roots_named.
  intros roots_left roots_right s Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_l. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_union_inv_l :
  forall roots_left roots_right Σ,
    root_set_ctx_roots_named (root_set_union roots_left roots_right) Σ ->
    root_set_ctx_roots_named roots_left Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots_left roots_right Σ Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_l. exact Hin.
Qed.

Lemma root_set_store_roots_named_union_inv_r :
  forall roots_left roots_right s,
    root_set_store_roots_named (root_set_union roots_left roots_right) s ->
    root_set_store_roots_named roots_right s.
Proof.
  unfold root_set_store_roots_named.
  intros roots_left roots_right s Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_r. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_union_inv_r :
  forall roots_left roots_right Σ,
    root_set_ctx_roots_named (root_set_union roots_left roots_right) Σ ->
    root_set_ctx_roots_named roots_right Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots_left roots_right Σ Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_r. exact Hin.
Qed.

Lemma root_sets_store_roots_named_union :
  forall sets s,
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    root_set_store_roots_named (root_sets_union sets) s.
Proof.
  intros sets s Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH]; simpl.
  - apply root_set_store_roots_named_nil.
  - apply root_set_store_roots_named_union; assumption.
Qed.

Lemma root_sets_union_store_roots_named_excludes_name :
  forall roots_list s x,
    Forall (fun roots => root_set_store_roots_named roots s) roots_list ->
    ~ In x (store_names s) ->
    roots_exclude x (root_sets_union roots_list).
Proof.
  intros roots_list s x Hnamed Hfresh.
  apply roots_exclude_root_sets_union.
  induction Hnamed as [| roots roots_list Hroot Hrest IH].
  - constructor.
  - constructor.
    + unfold root_set_store_roots_named, roots_exclude in *.
      intros Hin. apply Hfresh. apply Hroot. exact Hin.
    + exact IH.
Qed.

Lemma root_sets_ctx_roots_named_union :
  forall sets Σ,
    Forall (fun roots => root_set_ctx_roots_named roots Σ) sets ->
    root_set_ctx_roots_named (root_sets_union sets) Σ.
Proof.
  intros sets Σ Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH]; simpl.
  - apply root_set_ctx_roots_named_nil.
  - apply root_set_ctx_roots_named_union; assumption.
Qed.

Lemma root_sets_store_roots_named_weaken_store :
  forall sets s s',
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    (forall z, In z (store_names s) -> In z (store_names s')) ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s s' Hsets Hincl.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_weaken_store; eassumption.
    + apply IH.
Qed.

Lemma root_sets_ctx_roots_named_weaken_ctx :
  forall sets Σ Σ',
    Forall (fun roots => root_set_ctx_roots_named roots Σ) sets ->
    (forall z, In z (ctx_names Σ) -> In z (ctx_names Σ')) ->
    Forall (fun roots => root_set_ctx_roots_named roots Σ') sets.
Proof.
  intros sets Σ Σ' Hsets Hincl.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_ctx_roots_named_weaken_ctx; eassumption.
    + apply IH.
Qed.
