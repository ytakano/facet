From Facet.TypeSystem Require Import TypeSafetyRootsReadyStore.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyRootSets.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyStoreOps.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma roots_ready_store_entries_typed_names :
  forall env s_source entries Σ,
    Forall2 (store_entry_typed env s_source) entries Σ ->
    store_names entries = ctx_names Σ.
Proof.
  intros env s_source entries Σ Htyped.
  induction Htyped as [| se ce entries_tail Σ_tail Hentry _ IH].
  - reflexivity.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname _].
    simpl. rewrite Hname, IH. reflexivity.
Qed.

Lemma root_env_ctx_roots_named_store_typed :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_ctx_roots_named R Σ ->
    root_env_store_roots_named R s.
Proof.
  unfold root_env_ctx_roots_named, root_env_store_roots_named.
  intros env s Σ R Htyped Hnamed x roots z Hlookup Hin.
  rewrite (store_typed_names env s Σ Htyped).
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_ctx_roots_named_store_typed :
  forall env s Σ roots,
    store_typed env s Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_set_store_roots_named roots s.
Proof.
  unfold root_set_ctx_roots_named, root_set_store_roots_named.
  intros env s Σ roots Htyped Hnamed z Hin.
  rewrite (store_typed_names env s Σ Htyped).
  apply Hnamed. exact Hin.
Qed.

Lemma root_env_ctx_roots_named_store_typed_prefix :
  forall env s Σ R,
    store_typed_prefix env s Σ ->
    root_env_ctx_roots_named R Σ ->
    root_env_store_roots_named R s.
Proof.
  unfold root_env_ctx_roots_named, root_env_store_roots_named.
  intros env s Σ R Htyped Hnamed x roots z Hlookup Hin.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  rewrite store_names_app.
  apply in_or_app. left.
  rewrite (roots_ready_store_entries_typed_names env (entries ++ frame) entries Σ Hentries).
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_ctx_roots_named_store_typed_prefix :
  forall env s Σ roots,
    store_typed_prefix env s Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_set_store_roots_named roots s.
Proof.
  unfold root_set_ctx_roots_named, root_set_store_roots_named.
  intros env s Σ roots Htyped Hnamed z Hin.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  rewrite store_names_app.
  apply in_or_app. left.
  rewrite (roots_ready_store_entries_typed_names env (entries ++ frame) entries Σ Hentries).
  apply Hnamed. exact Hin.
Qed.

Lemma root_sets_ctx_roots_named_store_typed :
  forall env s Σ sets,
    store_typed env s Σ ->
    Forall (fun roots => root_set_ctx_roots_named roots Σ) sets ->
    Forall (fun roots => root_set_store_roots_named roots s) sets.
Proof.
  intros env s Σ sets Htyped Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_ctx_roots_named_store_typed; eassumption.
    + apply IH.
Qed.

Lemma store_typed_sctx_no_shadow :
  forall env s Σ,
    store_typed env s Σ ->
    store_no_shadow s ->
    sctx_no_shadow Σ.
Proof.
  unfold store_no_shadow, sctx_no_shadow.
  intros env s Σ Htyped Hnodup.
  rewrite <- (store_typed_names env s Σ Htyped).
  exact Hnodup.
Qed.

Lemma store_typed_store_no_shadow :
  forall env s Σ,
    store_typed env s Σ ->
    sctx_no_shadow Σ ->
    store_no_shadow s.
Proof.
  unfold store_no_shadow, sctx_no_shadow.
  intros env s Σ Htyped Hnodup.
  rewrite (store_typed_names env s Σ Htyped).
  exact Hnodup.
Qed.

Lemma store_roots_within_update_env_neq :
  forall R s x roots_update,
    store_roots_within R s ->
    (forall se, In se s -> se_name se <> x) ->
    store_roots_within (root_env_update x roots_update R) s.
Proof.
  intros R s x roots_update Hwithin Hnames.
  induction Hwithin as [R | R se rest Hentry Hrest IH].
  - constructor.
  - inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry.
      * rewrite root_env_lookup_update_neq.
        -- exact H.
        -- intros Hsame. subst sx.
           apply (Hnames (MkStoreEntry x sT sv sst)).
           ++ simpl. left. reflexivity.
           ++ reflexivity.
      * exact H0.
    + apply IH.
      intros se0 Hin. apply Hnames. simpl. right. exact Hin.
Qed.

Lemma value_roots_within_union_l :
  forall roots_old roots_new v,
    value_roots_within roots_old v ->
    value_roots_within (root_set_union roots_old roots_new) v.
Proof.
  intros roots_old roots_new v Hwithin.
  eapply (proj1 value_roots_within_weaken).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_left. exact Hin.
Qed.

Lemma value_roots_within_union_r :
  forall roots_old roots_new v,
    value_roots_within roots_new v ->
    value_roots_within (root_set_union roots_old roots_new) v.
Proof.
  intros roots_old roots_new v Hwithin.
  eapply (proj1 value_roots_within_weaken).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_right. exact Hin.
Qed.

Lemma value_fields_roots_within_union_l :
  forall roots_old roots_new fields,
    value_fields_roots_within roots_old fields ->
    value_fields_roots_within (root_set_union roots_old roots_new) fields.
Proof.
  intros roots_old roots_new fields Hwithin.
  eapply (proj2 (proj2 (proj2 value_roots_within_weaken))).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_left. exact Hin.
Qed.

Lemma value_fields_roots_within_union_r :
  forall roots_old roots_new fields,
    value_fields_roots_within roots_new fields ->
    value_fields_roots_within (root_set_union roots_old roots_new) fields.
Proof.
  intros roots_old roots_new fields Hwithin.
  eapply (proj2 (proj2 (proj2 value_roots_within_weaken))).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_right. exact Hin.
Qed.

Lemma value_update_path_roots_within_union :
  forall roots_old roots_new v path v_new v',
    value_roots_within roots_old v ->
    value_roots_within roots_new v_new ->
    value_update_path v path v_new = Some v' ->
    value_roots_within (root_set_union roots_old roots_new) v'.
Proof.
  intros roots_old roots_new v path.
  revert roots_old roots_new v.
  induction path as [| f rest IH]; intros roots_old roots_new v v_new v'
    Hwithin_old Hwithin_new Hupdate; simpl in Hupdate.
  - destruct v; simpl in Hupdate; injection Hupdate as Hsame; subst v';
      apply value_roots_within_union_r; exact Hwithin_new.
  - inversion Hwithin_old; subst; try discriminate.
    simpl in Hupdate.
    remember (
      fix update (fields0 : list (string * value)) : option (list (string * value)) :=
        match fields0 with
        | [] => None
        | (name, fv) :: tail =>
            if String.eqb f name
            then match value_update_path fv rest v_new with
                 | Some fv' => Some ((name, fv') :: tail)
                 | None => None
                 end
            else match update tail with
                 | Some tail' => Some ((name, fv) :: tail')
                 | None => None
                 end
        end) as update.
    assert (Hfields :
      forall fs fs',
        value_fields_roots_within roots_old fs ->
        update fs = Some fs' ->
        value_fields_roots_within (root_set_union roots_old roots_new) fs').
    { intros fs. subst update.
      induction fs as [| [fname fv] tail IHfields];
        intros fs' Hfields_roots Hfields_update; simpl in Hfields_update.
      - discriminate.
      - inversion Hfields_roots; subst.
        destruct (String.eqb f fname) eqn:Hname.
        + destruct (value_update_path fv rest v_new) as [fv' |] eqn:Hfv_update;
            try discriminate.
          inversion Hfields_update; subst.
          constructor.
          * eapply IH; eauto.
          * eapply (proj2 (proj2 (proj2 value_roots_within_weaken))).
            -- match goal with
               | H : value_fields_roots_within roots_old tail |- _ => exact H
               end.
            -- intros x Hin. apply root_set_union_in_left. exact Hin.
        + destruct ((
            fix update (fields0 : list (string * value)) : option (list (string * value)) :=
              match fields0 with
              | [] => None
              | (name0, fv0) :: tail0 =>
                  if String.eqb f name0
                  then match value_update_path fv0 rest v_new with
                       | Some fv' => Some ((name0, fv') :: tail0)
                       | None => None
                       end
                  else match update tail0 with
                       | Some tail' => Some ((name0, fv0) :: tail')
                       | None => None
                       end
              end) tail) as [tail' |] eqn:Htail_update; try discriminate.
          inversion Hfields_update; subst.
          constructor.
          * apply value_roots_within_union_l.
            match goal with
            | H : value_roots_within roots_old fv |- _ => exact H
            end.
          * eapply IHfields; eauto. }
    destruct (update fields) as [fields' |] eqn:Hfields_update; try discriminate.
    inversion Hupdate; subst.
    constructor.
    eapply Hfields; eauto.
Qed.

Lemma store_update_val_roots_within_union :
  forall R s x v s' roots_old roots_new,
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_lookup x R = Some roots_old ->
    value_roots_within roots_new v ->
    store_update_val x v s = Some s' ->
    store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) s'.
Proof.
  intros R s x v s' roots_old roots_new Hwithin Hnodup
    Hlookup_x Hvalue Hupdate.
  revert s' Hupdate.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; intros s' Hupdate;
    simpl in Hupdate; try discriminate.
  unfold store_no_shadow in Hnodup. simpl in Hnodup.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  inversion Hentry as [R0 sx sT sv sst roots Hlookup_se Hvalue_se]; subst R0 se.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst sx.
    rewrite ident_eqb_refl in Hupdate.
    rewrite Hlookup_x in Hlookup_se. inversion Hlookup_se; subst roots.
    inversion Hupdate; subst.
    assert (Hentry_up : store_entry_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT v sst)).
    { exact (SERW_Entry
        (root_env_update x (root_set_union roots_old roots_new) R)
        x sT v sst (root_set_union roots_old roots_new)
        (root_env_lookup_update_eq x (root_set_union roots_old roots_new)
          R roots_old Hlookup_x)
        (value_roots_within_union_r roots_old roots_new v Hvalue)). }
    assert (Hrest_up : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) rest).
    { eapply (store_roots_within_update_env_neq R rest x
        (root_set_union roots_old roots_new)).
      * exact Hrest.
      * intros se Hin Hsame.
        apply Hnotin.
        pose proof (store_entry_name_in_store_names se rest Hin) as Hin_name.
        rewrite Hsame in Hin_name. exact Hin_name. }
    exact (SRW_Cons
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT v sst) rest Hentry_up Hrest_up).
  - destruct (store_update_val x v rest) as [rest' |] eqn:Htail.
    + simpl in Hupdate. rewrite Heq in Hupdate.
      inversion Hupdate; subst.
    assert (Hentry_up : store_entry_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry sx sT sv sst)).
    { assert (Hlookup_up :
        root_env_lookup sx
          (root_env_update x (root_set_union roots_old roots_new) R) =
        Some roots).
      { rewrite root_env_lookup_update_neq.
        - exact Hlookup_se.
        - intros Hsame. subst sx. rewrite ident_eqb_refl in Heq. discriminate. }
      exact (SERW_Entry
        (root_env_update x (root_set_union roots_old roots_new) R)
        sx sT sv sst roots Hlookup_up Hvalue_se). }
    assert (Hrest_up : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) rest').
    { apply IH.
      * unfold store_no_shadow. exact Hnodup_tail.
      * exact Hlookup_x.
      * reflexivity. }
    exact (SRW_Cons
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry sx sT sv sst) rest' Hentry_up Hrest_up).
    + simpl in Hupdate. rewrite Heq in Hupdate. discriminate.
Qed.

Lemma store_update_path_roots_within_union :
  forall R s x path v_new s' roots_old roots_new,
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_lookup x R = Some roots_old ->
    value_roots_within roots_new v_new ->
    store_update_path x path v_new s = Some s' ->
    store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) s'.
Proof.
  intros R s x path v_new s' roots_old roots_new Hwithin Hnodup
    Hlookup_x Hvalue_new Hupdate.
  revert s' Hupdate.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; intros s' Hupdate;
    simpl in Hupdate; try discriminate.
  unfold store_no_shadow in Hnodup. simpl in Hnodup.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  inversion Hentry as [R0 sx sT sv sst roots Hlookup_se Hvalue_se]; subst R0 se.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst sx.
    rewrite ident_eqb_refl in Hupdate.
    rewrite Hlookup_x in Hlookup_se. inversion Hlookup_se; subst roots.
    destruct (value_update_path sv path v_new) as [sv' |] eqn:Hvalue_update.
    + simpl in Hupdate. rewrite Hvalue_update in Hupdate.
      inversion Hupdate; subst.
      assert (Hentry_up : store_entry_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT sv' sst)).
      { exact (SERW_Entry
        (root_env_update x (root_set_union roots_old roots_new) R)
        x sT sv' sst (root_set_union roots_old roots_new)
        (root_env_lookup_update_eq x (root_set_union roots_old roots_new)
          R roots_old Hlookup_x)
        (value_update_path_roots_within_union
          roots_old roots_new sv path v_new sv'
          Hvalue_se Hvalue_new Hvalue_update)). }
      assert (Hrest_up : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) rest).
      { eapply (store_roots_within_update_env_neq R rest x
        (root_set_union roots_old roots_new)).
        * exact Hrest.
        * intros se Hin Hsame.
        apply Hnotin.
        pose proof (store_entry_name_in_store_names se rest Hin) as Hin_name.
        rewrite Hsame in Hin_name. exact Hin_name. }
      exact (SRW_Cons
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT sv' sst) rest Hentry_up Hrest_up).
    + simpl in Hupdate. rewrite Hvalue_update in Hupdate. discriminate.
  - destruct (store_update_path x path v_new rest) as [rest' |] eqn:Htail.
    + simpl in Hupdate. rewrite Heq in Hupdate.
      inversion Hupdate; subst.
      assert (Hentry_up : store_entry_roots_within
        (root_env_update x (root_set_union roots_old roots_new) R)
        (MkStoreEntry sx sT sv sst)).
      { assert (Hlookup_up :
          root_env_lookup sx
            (root_env_update x (root_set_union roots_old roots_new) R) =
          Some roots).
        { rewrite root_env_lookup_update_neq.
          - exact Hlookup_se.
          - intros Hsame. subst sx. rewrite ident_eqb_refl in Heq. discriminate. }
        exact (SERW_Entry
          (root_env_update x (root_set_union roots_old roots_new) R)
          sx sT sv sst roots Hlookup_up Hvalue_se). }
      assert (Hrest_up : store_roots_within
        (root_env_update x (root_set_union roots_old roots_new) R) rest').
      { apply IH.
        * unfold store_no_shadow. exact Hnodup_tail.
        * exact Hlookup_x.
        * reflexivity. }
      exact (SRW_Cons
        (root_env_update x (root_set_union roots_old roots_new) R)
        (MkStoreEntry sx sT sv sst) rest' Hentry_up Hrest_up).
    + simpl in Hupdate. rewrite Heq in Hupdate. discriminate.
Qed.

Lemma eval_place_lookup_path_roots_within :
  forall R s p x_static path_static x_eval path_eval old_v roots,
    store_roots_within R s ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    root_env_lookup x_static R = Some roots ->
    value_roots_within roots old_v.
Proof.
  intros R s p x_static path_static x_eval path_eval old_v roots
    Hwithin Hpath_static Heval_place Hlookup_path Hroot_lookup.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  unfold store_lookup_path in Hlookup_path.
  destruct (store_lookup x_static s) as [se |] eqn:Hstore_lookup; try discriminate.
  eapply value_lookup_path_roots_within.
  - eapply store_roots_within_lookup_value; eassumption.
  - exact Hlookup_path.
Qed.

Lemma eval_place_update_path_roots_within_union :
  forall R1 s s1 s2 p x_static path_static x_eval path_eval
      v_new roots_old roots_new,
    store_roots_within R1 s1 ->
    store_no_shadow s1 ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    root_env_lookup x_static R1 = Some roots_old ->
    value_roots_within roots_new v_new ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_roots_within
      (root_env_update x_static (root_set_union roots_old roots_new) R1) s2.
Proof.
  intros R1 s s1 s2 p x_static path_static x_eval path_eval
    v_new roots_old roots_new Hwithin Hnodup Hpath_static Heval_place
    Hroot_lookup Hvalue_new Hupdate.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  eapply store_update_path_roots_within_union; eassumption.
Qed.


Lemma value_roots_within_singleton_ref_target :
  forall roots x_eval path_eval x,
    value_roots_within roots (VRef x_eval path_eval) ->
    singleton_store_root roots = Some x ->
    x_eval = x.
Proof.
  intros roots x_eval path_eval x Hwithin Hsingle.
  inversion Hwithin; subst.
  pose proof (singleton_store_root_some_equiv roots x Hsingle) as Hequiv.
  specialize (Hequiv (RStore x_eval)).
  destruct Hequiv as [Hequiv _].
  match goal with
  | Hin : In (RStore x_eval) roots |- _ => specialize (Hequiv Hin)
  end.
  simpl in Hequiv.
  destruct Hequiv as [Heq | []]. inversion Heq. reflexivity.
Qed.

Lemma singleton_store_root_ref_roots_within :
  forall roots x path x_final,
    singleton_store_root roots = Some x_final ->
    x = x_final ->
    value_roots_within roots (VRef x path).
Proof.
  intros roots x path x_final Hsingle Heq.
  subst x.
  constructor.
  destruct (singleton_store_root_some_equiv roots x_final Hsingle
    (RStore x_final)) as [_ Hin].
  apply Hin. simpl. left. reflexivity.
Qed.

Lemma eval_place_resolved_write_target_matches_root :
  forall R s p x_eval path_eval x,
    store_roots_within R s ->
    eval_place s p x_eval path_eval ->
    place_resolved_write_target R p = Some x ->
    x_eval = x.
Proof.
  intros R s p x_eval path_eval x Hwithin Heval.
  revert x.
  induction Heval; intros target_final Htarget; simpl in Htarget.
  - inversion Htarget. reflexivity.
  - eapply IHHeval; eassumption.
  - destruct (place_resolved_write_target R p) as [target_parent |] eqn:Htarget_p;
      try discriminate.
    destruct (root_env_lookup target_parent R) as [target_roots |]
      eqn:Hlookup_target; try discriminate.
    destruct (singleton_store_root target_roots) as [target_ref |] eqn:Hsingle;
      try discriminate.
    inversion Htarget; subst target_ref.
    assert (Hr : r = target_parent) by (apply (IHHeval Hwithin target_parent eq_refl)).
    subst r.
    assert (Hvalue_ref : value_roots_within target_roots (VRef x path)).
    { eapply value_lookup_path_roots_within.
      - eapply store_roots_within_lookup_value; eassumption.
      - match goal with
        | Hvalue_path : value_lookup_path (se_val se_r) rpath = Some (VRef x path) |- _ =>
            exact Hvalue_path
        end. }
    eapply value_roots_within_singleton_ref_target; eassumption.
Qed.

Lemma eval_place_resolved_write_target_ref_roots_within :
  forall R s p x path roots x_final,
    store_roots_within R s ->
    eval_place s p x path ->
    place_resolved_write_target R p = Some x_final ->
    singleton_store_root roots = Some x_final ->
    value_roots_within roots (VRef x path).
Proof.
  intros R s p x path roots x_final Hwithin Heval Htarget Hsingle.
  assert (Hx : x = x_final).
  { eapply eval_place_resolved_write_target_matches_root; eassumption. }
  eapply singleton_store_root_ref_roots_within; eassumption.
Qed.

Lemma eval_place_resolved_write_target_ref_runtime_root :
  forall R s p x path roots x_final,
    store_roots_within R s ->
    eval_place s p x path ->
    place_resolved_write_target R p = Some x_final ->
    singleton_store_root roots = Some x_final ->
    x = x_final /\ value_roots_within roots (VRef x path).
Proof.
  intros R s p x path roots x_final Hwithin Heval Htarget Hsingle.
  assert (Hx : x = x_final).
  { eapply eval_place_resolved_write_target_matches_root; eassumption. }
  split.
  - exact Hx.
  - eapply singleton_store_root_ref_roots_within; eassumption.
Qed.

Lemma eval_place_resolved_roots_write_target_ref_runtime_root :
  forall R s p x path roots x_final,
    store_roots_within R s ->
    eval_place s p x path ->
    place_resolved_roots R p = Some roots ->
    place_resolved_write_target R p = Some x_final ->
    singleton_store_root roots = Some x_final ->
    x = x_final /\ value_roots_within roots (VRef x path).
Proof.
  intros R s p x path roots x_final Hwithin Heval _ Htarget Hsingle.
  eapply eval_place_resolved_write_target_ref_runtime_root; eassumption.
Qed.

Lemma eval_place_resolved_lookup_path_roots_within :
  forall R s p x_eval path_eval old_v x roots,
    store_roots_within R s ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    place_resolved_write_target R p = Some x ->
    root_env_lookup x R = Some roots ->
    value_roots_within roots old_v.
Proof.
  intros R s p x_eval path_eval old_v x roots Hwithin Heval Hlookup_path
    Htarget Hroot_lookup.
  assert (Hx : x_eval = x).
  { eapply eval_place_resolved_write_target_matches_root; eassumption. }
  subst x_eval.
  unfold store_lookup_path in Hlookup_path.
  destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
  eapply value_lookup_path_roots_within.
  - eapply store_roots_within_lookup_value; eassumption.
  - exact Hlookup_path.
Qed.

Lemma eval_place_resolved_update_path_roots_within_union :
  forall R R1 s s1 s2 p x_eval path_eval x v_new roots_old roots_new,
    store_roots_within R s ->
    store_no_shadow s1 ->
    store_roots_within R1 s1 ->
    root_env_lookup x R1 = Some roots_old ->
    eval_place s p x_eval path_eval ->
    place_resolved_write_target R p = Some x ->
    value_roots_within roots_new v_new ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s2.
Proof.
  intros R R1 s s1 s2 p x_eval path_eval x v_new roots_old roots_new
    Hwithin Hnodup Hwithin1 Hlookup_old Heval Htarget Hvalue Hupdate.
  assert (Hx : x_eval = x).
  { eapply eval_place_resolved_write_target_matches_root.
    - exact Hwithin.
    - exact Heval.
    - exact Htarget. }
  subst x_eval.
  eapply store_update_path_roots_within_union; eassumption.
Qed.

Lemma lookup_alpha_rename_fn_def_typed_structural :
  forall env fname fdef fcall used used',
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    typed_fn_env_structural env fcall.
Proof.
  intros env fname fdef fcall used used' Hlookup Henv_checked Hrename.
  eapply alpha_rename_fn_def_typed_structural_forward.
  - exact Hrename.
  - eapply lookup_fn_checked_structural_params_nodup; eassumption.
  - eapply lookup_fn_checked_structural_typed; eassumption.
Qed.

Lemma typed_fn_env_structural_body :
  forall env f,
    typed_fn_env_structural env f ->
    exists T_body Γ_out,
      typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Γ_out = true.
Proof.
  intros env f Htyped.
  unfold typed_fn_env_structural in Htyped.
  exact Htyped.
Qed.

Lemma root_env_store_roots_named_to_ctx :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_store_roots_named R s ->
    root_env_ctx_roots_named R Σ.
Proof.
  unfold root_env_store_roots_named, root_env_ctx_roots_named.
  intros env s Σ R Hstore Hnamed x roots z Hlookup Hin.
  rewrite <- (store_typed_names env s Σ Hstore).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_to_ctx :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_store_keys_named R s ->
    root_env_ctx_keys_named R Σ.
Proof.
  unfold root_env_store_keys_named, root_env_ctx_keys_named.
  intros env s Σ R Hstore Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite <- (store_typed_names env s Σ Hstore).
    exact Hin.
Qed.

Lemma root_env_ctx_keys_named_store_typed :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_ctx_keys_named R Σ ->
    root_env_store_keys_named R s.
Proof.
  unfold root_env_store_keys_named, root_env_ctx_keys_named.
  intros env s Σ R Hstore Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite (store_typed_names env s Σ Hstore).
    exact Hin.
Qed.

Lemma root_env_ctx_keys_named_store_typed_prefix :
  forall env s Σ R,
    store_typed_prefix env s Σ ->
    root_env_ctx_keys_named R Σ ->
    root_env_store_keys_named R s.
Proof.
  unfold root_env_store_keys_named, root_env_ctx_keys_named.
  intros env s Σ R Hstore Hkeys.
  destruct Hstore as [entries [frame [Hs Hentries]]].
  subst s.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite store_names_app.
    apply in_or_app. left.
    rewrite (roots_ready_store_entries_typed_names env (entries ++ frame) entries Σ Hentries).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_to_ctx :
  forall env s Σ roots,
    store_typed env s Σ ->
    root_set_store_roots_named roots s ->
    root_set_ctx_roots_named roots Σ.
Proof.
  unfold root_set_store_roots_named, root_set_ctx_roots_named.
  intros env s Σ roots Hstore Hnamed z Hin.
  rewrite <- (store_typed_names env s Σ Hstore).
  apply Hnamed. exact Hin.
Qed.

Lemma ctx_names_remove_preserve_neq_root_names :
  forall x y Σ,
    x <> y ->
    In y (ctx_names Σ) ->
    In y (ctx_names (sctx_remove x Σ)).
Proof.
  unfold sctx_remove.
  intros x y Σ Hneq.
  induction Σ as [| [[[z T] st] m] rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y.
      destruct (ident_eqb x z) eqn:Hxz.
      * apply ident_eqb_eq in Hxz. exfalso. apply Hneq. exact Hxz.
      * simpl. left. reflexivity.
    + destruct (ident_eqb x z).
      * exact Hin.
      * simpl. right. apply IH. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_remove_ctx_excluding :
  forall roots Σ x,
    roots_exclude x roots ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots (sctx_remove x Σ).
Proof.
  unfold root_set_ctx_roots_named, roots_exclude.
  intros roots Σ x Hexclude Hnamed z Hin.
  apply ctx_names_remove_preserve_neq_root_names.
  - intros Heq. subst z. apply Hexclude. exact Hin.
  - apply Hnamed. exact Hin.
Qed.

Lemma root_env_ctx_roots_named_remove_ctx_excluding :
  forall R Σ x,
    (forall y roots,
      root_env_lookup y R = Some roots ->
      roots_exclude x roots) ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R (sctx_remove x Σ).
Proof.
  unfold root_env_ctx_roots_named, roots_exclude.
  intros R Σ x Hexclude Hnamed y roots z Hlookup Hin.
  apply ctx_names_remove_preserve_neq_root_names.
  - intros Heq. subst z. eapply Hexclude; eassumption.
  - eapply Hnamed; eassumption.
Qed.

Lemma sctx_lookup_in_ctx_names_root_names :
  forall x Σ T st,
    sctx_lookup x Σ = Some (T, st) ->
    In x (ctx_names Σ).
Proof.
  unfold sctx_lookup.
  intros x Σ.
  induction Σ as [| [[[y Ty] sty] my] rest IH]; intros T st Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    left. reflexivity.
  - right. eapply IH. exact Hlookup.
Qed.

Lemma typed_place_type_root_name_in_ctx_names :
  forall env Σ p T,
    typed_place_type_env_structural env Σ p T ->
    In (root_provenance_place_name p) (ctx_names Σ).
Proof.
  intros env Σ p T Htyped.
  induction Htyped; simpl.
  - eapply sctx_lookup_in_ctx_names_root_names. exact H.
  - exact IHHtyped.
  - exact IHHtyped.
Qed.

Lemma typed_place_root_name_in_ctx_names :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    In (root_provenance_place_name p) (ctx_names Σ).
Proof.
  intros env Σ p T Htyped.
  induction Htyped; simpl.
  - eapply sctx_lookup_in_ctx_names_root_names. exact H.
  - exact IHHtyped.
  - eapply typed_place_type_root_name_in_ctx_names. exact H.
  - eapply typed_place_type_root_name_in_ctx_names. exact H.
Qed.

Lemma root_of_place_ctx_roots_named :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    root_set_ctx_roots_named (root_of_place p) Σ.
Proof.
  intros env Σ p T Htyped.
  unfold root_of_place.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - apply root_set_ctx_roots_named_single.
    destruct (typed_place_direct_lookup env Σ p T x path Htyped Hpath)
      as [T_root [st [Hlookup _]]].
    eapply sctx_lookup_in_ctx_names_root_names. exact Hlookup.
  - apply root_set_ctx_roots_named_single.
    eapply typed_place_root_name_in_ctx_names. exact Htyped.
Qed.

Lemma root_env_lookup_ctx_roots_named :
  forall R Σ x roots,
    root_env_lookup x R = Some roots ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ.
Proof.
  unfold root_env_ctx_roots_named, root_set_ctx_roots_named.
  intros R Σ x roots Hlookup Hnamed z Hin.
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_ctx_roots_named_same_bindings :
  forall roots Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots Σ Σ' Hsame Hnamed z Hin.
  rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
  apply Hnamed. exact Hin.
Qed.

Lemma root_env_ctx_roots_named_same_bindings :
  forall R Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R Σ'.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ Σ' Hsame Hnamed x roots z Hlookup Hin.
  rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_ctx_keys_named_same_bindings :
  forall R Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R Σ'.
Proof.
  unfold root_env_ctx_keys_named.
  intros R Σ Σ' Hsame Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
    exact Hin.
Qed.

Lemma root_set_ctx_roots_named_consume_path :
  forall roots Σ x path Σ',
    sctx_consume_path Σ x path = infer_ok Σ' ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  intros roots Σ x path Σ' Hconsume Hnamed.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply sctx_consume_path_same_bindings. exact Hconsume.
  - exact Hnamed.
Qed.

Lemma root_env_lookup_ctx_roots_named_consume_path :
  forall R Σ y roots x path Σ',
    root_env_lookup y R = Some roots ->
    root_env_ctx_roots_named R Σ ->
    sctx_consume_path Σ x path = infer_ok Σ' ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  intros R Σ y roots x path Σ' Hlookup Henv_named Hconsume.
  eapply root_set_ctx_roots_named_consume_path.
  - exact Hconsume.
  - eapply root_env_lookup_ctx_roots_named; eassumption.
Qed.

Lemma root_env_ctx_roots_named_add_binding :
  forall R Σ x T m roots,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named (root_env_add x roots R)
      (sctx_add x T m Σ).
Proof.
  intros R Σ x T m roots Henv Hroots.
  apply root_env_ctx_roots_named_add_env_named.
  - eapply root_env_ctx_roots_named_weaken_ctx.
    + exact Henv.
    + intros z Hin. simpl. right. exact Hin.
  - eapply root_set_ctx_roots_named_weaken_ctx.
    + exact Hroots.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_ctx_keys_named_add_binding :
  forall R Σ x T m roots,
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named (root_env_add x roots R)
      (sctx_add x T m Σ).
Proof.
  intros R Σ x T m roots Hkeys.
  unfold root_env_ctx_keys_named.
  apply root_env_keys_named_add.
  - simpl. left. reflexivity.
  - eapply root_env_keys_named_weaken.
    + exact Hkeys.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_remove_excludes_roots_exclude :
  forall R x y roots,
    root_env_no_shadow R ->
    root_env_excludes x (root_env_remove x R) ->
    root_env_lookup y (root_env_remove x R) = Some roots ->
    roots_exclude x roots.
Proof.
  intros R x y roots Hrn Hexcl Hlookup.
  apply Hexcl with (y := y).
  - exact Hlookup.
  - intros Heq. subst y.
    rewrite root_env_lookup_remove_eq_no_shadow in Hlookup by exact Hrn.
    discriminate.
Qed.

Lemma root_env_ctx_roots_named_remove_binding :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_excludes x (root_env_remove x R) ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named (root_env_remove x R) (sctx_remove x Σ).
Proof.
  intros R Σ x Hrn Hexcl Henv.
  apply root_env_ctx_roots_named_remove_ctx_excluding.
  - intros y roots Hlookup.
    eapply root_env_remove_excludes_roots_exclude; eassumption.
  - apply root_env_ctx_roots_named_remove_env; assumption.
Qed.

Lemma root_env_ctx_keys_named_remove_binding :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named (root_env_remove x R) (sctx_remove x Σ).
Proof.
  unfold root_env_ctx_keys_named.
  intros R Σ x Hrn Hkeys.
  induction R as [| [z roots] rest IH]; intros y Hin; simpl in *;
    try contradiction.
  unfold root_env_no_shadow in Hrn. simpl in Hrn.
  inversion Hrn as [| ? ? Hz_notin Hrn_tail]; subst.
  destruct (ident_eqb x z) eqn:Hxz.
  - apply ident_eqb_eq in Hxz. subst z.
    apply ctx_names_remove_preserve_neq_root_names.
    + intros Heq. subst y. contradiction.
    + apply Hkeys. right. exact Hin.
  - simpl in Hin.
    destruct Hin as [Hy | Hin].
    + subst y.
      apply ctx_names_remove_preserve_neq_root_names.
      * intros Heq. subst z. rewrite ident_eqb_refl in Hxz. discriminate.
      * apply Hkeys. left. reflexivity.
    + apply IH.
      * exact Hrn_tail.
      * intros w Hw. apply Hkeys. right. exact Hw.
      * exact Hin.
Qed.

Lemma root_set_ctx_roots_named_remove_binding :
  forall roots Σ x,
    roots_exclude x roots ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots (sctx_remove x Σ).
Proof.
  intros roots Σ x Hexcl Hroots.
  apply root_set_ctx_roots_named_remove_ctx_excluding; assumption.
Qed.

Lemma root_env_ctx_roots_named_update_union :
  forall R Σ x roots_old roots_new,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots_old Σ ->
    root_set_ctx_roots_named roots_new Σ ->
    root_env_ctx_roots_named
      (root_env_update x (root_set_union roots_old roots_new) R) Σ.
Proof.
  intros R Σ x roots_old roots_new Hrn Henv Hold Hnew.
  apply root_env_ctx_roots_named_update_env_named.
  - exact Hrn.
  - exact Henv.
  - apply root_set_ctx_roots_named_union; assumption.
Qed.

Lemma root_env_ctx_keys_named_update :
  forall R Σ x roots,
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named (root_env_update x roots R) Σ.
Proof.
  intros R Σ x roots Hkeys.
  unfold root_env_ctx_keys_named.
  apply root_env_keys_named_update.
  exact Hkeys.
Qed.

Lemma root_env_ctx_roots_named_update_union_restore_path :
  forall R Σ1 Σ2 x path roots_old roots_new,
    sctx_restore_path Σ1 x path = infer_ok Σ2 ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ1 ->
    root_set_ctx_roots_named roots_old Σ1 ->
    root_set_ctx_roots_named roots_new Σ1 ->
    root_env_ctx_roots_named
      (root_env_update x (root_set_union roots_old roots_new) R) Σ2.
Proof.
  intros R Σ1 Σ2 x path roots_old roots_new Hrestore Hrn Henv Hold Hnew.
  eapply root_env_ctx_roots_named_same_bindings.
  - eapply sctx_restore_path_same_bindings. exact Hrestore.
  - apply root_env_ctx_roots_named_update_union; assumption.
Qed.

Lemma root_env_lookup_result_ctx_roots_named_after_typed :
  forall env Ω n R Σ e_new T_new Σ1 R1 roots_new x roots_result,
    root_env_lookup x R = Some roots_result ->
    root_env_ctx_roots_named R Σ ->
    typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
    root_set_ctx_roots_named roots_result Σ1.
Proof.
  intros env Ω n R Σ e_new T_new Σ1 R1 roots_new x roots_result
    Hlookup Henv Htyped.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped.
  - eapply root_env_lookup_ctx_roots_named; eassumption.
Qed.

Lemma root_env_lookup_result_ctx_roots_named_after_typed_restore_path :
  forall env Ω n R Σ e_new T_new Σ1 Σ2 R1 roots_new x path
      roots_result,
    root_env_lookup x R = Some roots_result ->
    root_env_ctx_roots_named R Σ ->
    typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
    sctx_restore_path Σ1 x path = infer_ok Σ2 ->
    root_set_ctx_roots_named roots_result Σ2.
Proof.
  intros env Ω n R Σ e_new T_new Σ1 Σ2 R1 roots_new x path
    roots_result Hlookup Henv Htyped Hrestore.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply sctx_restore_path_same_bindings. exact Hrestore.
  - eapply root_env_lookup_result_ctx_roots_named_after_typed;
      eassumption.
Qed.

Lemma root_store_single_ctx_roots_named_of_place_path :
  forall env Σ p T x path,
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x, path) ->
    root_set_ctx_roots_named [RStore x] Σ.
Proof.
  intros env Σ p T x path Htyped Hpath.
  apply root_set_ctx_roots_named_single.
  destruct (typed_place_direct_lookup env Σ p T x path Htyped Hpath)
    as [T_root [st [Hlookup _]]].
  eapply sctx_lookup_in_ctx_names_root_names. exact Hlookup.
Qed.

Lemma root_set_ctx_roots_named_ctx_merge_left :
  forall roots Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_ctx_roots_named roots Σ2 ->
    root_set_ctx_roots_named roots Σ4.
Proof.
  intros roots Σ2 Σ3 Σ4 Hmerge Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
  - exact Hroots.
Qed.

Lemma root_env_ctx_roots_named_ctx_merge_left :
  forall R Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_env_ctx_roots_named R Σ2 ->
    root_env_ctx_roots_named R Σ4.
Proof.
  intros R Σ2 Σ3 Σ4 Hmerge Henv.
  eapply root_env_ctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
  - exact Henv.
Qed.

Lemma root_set_ctx_roots_named_ctx_merge_right :
  forall env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2
      e3 T3 Σ3 R3 roots3 Σ4,
    typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
    typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_ctx_roots_named roots3 Σ3 ->
    root_set_ctx_roots_named roots3 Σ4.
Proof.
  intros env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 e3 T3 Σ3 R3
    roots3 Σ4 Htyped2 Htyped3 Hmerge Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_right.
    + eapply sctx_same_bindings_trans.
      * apply sctx_same_bindings_sym.
        eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact Htyped2.
      * eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact Htyped3.
    + exact Hmerge.
  - exact Hroots.
Qed.

Lemma root_set_ctx_roots_named_if_merge :
  forall env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2
      e3 T3 Σ3 R3 roots3 Σ4,
    typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
    typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_ctx_roots_named roots2 Σ2 ->
    root_set_ctx_roots_named roots3 Σ3 ->
    root_set_ctx_roots_named (root_set_union roots2 roots3) Σ4.
Proof.
  intros env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 e3 T3 Σ3 R3
    roots3 Σ4 Htyped2 Htyped3 Hmerge Hroots2 Hroots3.
  apply root_set_ctx_roots_named_union.
  - eapply root_set_ctx_roots_named_ctx_merge_left; eassumption.
  - eapply root_set_ctx_roots_named_ctx_merge_right.
    + exact Htyped2.
    + exact Htyped3.
    + exact Hmerge.
    + exact Hroots3.
Qed.

Lemma root_set_ctx_roots_named_typed_args_tail :
  forall env Ω n Σ1 R1 roots args ps Σ2 R2 roots_rest,
    typed_args_roots env Ω n R1 Σ1 args ps Σ2 R2 roots_rest ->
    root_set_ctx_roots_named roots Σ1 ->
    root_set_ctx_roots_named roots Σ2.
Proof.
  intros env Ω n Σ1 R1 roots args ps Σ2 R2 roots_rest Htyped_args Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply typed_args_env_structural_same_bindings.
    eapply typed_args_roots_structural. exact Htyped_args.
  - exact Hroots.
Qed.

Lemma root_set_ctx_roots_named_typed_fields_tail :
  forall env Ω n lts ty_args Σ1 R1 roots fields defs Σ2 R2 roots_rest,
    typed_fields_roots env Ω n lts ty_args R1 Σ1 fields defs Σ2 R2
      roots_rest ->
    root_set_ctx_roots_named roots Σ1 ->
    root_set_ctx_roots_named roots Σ2.
Proof.
  intros env Ω n lts ty_args Σ1 R1 roots fields defs Σ2 R2 roots_rest
    Htyped_fields Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply typed_fields_env_structural_same_bindings.
    eapply typed_fields_roots_structural. exact Htyped_fields.
  - exact Hroots.
Qed.

Lemma typed_args_roots_arg_roots_length :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' arg_roots ->
    List.length arg_roots = List.length ps.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Htyped_args.
  induction Htyped_args; simpl; auto.
Qed.

Lemma typed_fields_roots_cons_inv_ts :
  forall env Ω n lts args R Σ fields f rest Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields (f :: rest) Σ' R' roots ->
    exists e_field T_field Σ1 R1 roots_field roots_rest,
      lookup_field_b (field_name f) fields = Some e_field /\
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field /\
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) =
        true /\
      typed_fields_roots env Ω n lts args R1 Σ1 fields rest
        Σ' R' roots_rest /\
      roots = root_set_union roots_field roots_rest.
Proof.
  intros env Ω n lts args R Σ fields f rest Σ' R' roots Htyped.
  inversion Htyped; subst.
  exists e_field, T_field, Σ1, R1, roots_field, roots_rest.
  repeat split; assumption.
Qed.
