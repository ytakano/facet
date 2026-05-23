From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCallFrameRootEnv.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition root_env_tail_fresh_names (R_tail : root_env)
    (names : list ident) : Prop :=
  forall x,
    In x names ->
    root_env_lookup x R_tail = None /\ root_env_excludes x R_tail.

Lemma root_env_tail_fresh_names_app_l :
  forall R_tail names1 names2,
    root_env_tail_fresh_names R_tail (names1 ++ names2) ->
    root_env_tail_fresh_names R_tail names1.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail names1 names2 Hfresh x Hin.
  apply Hfresh. apply in_or_app. left. exact Hin.
Qed.

Lemma root_env_tail_fresh_names_app_r :
  forall R_tail names1 names2,
    root_env_tail_fresh_names R_tail (names1 ++ names2) ->
    root_env_tail_fresh_names R_tail names2.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail names1 names2 Hfresh x Hin.
  apply Hfresh. apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_tail_fresh_names_cons_head :
  forall R_tail x names,
    root_env_tail_fresh_names R_tail (x :: names) ->
    root_env_lookup x R_tail = None /\ root_env_excludes x R_tail.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail x names Hfresh.
  apply Hfresh. left. reflexivity.
Qed.

Lemma root_env_tail_fresh_names_cons_tail :
  forall R_tail x names,
    root_env_tail_fresh_names R_tail (x :: names) ->
    root_env_tail_fresh_names R_tail names.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail x names Hfresh y Hin.
  apply Hfresh. right. exact Hin.
Qed.

Lemma root_env_tail_fresh_names_lookup_field :
  forall R_tail fname fields e,
    lookup_field_b fname fields = Some e ->
    root_env_tail_fresh_names R_tail (fields_local_store_names fields) ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e).
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail fname fields e Hlookup Hfresh x Hin.
  apply Hfresh.
  eapply fields_local_store_names_in_expr.
  - eapply lookup_field_b_success. exact Hlookup.
  - exact Hin.
Qed.

Theorem typed_roots_shadow_safe_tail_frame_mutual :
  forall env Ω n R_tail,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
    typed_env_roots_shadow_safe env Ω n (R ++ R_tail) Σ e T Σ'
      (R' ++ R_tail) roots) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_env_tail_fresh_names R_tail (args_local_store_names args) ->
    typed_args_roots_shadow_safe env Ω n (R ++ R_tail) Σ args ps Σ'
      (R' ++ R_tail) roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_env_tail_fresh_names R_tail (fields_local_store_names fields) ->
    typed_fields_roots_shadow_safe env Ω n lts args (R ++ R_tail) Σ
      fields defs Σ' (R' ++ R_tail) roots).
Proof.
  intros env Ω n R_tail.
  apply typed_roots_shadow_safe_ind; intros; simpl in *.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - eapply TERS_Var_Copy; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Var_Move; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Place_Copy; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Place_Move; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Call; eauto.
  - eapply TERS_Fn; eauto.
  - eapply TERS_MakeClosure; eauto.
  - eapply TERS_MakeClosure_Static; eauto.
  - eapply TERS_CallExpr_MakeClosure; eauto.
  - eapply TERS_Struct; eauto.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H1) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H1) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply TERS_Let.
    + apply H. exact Hfresh1.
    + exact e.
    + rewrite root_env_lookup_app_right by exact e0.
      exact Htail_lookup.
    + exact r.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply H0. exact Hfresh2.
    + exact e3.
    + exact r1.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H1) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H1) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply TERS_LetInfer.
    + apply H. exact Hfresh1.
    + rewrite root_env_lookup_app_right by exact e.
      exact Htail_lookup.
    + exact r.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply H0. exact Hfresh2.
    + exact e0.
    + exact r1.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - eapply TERS_Drop. eauto.
  - replace (root_env_update x (root_set_union roots_old roots_new) R1 ++
        R_tail)
      with (root_env_update x (root_set_union roots_old roots_new)
        (R1 ++ R_tail)).
    eapply TERS_Replace_Path; eauto.
    + eapply root_env_lookup_app_left; eassumption.
    + eapply root_env_lookup_app_left; eassumption.
    + rewrite root_env_update_app_left with (roots_old := roots_old)
        by eassumption.
      reflexivity.
  - replace (root_env_update x (root_set_union roots_old roots_new) R1 ++
        R_tail)
      with (root_env_update x (root_set_union roots_old roots_new)
        (R1 ++ R_tail)).
    eapply TERS_Assign_Path; eauto.
    + eapply root_env_lookup_app_left; eassumption.
    + rewrite root_env_update_app_left with (roots_old := roots_old)
        by eassumption.
      reflexivity.
  - eapply TERS_BorrowShared; eauto.
  - eapply TERS_BorrowUnique; eauto.
  - eapply TERS_DerefBorrowShared; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_DerefBorrowUnique; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H2) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H2) as Hfresh_tail.
    pose proof (root_env_tail_fresh_names_app_l _ _ _ Hfresh_tail) as Hfresh2.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ Hfresh_tail) as Hfresh3.
    eapply TERS_If.
    + apply H. exact Hfresh1.
    + exact e.
    + apply H0. exact Hfresh2.
    + apply H1. exact Hfresh3.
    + exact e0.
    + exact e4.
    + apply root_env_equiv_app.
      * exact r.
      * apply root_env_equiv_refl.
  - constructor.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H1) as Hfresh_e.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H1) as Hfresh_es.
    eapply TERSArgs_Cons.
    + apply H. exact Hfresh_e.
    + exact e0.
    + apply H0. exact Hfresh_es.
  - constructor.
  - eapply TERSFields_Cons.
    + exact e.
    + apply H. eapply root_env_tail_fresh_names_lookup_field; eassumption.
    + exact e0.
    + apply H0. exact H1.
Qed.

Lemma typed_env_roots_shadow_safe_tail_frame :
  forall env Ω n R_tail R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
    typed_env_roots_shadow_safe env Ω n (R ++ R_tail) Σ e T Σ'
      (R' ++ R_tail) roots.
Proof.
  intros env Ω n R_tail.
  exact (proj1 (typed_roots_shadow_safe_tail_frame_mutual env Ω n R_tail)).
Qed.

Lemma root_env_remove_params_no_shadow :
  forall ps R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_remove_params ps R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R Hnodup; simpl.
  - exact Hnodup.
  - apply IH. apply root_env_no_shadow_remove. exact Hnodup.
Qed.

Lemma root_env_lookup_remove_params_not_in :
  forall ps R x,
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_remove_params ps R) =
      root_env_lookup x R.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R x Hnotin; simpl in *.
  - reflexivity.
  - rewrite IH.
    + rewrite root_env_lookup_remove_neq.
      * reflexivity.
      * intros Heq. subst x. apply Hnotin. left. reflexivity.
    + intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma root_env_lookup_remove_params_none_preserved :
  forall ps R x,
    root_env_lookup x R = None ->
    root_env_lookup x (root_env_remove_params ps R) = None.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R x Hlookup; simpl.
  - exact Hlookup.
  - apply IH.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      rewrite root_env_remove_lookup_none by exact Hlookup.
      exact Hlookup.
    + rewrite root_env_lookup_remove_neq.
      * exact Hlookup.
      * intros Hcontra. subst x.
        rewrite ident_eqb_refl in Heq. discriminate.
Qed.

Lemma root_env_remove_params_lookup_none :
  forall ps R x,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_remove_params ps R) = None.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R x Hnodup Hrn Hin; simpl in *.
  - contradiction.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct Hin as [Hin | Hin].
    + subst x.
      rewrite root_env_lookup_remove_params_not_in.
      * apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
      * exact Hnotin.
    + eapply IH.
      * exact Hnodup_tail.
      * apply root_env_no_shadow_remove. exact Hrn.
      * exact Hin.
Qed.

Lemma root_env_add_params_roots_lookup_not_in :
  forall ps roots_list R x,
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_add_params_roots ps roots_list R) =
      root_env_lookup x R.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R x Hnotin;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      contradiction Hnotin. left. reflexivity.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma root_env_add_params_roots_covers_lookup :
  forall ps roots_list R x,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length roots_list = List.length ps ->
    In x (ctx_names (params_ctx ps)) ->
    exists roots,
      root_env_lookup x (root_env_add_params_roots ps roots_list R) =
        Some roots.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R x Hnodup Hlen Hin;
    destruct roots_list as [| roots roots_list]; simpl in *; try discriminate.
  - contradiction.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    inversion Hlen as [Hlen_tail].
    destruct Hin as [Hin | Hin].
    + subst x. exists roots. simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl.
      destruct (ident_eqb x (param_name p)) eqn:Heq.
      * apply ident_eqb_eq in Heq. subst x. contradiction.
      * eapply IH; eassumption.
Qed.

Lemma root_env_add_params_roots_lookup_remove_neq :
  forall ps roots_list R x y,
    x <> y ->
    root_env_lookup x (root_env_add_params_roots ps roots_list
      (root_env_remove y R)) =
    root_env_lookup x (root_env_add_params_roots ps roots_list R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R x y Hneq;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - apply root_env_lookup_remove_neq. intros Heq. apply Hneq. symmetry. exact Heq.
  - apply root_env_lookup_remove_neq. intros Heq. apply Hneq. symmetry. exact Heq.
  - apply root_env_lookup_remove_neq. intros Heq. apply Hneq. symmetry. exact Heq.
  - destruct (ident_eqb x (param_name p)) eqn:Heq; try reflexivity.
    apply IH. exact Hneq.
Qed.

Lemma root_set_instantiate_single_param_equiv :
  forall rho x roots,
    root_subst_lookup x rho = roots ->
    root_set_equiv (root_set_instantiate rho [RParam x]) roots.
Proof.
  intros rho x roots Hlookup.
  simpl. rewrite Hlookup.
  eapply root_set_equiv_trans.
  - apply root_set_union_equiv_app.
  - simpl. rewrite app_nil_r. apply root_set_equiv_refl.
Qed.

Lemma root_env_instantiate_cons_initial_origin_notin :
  forall x roots rho ps_orig ps_current,
    ~ In x (ctx_names (params_ctx ps_orig)) ->
    root_env_instantiate ((x, roots) :: rho)
      (initial_root_env_for_params_origin ps_orig ps_current) =
    root_env_instantiate rho
      (initial_root_env_for_params_origin ps_orig ps_current).
Proof.
  intros x roots rho ps_orig.
  induction ps_orig as [| p ps_orig IH]; intros ps_current Hnotin;
    destruct ps_current as [| pc ps_current]; simpl in *; try reflexivity.
  assert (Hneq : param_name p <> x).
  { intros Heq. apply Hnotin. left. exact Heq. }
  assert (Htail : ~ In x (ctx_names (params_ctx ps_orig))).
  { intros Hin. apply Hnotin. right. exact Hin. }
  destruct (ident_eqb (param_name p) x) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite IH; [reflexivity | exact Htail].
Qed.

Lemma root_env_instantiate_initial_origin_equiv_add_params_roots :
  forall ps_orig ps_current arg_roots,
    params_alpha ps_orig ps_current ->
    NoDup (ctx_names (params_ctx ps_orig)) ->
    List.length arg_roots = List.length ps_orig ->
    root_env_equiv
      (root_env_instantiate (root_subst_of_params ps_orig arg_roots)
        (initial_root_env_for_params_origin ps_orig ps_current))
      (root_env_add_params_roots ps_current arg_roots []).
Proof.
  intros ps_orig ps_current arg_roots Halpha Hnodup.
  revert arg_roots.
  induction Halpha as [| p pr ps psr Hshape Halpha_tail IH];
    intros arg_roots Hlen.
  - destruct arg_roots as [| roots arg_roots]; simpl in Hlen; try discriminate.
    simpl. apply root_env_equiv_refl.
  - destruct arg_roots as [| roots arg_roots]; simpl in Hlen; try discriminate.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    inversion Hlen as [Hlen_tail].
    unfold root_env_equiv. intros x. simpl.
    destruct (ident_eqb x (param_name pr)) eqn:Heq.
    + rewrite ident_eqb_refl.
      eapply root_set_equiv_trans.
      * apply root_set_union_equiv_app.
      * simpl. rewrite app_nil_r. apply root_set_equiv_refl.
    + rewrite root_env_instantiate_cons_initial_origin_notin.
      * specialize (IH Hnodup_tail arg_roots Hlen_tail).
        unfold root_env_equiv in IH.
        apply IH.
      * exact Hnotin.
Qed.

Lemma root_env_add_params_roots_equiv_call_param_root_env :
  forall ps roots_list R_tail,
    List.length roots_list = List.length ps ->
    root_env_equiv
      (root_env_add_params_roots ps roots_list R_tail)
      (call_param_root_env ps roots_list R_tail).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R_tail Hlen;
    destruct roots_list as [| roots roots_list]; simpl in *; try discriminate.
  - apply root_env_equiv_refl.
  - inversion Hlen as [Hlen_tail].
    unfold root_env_equiv. intros x. simpl.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply root_set_equiv_refl.
    + apply ident_eqb_neq in Heq.
      specialize (IH roots_list (root_env_remove (param_name p) R_tail)
        Hlen_tail).
      unfold root_env_equiv in IH.
      specialize (IH x).
      rewrite root_env_add_params_roots_lookup_remove_neq in IH by exact Heq.
      exact IH.
Qed.

Lemma root_env_instantiate_initial_origin_equiv_call_param_root_env_empty :
  forall ps_orig ps_current arg_roots,
    params_alpha ps_orig ps_current ->
    NoDup (ctx_names (params_ctx ps_orig)) ->
    List.length arg_roots = List.length ps_orig ->
    root_env_equiv
      (root_env_instantiate (root_subst_of_params ps_orig arg_roots)
        (initial_root_env_for_params_origin ps_orig ps_current))
      (call_param_root_env ps_current arg_roots []).
Proof.
  intros ps_orig ps_current arg_roots Halpha Hnodup Hlen.
  pose proof Halpha as Halpha_len.
  assert (Hlen_current : List.length arg_roots = List.length ps_current).
  { assert (Hparams_len : List.length ps_orig = List.length ps_current).
    { clear Halpha Hnodup Hlen arg_roots.
      induction Halpha_len; simpl; try reflexivity.
      f_equal. exact IHHalpha_len. }
    rewrite <- Hparams_len. exact Hlen. }
  eapply root_env_equiv_trans.
  - eapply root_env_instantiate_initial_origin_equiv_add_params_roots;
      eassumption.
  - apply root_env_add_params_roots_equiv_call_param_root_env.
    exact Hlen_current.
Qed.

Lemma root_env_add_params_roots_no_shadow :
  forall ps roots_list R,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R = None) ->
    root_env_no_shadow (root_env_add_params_roots ps roots_list R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R Hnodup Hrn Hfresh;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - exact Hrn.
  - exact Hrn.
  - exact Hrn.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    apply root_env_no_shadow_add.
    + apply IH.
      * exact Hnodup_tail.
      * exact Hrn.
      * intros x Hin. apply Hfresh. right. exact Hin.
    + rewrite root_env_add_params_roots_lookup_not_in.
      * apply Hfresh. left. reflexivity.
      * exact Hnotin.
Qed.

Lemma call_param_root_env_no_shadow :
  forall ps roots R_tail,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R_tail ->
    root_env_no_shadow (call_param_root_env ps roots R_tail).
Proof.
  intros ps roots R_tail Hnodup Hrn.
  unfold call_param_root_env.
  apply root_env_add_params_roots_no_shadow.
  - exact Hnodup.
  - apply root_env_remove_params_no_shadow. exact Hrn.
  - intros x Hin.
    eapply root_env_remove_params_lookup_none; eassumption.
Qed.
