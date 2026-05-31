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

Lemma root_env_tail_fresh_names_lookup_expr_branch :
  forall R_tail name branches e,
    lookup_expr_branch name branches = Some e ->
    root_env_tail_fresh_names R_tail (match_branches_local_store_names branches) ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e).
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail name branches e Hlookup Hfresh x Hin.
  apply Hfresh.
  eapply lookup_expr_branch_local_store_names_in; eassumption.
Qed.

Lemma root_env_tail_fresh_names_lookup_expr_branch_binders :
  forall R_tail name branches binders,
    lookup_expr_branch_binders name branches = Some binders ->
    root_env_tail_fresh_names R_tail (match_branches_local_store_names branches) ->
    root_env_tail_fresh_names R_tail binders.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail name branches binders Hlookup Hfresh x Hin.
  apply Hfresh.
  eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
Qed.

Lemma root_env_tail_fresh_names_params_lookup_none :
  forall R_tail ps names,
    root_env_tail_fresh_names R_tail names ->
    (forall x, In x (ctx_names (params_ctx ps)) -> In x names) ->
    root_env_lookup_params_none_b ps R_tail = true.
Proof.
  induction ps as [| [m x T] ps IH]; intros names Hfresh Hnames.
  - reflexivity.
  - simpl.
    destruct (Hfresh x) as [Hlookup _].
    { apply Hnames. simpl. left. reflexivity. }
    rewrite Hlookup.
    apply IH with (names := names).
    + exact Hfresh.
    + intros y Hy. apply Hnames. simpl. right. exact Hy.
Qed.

Lemma root_env_tail_fresh_names_params_excludes :
  forall R_tail ps names,
    root_env_tail_fresh_names R_tail names ->
    (forall x, In x (ctx_names (params_ctx ps)) -> In x names) ->
    root_env_excludes_params ps R_tail.
Proof.
  unfold root_env_excludes_params.
  intros R_tail ps names Hfresh Hnames.
  apply Forall_forall. intros x Hin.
  destruct (Hfresh x) as [_ Hexcl].
  - apply Hnames. exact Hin.
  - exact Hexcl.
Qed.

Lemma place_resolved_write_target_app_left :
  forall R R_tail p x,
    place_resolved_write_target R p = Some x ->
    place_resolved_write_target (R ++ R_tail) p = Some x.
Proof.
  induction p; intros x Htarget; simpl in Htarget |- *.
  - exact Htarget.
  - case_eq (place_resolved_write_target R p).
    + intros target Hq.
      rewrite (IHp target Hq).
      destruct (root_env_lookup target R) as [roots |] eqn:Hlookup.
      * rewrite (root_env_lookup_app_left target R R_tail roots Hlookup).
        rewrite Hq in Htarget. rewrite Hlookup in Htarget.
        exact Htarget.
      * rewrite Hq in Htarget. rewrite Hlookup in Htarget. discriminate.
    + intros Hq. rewrite Hq in Htarget. discriminate.
  - apply IHp. exact Htarget.
Qed.


Lemma root_env_excludes_params_app_local :
  forall ps R1 R2,
    root_env_excludes_params ps R1 ->
    root_env_excludes_params ps R2 ->
    root_env_excludes_params ps (R1 ++ R2).
Proof.
  unfold root_env_excludes_params.
  intros ps R1 R2 Hexcl1 Hexcl2.
  apply Forall_forall. intros x Hin.
  eapply root_env_excludes_app.
  - eapply Forall_forall in Hexcl1; eauto.
  - eapply Forall_forall in Hexcl2; eauto.
Qed.

Lemma root_env_add_params_roots_same_app_left :
  forall ps roots R R_tail,
    root_env_add_params_roots_same ps roots (R ++ R_tail) =
    root_env_add_params_roots_same ps roots R ++ R_tail.
Proof.
  induction ps as [| p ps IH]; intros roots R R_tail.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma root_env_remove_match_params_app_left :
  forall ps R R_tail,
    root_env_lookup_params_none_b ps R_tail = true ->
    root_env_remove_match_params ps (R ++ R_tail) =
    root_env_remove_match_params ps R ++ R_tail.
Proof.
  induction ps as [| p ps IH]; intros R R_tail Hnone.
  - reflexivity.
  - simpl in Hnone |- *.
    destruct (root_env_lookup (param_name p) R_tail) eqn:Hlookup_tail;
      try discriminate.
    rewrite root_env_remove_app_left by exact Hlookup_tail.
    apply IH. exact Hnone.
Qed.

Lemma root_env_lookup_params_none_b_app :
  forall ps R1 R2,
    root_env_lookup_params_none_b ps R1 = true ->
    root_env_lookup_params_none_b ps R2 = true ->
    root_env_lookup_params_none_b ps (R1 ++ R2) = true.
Proof.
  induction ps as [| p ps IH]; intros R1 R2 Hnone1 Hnone2.
  - reflexivity.
  - simpl in *.
    destruct (root_env_lookup (param_name p) R1) eqn:Hlookup1;
      try discriminate.
    destruct (root_env_lookup (param_name p) R2) eqn:Hlookup2;
      try discriminate.
    rewrite root_env_lookup_app_right by exact Hlookup1.
    rewrite Hlookup2.
    apply IH; assumption.
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
      fields defs Σ' (R' ++ R_tail) roots) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_env_tail_fresh_names R_tail (match_branches_local_store_names branches) ->
    typed_match_tail_roots_shadow_safe env Ω n lts args (R ++ R_tail) roots_scrut Σ branches
      variants expected_core (R_out ++ R_tail) Σs Ts rootss).
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
	  - eapply TERS_CallGeneric; eauto.
	  - eapply TERS_Fn; eauto.
  - eapply TERS_MakeClosure; eauto.
  - eapply TERS_MakeClosure_Static; eauto.
  - eapply TERS_CallExpr_MakeClosure; eauto.
  - eapply TERS_CallExpr_Fn.
    + exact n0.
    + apply H. eapply root_env_tail_fresh_names_app_l. exact H1.
    + apply H0. eapply root_env_tail_fresh_names_app_r. exact H1.
  - eapply TERS_CallExpr_Closure.
    + exact n0.
    + apply H. eapply root_env_tail_fresh_names_app_l. exact H1.
    + apply H0. eapply root_env_tail_fresh_names_app_r. exact H1.
  - eapply TERS_CallExpr_TypeForall.
    + exact n0.
    + apply H. eapply root_env_tail_fresh_names_app_l. exact H1.
    + exact e.
    + exact e0.
    + apply H0. eapply root_env_tail_fresh_names_app_r. exact H1.
  - eapply TERS_CallExpr_MixedForall.
    + exact n0.
    + apply H. eapply root_env_tail_fresh_names_app_l. exact H1.
    + exact e.
    + exact e0.
    + exact e1.
    + exact e2.
    + eauto.
    + apply H0. eapply root_env_tail_fresh_names_app_r. exact H1.
  - eapply TERS_CallExpr_Forall_Fn.
    + exact n0.
    + apply H. eapply root_env_tail_fresh_names_app_l. exact H1.
    + exact e.
    + exact e0.
    + exact e1.
    + eauto.
    + apply H0. eapply root_env_tail_fresh_names_app_r. exact H1.
  - eapply TERS_CallExpr_Forall_Closure.
    + exact n0.
    + apply H. eapply root_env_tail_fresh_names_app_l. exact H1.
    + exact e.
    + exact e0.
    + exact e1.
    + exact e2.
    + eauto.
    + apply H0. eapply root_env_tail_fresh_names_app_r. exact H1.
  - eapply TERS_Struct; eauto.
  - eapply TERS_Enum; eauto.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H2) as Hfresh_scrut.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H2) as Hfresh_branches.
    assert (Hfresh_binders :
      root_env_tail_fresh_names R_tail binders_head).
    { eapply root_env_tail_fresh_names_lookup_expr_branch_binders;
      eassumption. }
    assert (Htail_params_none :
      root_env_lookup_params_none_b ps_head R_tail = true).
    { eapply root_env_tail_fresh_names_params_lookup_none.
      - exact Hfresh_binders.
      - intros x Hin.
	        rewrite (match_payload_params_names _ _ _ _ _ e7) in Hin.
        exact Hin. }
    assert (Htail_params_excl :
      root_env_excludes_params ps_head R_tail).
    { eapply root_env_tail_fresh_names_params_excludes.
      - exact Hfresh_binders.
      - intros x Hin.
	        rewrite (match_payload_params_names _ _ _ _ _ e7) in Hin.
        exact Hin. }
    eapply TERS_Match
      with (R_payload := R_payload ++ R_tail)
           (R_head_payload := R_head_payload ++ R_tail).
    + apply H. exact Hfresh_scrut.
    + exact e.
    + exact e0.
    + exact e1.
    + exact e2.
    + exact e3.
    + exact e4.
    + exact e5.
	    + exact e6.
	    + exact e7.
	    + exact e8.
	    + exact e9.
	    + apply root_env_lookup_params_none_b_app; assumption.
	    + exact e11.
	    + rewrite e12. symmetry.
	      apply root_env_add_params_roots_same_app_left.
	    + apply H0.
	      eapply root_env_tail_fresh_names_lookup_expr_branch; eassumption.
	    + exact e13.
	    + exact r.
	    + rewrite e14. symmetry.
	      apply root_env_remove_match_params_app_left.
	      exact Htail_params_none.
	    + apply root_env_excludes_params_app_local; assumption.
	    + exact e15.
	    + apply H1. exact Hfresh_branches.
	    + exact e16.
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
    eapply TERS_Replace_Resolved; eauto.
    + eapply place_resolved_write_target_app_left; eassumption.
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
  - replace (root_env_update x (root_set_union roots_old roots_new) R1 ++
        R_tail)
      with (root_env_update x (root_set_union roots_old roots_new)
        (R1 ++ R_tail)).
    eapply TERS_Assign_Resolved; eauto.
    + eapply place_resolved_write_target_app_left; eassumption.
    + eapply root_env_lookup_app_left; eassumption.
    + rewrite root_env_update_app_left with (roots_old := roots_old)
        by eassumption.
      reflexivity.
  - eapply TERS_BorrowShared; eauto.
  - eapply TERS_BorrowShared_Indirect; eauto.
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots R p = Some roots |- _ =>
        rewrite (place_borrow_roots_indirect (R ++ R_tail) p Hpath);
        rewrite (place_borrow_roots_indirect R p Hpath) in Hborrow;
        eapply root_env_lookup_app_left; exact Hborrow
    end.
  - eapply TERS_BorrowUnique; eauto.
  - eapply TERS_BorrowUnique_Indirect; eauto.
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots R p = Some roots |- _ =>
        rewrite (place_borrow_roots_indirect (R ++ R_tail) p Hpath);
        rewrite (place_borrow_roots_indirect R p Hpath) in Hborrow;
        eapply root_env_lookup_app_left; exact Hborrow
    end.
  - eapply TERS_DerefBorrowShared; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_DerefBorrowShared_Indirect; eauto.
    match goal with
    | Hpath : place_path p = None,
      Hlookup : place_root_lookup R p = Some roots |- _ =>
        rewrite (place_root_lookup_indirect (R ++ R_tail) p Hpath);
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_app_left; exact Hlookup
    end.
  - eapply TERS_DerefBorrowUnique; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_DerefBorrowUnique_Indirect; eauto.
    match goal with
    | Hpath : place_path p = None,
      Hlookup : place_root_lookup R p = Some roots |- _ =>
        rewrite (place_root_lookup_indirect (R ++ R_tail) p Hpath);
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_app_left; exact Hlookup
    end.
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
  - constructor.
  - assert (Hfresh_binders :
      root_env_tail_fresh_names R_tail binders).
    { eapply root_env_tail_fresh_names_lookup_expr_branch_binders;
      eassumption. }
    assert (Htail_params_none :
      root_env_lookup_params_none_b ps R_tail = true).
    { eapply root_env_tail_fresh_names_params_lookup_none.
      - exact Hfresh_binders.
      - intros x Hin.
	        rewrite (match_payload_params_names _ _ _ _ _ e1) in Hin.
        exact Hin. }
    assert (Htail_params_excl :
      root_env_excludes_params ps R_tail).
    { eapply root_env_tail_fresh_names_params_excludes.
      - exact Hfresh_binders.
      - intros x Hin.
	        rewrite (match_payload_params_names _ _ _ _ _ e1) in Hin.
        exact Hin. }
    eapply TERSMatchTail_Cons
      with (R_payload := R_payload ++ R_tail)
           (Rv_payload := Rv_payload ++ R_tail)
           (Rv := Rv ++ R_tail).
    + exact e0.
	    + exact e1.
	    + exact e2.
	    + exact e3.
	    + apply root_env_lookup_params_none_b_app; assumption.
	    + exact e5.
	    + rewrite e6. symmetry.
	      apply root_env_add_params_roots_same_app_left.
	    + apply H. eapply root_env_tail_fresh_names_lookup_expr_branch; eassumption.
	    + exact e7.
	    + exact r.
	    + rewrite e8. symmetry.
	      apply root_env_remove_match_params_app_left.
	      exact Htail_params_none.
	    + apply root_env_excludes_params_app_local; assumption.
	    + exact e9.
	    + exact e10.
    + apply root_env_equiv_app.
      * exact r1.
      * apply root_env_equiv_refl.
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
