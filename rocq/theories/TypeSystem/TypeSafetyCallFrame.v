From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCallFrameShadowSafe.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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
