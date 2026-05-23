From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCallFrameBindParams.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Fixpoint root_env_add_params_roots
    (ps : list param) (roots : list root_set) (R : root_env) : root_env :=
  match ps, roots with
  | p :: ps', roots_p :: roots' =>
      root_env_add (param_name p) roots_p
        (root_env_add_params_roots ps' roots' R)
  | _, _ => R
  end.

Lemma root_env_lookup_add_eq :
  forall x roots R,
    root_env_lookup x (root_env_add x roots R) = Some roots.
Proof.
  intros x roots R. unfold root_env_add. simpl.
  rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma root_env_lookup_add_neq :
  forall x y roots R,
    x <> y ->
    root_env_lookup y (root_env_add x roots R) = root_env_lookup y R.
Proof.
  intros x y roots R Hneq. unfold root_env_add. simpl.
  destruct (ident_eqb y x) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y. contradiction Hneq. reflexivity.
  - reflexivity.
Qed.

Lemma root_env_lookup_update_eq :
  forall x roots R roots_old,
    root_env_lookup x R = Some roots_old ->
    root_env_lookup x (root_env_update x roots R) = Some roots.
Proof.
  intros x roots R.
  induction R as [| [y roots_y] rest IH]; intros roots_old Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - simpl. rewrite Heq. reflexivity.
  - simpl. rewrite Heq. exact (IH roots_old Hlookup).
Qed.

Lemma root_env_lookup_update_neq :
  forall x y roots R,
    x <> y ->
    root_env_lookup y (root_env_update x roots R) = root_env_lookup y R.
Proof.
  intros x y roots R Hneq.
  induction R as [| [z roots_z] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x z) eqn:Hxz; simpl.
  - destruct (ident_eqb y z) eqn:Hyz.
    + apply ident_eqb_eq in Hxz. apply ident_eqb_eq in Hyz.
      subst z. subst y. contradiction Hneq. reflexivity.
    + reflexivity.
  - destruct (ident_eqb y z); try reflexivity.
    exact IH.
Qed.

Lemma root_env_lookup_remove_neq :
  forall x y R,
    x <> y ->
    root_env_lookup y (root_env_remove x R) = root_env_lookup y R.
Proof.
  intros x y R Hneq.
  induction R as [| [z roots_z] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x z) eqn:Hxz.
  - apply ident_eqb_eq in Hxz. subst z.
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y. contradiction Hneq. reflexivity.
    + reflexivity.
  - simpl.
    destruct (ident_eqb y z); try reflexivity.
    exact IH.
Qed.

Lemma root_env_equiv_app :
  forall R1 R1' R2 R2',
    root_env_equiv R1 R1' ->
    root_env_equiv R2 R2' ->
    root_env_equiv (R1 ++ R2) (R1' ++ R2').
Proof.
  unfold root_env_equiv.
  intros R1 R1' R2 R2' Heq1 Heq2 x.
  specialize (Heq1 x).
  specialize (Heq2 x).
  destruct (root_env_lookup x R1) as [roots1 |] eqn:Hlookup1;
    destruct (root_env_lookup x R1') as [roots1' |] eqn:Hlookup1';
    try contradiction.
  - rewrite (root_env_lookup_app_left x R1 R2 roots1 Hlookup1).
    rewrite (root_env_lookup_app_left x R1' R2' roots1' Hlookup1').
    exact Heq1.
  - rewrite (root_env_lookup_app_right x R1 R2 Hlookup1).
    rewrite (root_env_lookup_app_right x R1' R2' Hlookup1').
    exact Heq2.
Qed.

Lemma root_env_remove_lookup_none :
  forall x R,
    root_env_lookup x R = None ->
    root_env_remove x R = R.
Proof.
  intros x R.
  induction R as [| [y roots_y] rest IH]; intros Hlookup; simpl in *.
  - reflexivity.
  - destruct (ident_eqb x y); try discriminate.
    rewrite IH by exact Hlookup. reflexivity.
Qed.

Lemma root_env_remove_app_left :
  forall x R1 R2,
    root_env_lookup x R2 = None ->
    root_env_remove x (R1 ++ R2) = root_env_remove x R1 ++ R2.
Proof.
  intros x R1.
  induction R1 as [| [y roots_y] rest IH]; intros R2 Hlookup_tail;
    simpl in *.
  - apply root_env_remove_lookup_none. exact Hlookup_tail.
  - destruct (ident_eqb x y); try reflexivity.
    rewrite IH by exact Hlookup_tail. reflexivity.
Qed.

Lemma root_env_update_app_left :
  forall x roots R1 R2 roots_old,
    root_env_lookup x R1 = Some roots_old ->
    root_env_update x roots (R1 ++ R2) =
      root_env_update x roots R1 ++ R2.
Proof.
  intros x roots R1.
  induction R1 as [| [y roots_y] rest IH]; intros R2 roots_old Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y); try reflexivity.
  rewrite IH with (roots_old := roots_old) by exact Hlookup.
  reflexivity.
Qed.

Fixpoint root_env_remove_params (ps : list param) (R : root_env)
    : root_env :=
  match ps with
  | [] => R
  | p :: ps' => root_env_remove_params ps' (root_env_remove (param_name p) R)
  end.

Definition call_param_root_env
    (ps : list param) (arg_roots : list root_set) (R_tail : root_env)
    : root_env :=
  root_env_add_params_roots ps arg_roots
    (root_env_remove_params ps R_tail).

Lemma root_env_add_params_roots_app_tail :
  forall ps roots_list R_tail,
    root_env_add_params_roots ps roots_list R_tail =
      root_env_add_params_roots ps roots_list [] ++ R_tail.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R_tail;
    destruct roots_list as [| roots roots_list]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma root_env_remove_params_empty :
  forall ps,
    root_env_remove_params ps [] = [].
Proof.
  induction ps as [| p ps IH]; simpl; try reflexivity.
  exact IH.
Qed.

Lemma root_env_remove_params_app_left :
  forall ps R1 R2,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R2 = None) ->
    root_env_remove_params ps (R1 ++ R2) =
      root_env_remove_params ps R1 ++ R2.
Proof.
  induction ps as [| p ps IH]; intros R1 R2 Hlookup_tail; simpl.
  - reflexivity.
  - rewrite root_env_remove_app_left.
    + apply IH. intros x Hin.
      apply Hlookup_tail. right. exact Hin.
    + apply Hlookup_tail. left. reflexivity.
Qed.

Lemma call_param_root_env_app_tail :
  forall ps roots_list R_tail,
    call_param_root_env ps roots_list R_tail =
      call_param_root_env ps roots_list [] ++
        root_env_remove_params ps R_tail.
Proof.
  intros ps roots_list R_tail.
  unfold call_param_root_env at 1 2.
  rewrite root_env_remove_params_empty.
  apply root_env_add_params_roots_app_tail.
Qed.

Lemma root_env_add_params_roots_app_roots :
  forall ps qs roots_ps roots_qs R,
    List.length roots_ps = List.length ps ->
    root_env_add_params_roots (ps ++ qs) (roots_ps ++ roots_qs) R =
      root_env_add_params_roots ps roots_ps
        (root_env_add_params_roots qs roots_qs R).
Proof.
  induction ps as [| p ps IH]; intros qs roots_ps roots_qs R Hlen;
    destruct roots_ps as [| roots roots_ps]; simpl in *; try discriminate.
  - reflexivity.
  - inversion Hlen as [Hlen_tail].
    rewrite IH by exact Hlen_tail.
    reflexivity.
Qed.

Lemma root_env_add_params_roots_preserves_equiv :
  forall ps roots_list R R',
    root_env_equiv R R' ->
    root_env_equiv
      (root_env_add_params_roots ps roots_list R)
      (root_env_add_params_roots ps roots_list R').
Proof.
  induction ps as [| p ps IH]; intros roots_list R R' Heq;
    destruct roots_list as [| roots roots_list]; simpl.
  - exact Heq.
  - exact Heq.
  - exact Heq.
  - apply root_env_equiv_add.
    + apply root_set_equiv_refl.
    + apply IH. exact Heq.
Qed.

Lemma call_param_root_env_app_roots :
  forall ps qs roots_ps roots_qs R,
    List.length roots_ps = List.length ps ->
    call_param_root_env (ps ++ qs) (roots_ps ++ roots_qs) R =
      root_env_add_params_roots ps roots_ps
        (root_env_add_params_roots qs roots_qs
          (root_env_remove_params (ps ++ qs) R)).
Proof.
  intros ps qs roots_ps roots_qs R Hlen.
  unfold call_param_root_env.
  apply root_env_add_params_roots_app_roots. exact Hlen.
Qed.

Lemma params_alpha_refl_ts :
  forall ps,
    params_alpha ps ps.
Proof.
  apply params_alpha_refl.
Qed.

Lemma params_alpha_app_ts :
  forall ps psr qs qsr,
    params_alpha ps psr ->
    params_alpha qs qsr ->
    params_alpha (ps ++ qs) (psr ++ qsr).
Proof.
  intros ps psr qs qsr Halpha_ps Halpha_qs.
  induction Halpha_ps as [| p pr ps psr Hshape Halpha_tail IH];
    simpl.
  - exact Halpha_qs.
  - constructor; assumption.
Qed.

Lemma alpha_rename_fn_def_binding_params_alpha_ts :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    params_alpha (fn_params f ++ fn_captures f)
      (fn_params fr ++ fn_captures fr).
Proof.
  intros used f fr used' Hrename.
  apply params_alpha_app_ts.
  - pose proof (alpha_rename_fn_def_shape used f fr used' Hrename)
      as [_ [_ Hparams_alpha]].
    exact Hparams_alpha.
  - rewrite <- (alpha_rename_fn_def_captures used f fr used' Hrename).
    apply params_alpha_refl_ts.
Qed.

Lemma root_env_remove_app_right_lookup_none :
  forall x R1 R2,
    root_env_lookup x R1 = None ->
    root_env_remove x (R1 ++ R2) = R1 ++ root_env_remove x R2.
Proof.
  intros x R1.
  induction R1 as [| [y roots_y] R1 IH]; intros R2 Hlookup; simpl in *.
  - reflexivity.
  - destruct (ident_eqb x y) eqn:Heq; try discriminate.
    rewrite IH by exact Hlookup.
    reflexivity.
Qed.

Lemma root_env_remove_params_lookup_none_self :
  forall ps R,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R = None) ->
    root_env_remove_params ps R = R.
Proof.
  induction ps as [| p ps IH]; intros R Hfresh; simpl.
  - reflexivity.
  - rewrite root_env_remove_lookup_none.
    + apply IH. intros x Hin.
      apply Hfresh. right. exact Hin.
    + apply Hfresh. left. reflexivity.
Qed.

Lemma root_env_remove_params_app_right_lookup_none :
  forall ps R1 R2,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R1 = None) ->
    root_env_remove_params ps (R1 ++ R2) =
      R1 ++ root_env_remove_params ps R2.
Proof.
  induction ps as [| p ps IH]; intros R1 R2 Hfresh; simpl.
  - reflexivity.
  - rewrite root_env_remove_app_right_lookup_none.
    + rewrite IH.
      * reflexivity.
      * intros x Hin. apply Hfresh. right. exact Hin.
    + apply Hfresh. left. reflexivity.
Qed.

Lemma captured_call_runtime_root_env_tail_decompose :
  forall ps arg_roots Rcap R_args,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x Rcap = None) ->
    call_param_root_env ps arg_roots (Rcap ++ R_args) =
      call_param_root_env ps arg_roots Rcap ++
        root_env_remove_params ps R_args.
Proof.
  intros ps arg_roots Rcap R_args Hfresh_cap.
  unfold call_param_root_env.
  rewrite (root_env_remove_params_app_right_lookup_none
             ps Rcap R_args Hfresh_cap).
  rewrite (root_env_remove_params_lookup_none_self
             ps Rcap Hfresh_cap).
  rewrite (root_env_add_params_roots_app_tail
             ps arg_roots (Rcap ++ root_env_remove_params ps R_args)).
  rewrite (root_env_add_params_roots_app_tail ps arg_roots Rcap).
  rewrite app_assoc.
  reflexivity.
Qed.
