From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping AlphaEnvStructural AlphaRoots.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Shadow provenance alpha-renaming proofs                             *)
(* ------------------------------------------------------------------ *)

Definition root_set_sctx_roots_named (roots : root_set) (Σ : sctx) : Prop :=
  forall z,
    In (RStore z) roots ->
    In z (ctx_names Σ).

Definition root_env_sctx_roots_named (R : root_env) (Σ : sctx) : Prop :=
  forall x roots z,
    root_env_lookup x R = Some roots ->
    In (RStore z) roots ->
    In z (ctx_names Σ).

Definition root_env_sctx_keys_named (R : root_env) (Σ : sctx) : Prop :=
  root_env_keys_named R (ctx_names Σ).

Lemma root_env_lookup_params_none_b_from_sctx_keys :
  forall ps R Σ,
    root_env_sctx_keys_named R Σ ->
    ctx_lookup_params_none_b ps Σ = true ->
    root_env_lookup_params_none_b ps R = true.
Proof.
  induction ps as [| [m x T] ps IH]; intros R Σ Hkeys Hfresh; simpl in *.
  - reflexivity.
  - destruct (ctx_lookup_state x Σ) as [[Tx st] |] eqn:Hctx;
      try discriminate.
    destruct (root_env_lookup x R) as [roots |] eqn:Hlookup.
    + exfalso.
      destruct (ctx_lookup_state_in_names_some Σ x) as [Tx' [st' Hsome]].
      * apply Hkeys.
        eapply root_env_lookup_some_in_names. exact Hlookup.
      * rewrite Hctx in Hsome. discriminate.
    + eapply IH.
      * exact Hkeys.
      * exact Hfresh.
Qed.

Lemma initial_root_env_for_params_origin_sctx_keys_named :
  forall ps_orig ps_current,
    List.length ps_orig = List.length ps_current ->
    root_env_sctx_keys_named
      (initial_root_env_for_params_origin ps_orig ps_current)
      (sctx_of_ctx (params_ctx ps_current)).
Proof.
  unfold root_env_sctx_keys_named, root_env_keys_named, sctx_of_ctx.
  intros ps_orig ps_current Hlen x Hin.
  rewrite initial_root_env_for_params_origin_names in Hin; assumption.
Qed.

Lemma initial_root_env_for_params_origin_sctx_roots_named :
  forall ps_orig ps_current,
    root_env_sctx_roots_named
      (initial_root_env_for_params_origin ps_orig ps_current)
      (sctx_of_ctx (params_ctx ps_current)).
Proof.
  unfold root_env_sctx_roots_named.
  induction ps_orig as [| p_orig ps_orig IH];
    intros ps_current x roots z Hlookup Hin;
    destruct ps_current as [| p_current ps_current]; simpl in *;
    try discriminate.
  destruct (ident_eqb x (param_name p_current)) eqn:Heq.
  - inversion Hlookup; subst roots. simpl in Hin.
    destruct Hin as [Hin | Hin]; inversion Hin.
  - right. eapply IH; eassumption.
Qed.

Lemma root_env_sctx_keys_named_fresh_not_in :
  forall R Σ x,
    root_env_sctx_keys_named R Σ ->
    ~ In x (ctx_names Σ) ->
    ~ In x (root_env_names R).
Proof.
  unfold root_env_sctx_keys_named, root_env_keys_named.
  intros R Σ x Hnamed Hfresh Hin.
  apply Hfresh. apply Hnamed. exact Hin.
Qed.

Lemma root_env_sctx_keys_named_fresh_lookup_none :
  forall R Σ x,
    root_env_sctx_keys_named R Σ ->
    ~ In x (ctx_names Σ) ->
    root_env_lookup x R = None.
Proof.
  intros R Σ x Hkeys Hfresh.
  apply root_env_lookup_not_in_names.
  eapply root_env_sctx_keys_named_fresh_not_in; eassumption.
Qed.

Lemma root_set_sctx_roots_named_nil :
  forall Σ,
    root_set_sctx_roots_named [] Σ.
Proof.
  unfold root_set_sctx_roots_named. intros Σ z Hin. contradiction.
Qed.

Lemma root_set_sctx_roots_named_single :
  forall x Σ,
    In x (ctx_names Σ) ->
    root_set_sctx_roots_named [RStore x] Σ.
Proof.
  unfold root_set_sctx_roots_named.
  intros x Σ Hin z Hroot. simpl in Hroot.
  destruct Hroot as [Hroot | Hroot]; try contradiction.
  inversion Hroot. subst z. exact Hin.
Qed.

Lemma root_set_sctx_roots_named_union :
  forall roots_left roots_right Σ,
    root_set_sctx_roots_named roots_left Σ ->
    root_set_sctx_roots_named roots_right Σ ->
    root_set_sctx_roots_named (root_set_union roots_left roots_right) Σ.
Proof.
  unfold root_set_sctx_roots_named.
  intros roots_left roots_right Σ Hleft Hright z Hin.
  apply root_set_union_in_inv in Hin.
  destruct Hin as [Hin | Hin]; [apply Hleft | apply Hright]; exact Hin.
Qed.

Lemma root_sets_sctx_roots_named_union :
  forall sets Σ,
    Forall (fun roots => root_set_sctx_roots_named roots Σ) sets ->
    root_set_sctx_roots_named (root_sets_union sets) Σ.
Proof.
  intros sets Σ Hsets.
  induction Hsets as [| roots rest Hroots Hrest IH]; simpl.
  - apply root_set_sctx_roots_named_nil.
  - apply root_set_sctx_roots_named_union; assumption.
Qed.

Lemma root_set_sctx_roots_named_same_bindings :
  forall roots Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named roots Σ'.
Proof.
  unfold root_set_sctx_roots_named.
  intros roots Σ Σ' Hsame Hnamed z Hin.
  rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
  apply Hnamed. exact Hin.
Qed.

Ltac solve_sctx_keys_single_ih :=
  match goal with
  | IH : root_env_no_shadow ?R ->
          root_env_sctx_keys_named ?R ?Σ ->
          root_env_sctx_keys_named ?R' ?Σ',
    Hrn : root_env_no_shadow ?R,
    Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
      exact (IH Hrn Henv)
  end.

Ltac solve_sctx_keys_callee_args :=
  match goal with
  | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
    Hcallee : root_env_no_shadow ?R ->
      root_env_sctx_keys_named ?R ?Σ ->
      root_env_sctx_keys_named ?R1 ?Σ1,
    Hargs : root_env_no_shadow ?R1 ->
      root_env_sctx_keys_named ?R1 ?Σ1 ->
      root_env_sctx_keys_named ?R2 ?Σ2,
    Hrn : root_env_no_shadow ?R,
    Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
      pose proof (Hcallee Hrn Hkeys) as Hkeys1;
      assert (Hrn1 : root_env_no_shadow R1)
        by (eapply typed_env_roots_no_shadow;
            [eapply typed_env_roots_shadow_safe_roots; exact Htyped
            | exact Hrn]);
      exact (Hargs Hrn1 Hkeys1)
  end.

Ltac solve_sctx_roots_args_union :=
  match goal with
  | IH : root_env_no_shadow ?R ->
          root_env_sctx_roots_named ?R ?Σ ->
          root_env_sctx_roots_named ?R' ?Σ' /\
          Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
    Hrn : root_env_no_shadow ?R,
    Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
      destruct (IH Hrn Henv) as [Henv_args Hroots_args];
      split;
      [ exact Henv_args
      | apply root_sets_sctx_roots_named_union; exact Hroots_args ]
  end.

Ltac solve_sctx_roots_single_ih :=
  match goal with
  | IH : root_env_no_shadow ?R ->
          root_env_sctx_roots_named ?R ?Σ ->
          root_env_sctx_roots_named ?R' ?Σ' /\
          root_set_sctx_roots_named ?roots ?Σ',
    Hrn : root_env_no_shadow ?R,
    Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
      exact (IH Hrn Henv)
  end.

Lemma root_env_sctx_roots_named_same_bindings :
  forall R Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R Σ'.
Proof.
  unfold root_env_sctx_roots_named.
  intros R Σ Σ' Hsame Hnamed x roots z Hlookup Hin.
  rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_sctx_keys_named_same_bindings :
  forall R Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R Σ'.
Proof.
  unfold root_env_sctx_keys_named.
  intros R Σ Σ' Hsame Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
    exact Hin.
Qed.

Lemma root_env_sctx_roots_named_add_params_env :
  forall ps R Σ,
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R (sctx_add_params ps Σ).
Proof.
  unfold root_env_sctx_roots_named, sctx_add_params, ctx_add_params.
  intros ps R Σ Hnamed x roots z Hlookup Hin.
  rewrite ctx_names_app.
  apply in_or_app. right.
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_sctx_keys_named_add_params_env :
  forall ps R Σ,
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R (sctx_add_params ps Σ).
Proof.
  unfold root_env_sctx_keys_named, sctx_add_params, ctx_add_params.
  intros ps R Σ Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite ctx_names_app.
    apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_lookup_sctx_roots_named :
  forall R Σ x roots,
    root_env_lookup x R = Some roots ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ.
Proof.
  unfold root_env_sctx_roots_named, root_set_sctx_roots_named.
  intros R Σ x roots Hlookup Hnamed z Hin.
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_sctx_roots_named_fresh_exclude :
  forall roots Σ x,
    root_set_sctx_roots_named roots Σ ->
    ~ In x (ctx_names Σ) ->
    roots_exclude x roots.
Proof.
  unfold root_set_sctx_roots_named, roots_exclude.
  intros roots Σ x Hnamed Hfresh Hin.
  apply Hfresh. apply Hnamed. exact Hin.
Qed.

Lemma root_env_sctx_roots_named_fresh_excludes :
  forall R Σ x,
    root_env_sctx_roots_named R Σ ->
    ~ In x (ctx_names Σ) ->
    root_env_excludes x R.
Proof.
  unfold root_env_excludes.
  intros R Σ x Hnamed Hfresh y roots Hlookup _.
  apply root_set_sctx_roots_named_fresh_exclude with (Σ := Σ).
  - eapply root_env_lookup_sctx_roots_named; eassumption.
  - exact Hfresh.
Qed.

Lemma root_env_sctx_support_fresh_let_init :
  forall R roots Σ x,
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    ~ In x (ctx_names Σ) ->
    root_env_lookup x R = None /\
    roots_exclude x roots /\
    root_env_excludes x R.
Proof.
  intros R roots Σ x Hkeys Henv Hroots Hfresh.
  repeat split.
  - eapply root_env_sctx_keys_named_fresh_lookup_none; eassumption.
  - eapply root_set_sctx_roots_named_fresh_exclude; eassumption.
  - eapply root_env_sctx_roots_named_fresh_excludes; eassumption.
Qed.

Lemma ctx_names_remove_not_in_no_shadow :
  forall x Σ,
    sctx_no_shadow Σ ->
    ~ In x (ctx_names (sctx_remove x Σ)).
Proof.
  unfold sctx_no_shadow, sctx_remove.
  intros x Σ Hnodup.
  induction Σ as [| [[[y T] st] m] rest IH]; simpl in *.
  - intros Hin. contradiction.
  - inversion Hnodup as [| ? ? Hy_notin Hnodup_tail]; subst.
    destruct (ident_eqb x y) eqn:Hxy.
    + apply ident_eqb_eq in Hxy. subst y. exact Hy_notin.
    + simpl. intros Hin.
      destruct Hin as [Hin | Hin].
      * subst y. rewrite ident_eqb_refl in Hxy. discriminate.
      * apply IH.
        -- exact Hnodup_tail.
        -- exact Hin.
Qed.

Lemma root_set_sctx_roots_named_equiv :
  forall roots roots' Σ,
    root_set_equiv roots roots' ->
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named roots' Σ.
Proof.
  unfold root_set_sctx_roots_named.
  intros roots roots' Σ Heq Hnamed z Hin.
  apply Hnamed. apply Heq. exact Hin.
Qed.

Lemma root_env_sctx_roots_named_equiv :
  forall R R' Σ,
    root_env_equiv R R' ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ.
Proof.
  unfold root_env_sctx_roots_named.
  intros R R' Σ Heq Hnamed x roots z Hlookup Hin.
  destruct (root_env_equiv_lookup_r R R' x roots Heq Hlookup)
    as [roots0 [Hlookup0 Hroots]].
  eapply Hnamed.
  - exact Hlookup0.
  - apply Hroots. exact Hin.
Qed.

Lemma root_env_sctx_keys_named_equiv :
  forall R R' Σ,
    root_env_no_shadow R' ->
    root_env_equiv R R' ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ.
Proof.
  unfold root_env_sctx_keys_named, root_env_keys_named.
  intros R R' Σ Hns' Heq Hkeys x Hin.
  assert (Hexists : exists roots, In (x, roots) R').
  { clear -Hin.
    induction R' as [| [y roots_y] rest IH]; simpl in *.
    - contradiction.
    - destruct Hin as [Hin | Hin].
      + subst x. exists roots_y. left. reflexivity.
      + destruct (IH Hin) as [roots Hpair].
        exists roots. right. exact Hpair. }
  destruct Hexists as [roots Hpair].
  assert (Hlookup' : root_env_lookup x R' = Some roots)
    by (eapply root_env_lookup_in_no_shadow; eassumption).
  destruct (root_env_equiv_lookup_r R R' x roots Heq Hlookup')
    as [roots0 [Hlookup _]].
  apply Hkeys.
  eapply root_env_lookup_some_in_names. exact Hlookup.
Qed.

Lemma ctx_alpha_lookup_rename_in_names :
  forall rho Σ Σr x,
    ctx_alpha rho Σ Σr ->
    In x (ctx_names Σ) ->
    In (lookup_rename x rho) (ctx_names Σr).
Proof.
  intros rho Σ Σr x Halpha.
  induction Halpha; intros Hin; simpl in *.
  - exact Hin.
  - destruct Hin as [Hin | Hin].
    + subst x0. simpl. rewrite ident_eqb_refl. left. reflexivity.
    + destruct (ident_eqb x0 x) eqn:Hx0x.
      * apply ident_eqb_eq in Hx0x. subst x0.
        simpl. rewrite ident_eqb_refl. left. reflexivity.
      * simpl.
        assert (Hxx0 : ident_eqb x x0 = false).
        { apply ident_eqb_neq. intro Heq. subst x0.
          rewrite ident_eqb_refl in Hx0x. discriminate. }
        rewrite Hxx0. right. apply IHHalpha. exact Hin.
Qed.

Lemma ctx_alpha_no_collision_on :
  forall rho Σ Σr,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    rename_no_collision_on rho (ctx_names Σ).
Proof.
  intros rho Σ Σr Halpha.
  induction Halpha; intros Hnodup Hnodup_r.
  - unfold rename_no_collision_on, rename_no_collision_for.
    intros x Hin y Hyin Hyx Heq. simpl in Heq. contradiction.
  - inversion Hnodup as [| ? ? Hx_notin Hnodup_tail]; subst.
    inversion Hnodup_r as [| ? ? Hxr_notin Hnodup_r_tail]; subst.
    unfold rename_no_collision_on, rename_no_collision_for in *.
    intros a Ha y Hy Hya Heq.
    simpl in Ha, Hy.
    destruct Ha as [Ha | Ha]; destruct Hy as [Hy | Hy].
    + subst. contradiction.
    + subst a.
      assert (Hyx : y <> x).
      { intros Heq_yx. subst y. contradiction. }
      simpl in Heq. rewrite ident_eqb_refl in Heq.
      destruct (ident_eqb y x) eqn:Hyeq.
      * apply ident_eqb_eq in Hyeq. contradiction.
      * apply Hxr_notin.
        rewrite <- Heq.
        eapply ctx_alpha_lookup_rename_in_names; eassumption.
    + subst y.
      assert (Hax : a <> x).
      { intros Heq_ax. subst a. contradiction. }
      simpl in Heq. rewrite ident_eqb_refl in Heq.
      destruct (ident_eqb a x) eqn:Heq_ax.
      * apply ident_eqb_eq in Heq_ax. contradiction.
      * apply Hxr_notin.
        rewrite Heq.
        eapply ctx_alpha_lookup_rename_in_names; eassumption.
    + assert (Hax : a <> x).
      { intros Heq_ax. subst a. contradiction. }
      assert (Hyx : y <> x).
      { intros Heq_yx. subst y. contradiction. }
      simpl in Heq.
      destruct (ident_eqb a x) eqn:Heq_ax.
      * apply ident_eqb_eq in Heq_ax. contradiction.
      * destruct (ident_eqb y x) eqn:Hyeq.
        -- apply ident_eqb_eq in Hyeq. contradiction.
        -- pose proof (IHHalpha Hnodup_tail Hnodup_r_tail
             a Ha y Hy Hya) as Hneq.
           apply Hneq. exact Heq.
Qed.

Lemma ctx_alpha_nodup_names :
  forall rho Σ Σr,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr).
Proof.
  intros rho Σ Σr Halpha.
  induction Halpha; intros Hnodup.
  - exact Hnodup.
  - inversion Hnodup as [| ? ? _ Hnodup_tail]; subst.
    simpl. constructor.
    + exact H.
    + apply IHHalpha. exact Hnodup_tail.
Qed.

Lemma ctx_alpha_renamed_name_preimage :
  forall rho Σ Σr xr,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    In xr (ctx_names Σr) ->
    exists x,
      In x (ctx_names Σ) /\ lookup_rename x rho = xr.
Proof.
  intros rho Σ Σr xr Halpha.
  induction Halpha; intros Hnodup Hin; simpl in *.
  - exists xr. split; [exact Hin | reflexivity].
  - inversion Hnodup as [| ? ? Hx_notin Hnodup_tail]; subst.
    simpl in *.
    destruct Hin as [Hin | Hin].
    + subst xr.
      exists x. split.
      * left. reflexivity.
      * simpl. rewrite ident_eqb_refl. reflexivity.
    + destruct (IHHalpha Hnodup_tail Hin) as [y [Hy Hlookup]].
      exists y. split.
      * right. exact Hy.
      * simpl.
        destruct (ident_eqb y x) eqn:Hyx.
        -- apply ident_eqb_eq in Hyx. subst y.
           contradiction.
        -- exact Hlookup.
Qed.

Lemma alpha_rename_fn_def_initial_support_facts :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params f))) ->
    exists rho used_params,
      alpha_rename_params []
        (param_names (fn_params f) ++
         param_names (fn_captures f) ++ free_vars_expr (fn_body f) ++ used)
        (fn_params f) = (fn_params fr, rho, used_params) /\
      alpha_rename_expr rho used_params (fn_body f) =
        (fn_body fr, used') /\
      ctx_alpha rho
        (sctx_of_ctx (params_ctx (fn_params f)))
        (sctx_of_ctx (params_ctx (fn_params fr))) /\
      root_env_no_shadow (initial_root_env_for_fn f) /\
      root_env_no_shadow
        (initial_root_env_for_params_origin
          (fn_params f) (fn_params fr)) /\
      root_env_equiv
        (initial_root_env_for_params_origin
          (fn_params f) (fn_params fr))
        (root_env_rename rho (initial_root_env_for_fn f)) /\
      root_env_sctx_keys_named (initial_root_env_for_fn f)
        (sctx_of_ctx (params_ctx (fn_params f))) /\
      root_env_sctx_roots_named (initial_root_env_for_fn f)
        (sctx_of_ctx (params_ctx (fn_params f))) /\
      rename_no_collision_on rho
        (root_env_names (initial_root_env_for_fn f)) /\
      (forall x,
        In x (ctx_names
          (sctx_of_ctx (params_ctx (fn_params fr)))) ->
        In x used_params) /\
      (forall x, In x (rename_range rho) -> In x used_params) /\
      disjoint_names (free_vars_expr (fn_body f)) (rename_range rho).
Proof.
  intros used f fr used' Hrename Hnodup.
  destruct (alpha_rename_fn_def_params_body_facts
      used f fr used' Hrename)
    as (rho & used_params & Hps & Hbody & Halpha & Hctx_used &
        Hrange_used & Hdisj).
  exists rho, used_params.
  repeat split.
  - exact Hps.
  - exact Hbody.
  - exact Halpha.
  - apply initial_root_env_for_fn_no_shadow. exact Hnodup.
  - apply initial_root_env_for_params_origin_no_shadow.
    + apply params_alpha_length.
      eapply alpha_rename_params_shape. exact Hps.
    + eapply alpha_rename_params_names_nodup. exact Hps.
  - destruct (alpha_rename_fn_def_initial_root_env_rename
        used f fr used' Hrename Hnodup) as
      [rho0 [used_params0 [Hps0 Hroot_eq]]].
    rewrite Hps in Hps0. inversion Hps0; subst rho0 used_params0.
    rewrite Hroot_eq. apply root_env_equiv_refl.
  - unfold initial_root_env_for_fn.
    apply initial_root_env_for_params_origin_sctx_keys_named.
    reflexivity.
  - unfold initial_root_env_for_fn.
    apply initial_root_env_for_params_origin_sctx_roots_named.
  - rewrite initial_root_env_for_fn_names.
    eapply ctx_alpha_no_collision_on.
    + exact Halpha.
    + exact Hnodup.
    + eapply alpha_rename_params_names_nodup. exact Hps.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
Qed.

Lemma root_set_sctx_roots_named_rename :
  forall rho Σ Σr roots rootsr,
    ctx_alpha rho Σ Σr ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named rootsr Σr.
Proof.
  unfold root_set_sctx_roots_named.
  intros rho Σ Σr roots rootsr Halpha Heq Hnamed z Hin.
  apply Heq in Hin.
  apply root_set_rename_in_inv in Hin.
  destruct Hin as [atom [Hin Hatom]].
  destruct atom as [y | y]; simpl in Hatom; inversion Hatom; subst z.
  eapply ctx_alpha_lookup_rename_in_names.
  - exact Halpha.
  - apply Hnamed. exact Hin.
Qed.

Lemma root_env_sctx_roots_named_rename :
  forall rho Σ Σr R Rr,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named Rr Σr.
Proof.
  unfold root_env_sctx_roots_named.
  intros rho Σ Σr R Rr Halpha Hns Heq Hnamed x roots z Hlookup Hin.
  destruct (root_env_equiv_lookup_l Rr (root_env_rename rho R)
    x roots Heq Hlookup) as [roots_ren [Hlookup_ren Hroots]].
  destruct (root_env_lookup_rename_inv rho R x roots_ren Hns Hlookup_ren)
    as [y [roots0 [Hlookup0 [Hx Hroots_ren]]]].
  subst x roots_ren.
  apply Hroots in Hin.
  apply root_set_rename_in_inv in Hin.
  destruct Hin as [atom [Hin0 Hatom]].
  destruct atom as [w | w]; simpl in Hatom; inversion Hatom; subst z.
  eapply ctx_alpha_lookup_rename_in_names.
  - exact Halpha.
  - eapply Hnamed; eassumption.
Qed.

Lemma root_env_sctx_keys_named_rename :
  forall rho Σ Σr R Rr,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named Rr Σr.
Proof.
  intros rho Σ Σr R Rr Halpha Hns Heq Hkeys.
  eapply root_env_sctx_keys_named_equiv.
  - exact Hns.
  - apply root_env_equiv_sym. exact Heq.
  - unfold root_env_sctx_keys_named.
    eapply root_env_keys_named_rename.
    + exact Hkeys.
    + intros x Hin.
      eapply ctx_alpha_lookup_rename_in_names; eassumption.
Qed.

Lemma root_env_sctx_support_fresh_renamed_let_init :
  forall rho R Rr roots rootsr Σ Σr xr,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    ~ In xr (ctx_names Σr) ->
    root_env_lookup xr Rr = None /\
    roots_exclude xr rootsr /\
    root_env_excludes xr Rr.
Proof.
  intros rho R Rr roots rootsr Σ Σr xr Halpha HnsR HnsRr HRr Hrootsr
    Hkeys Hroots Hroots_set Hfresh.
  assert (Hkeys_r : root_env_sctx_keys_named Rr Σr).
  { eapply root_env_sctx_keys_named_rename; eassumption. }
  assert (Hroots_r : root_env_sctx_roots_named Rr Σr).
  { eapply root_env_sctx_roots_named_rename.
    - exact Halpha.
    - exact HnsR.
    - exact HRr.
    - exact Hroots. }
  assert (Hroots_set_r : root_set_sctx_roots_named rootsr Σr).
  { eapply root_set_sctx_roots_named_rename.
    - exact Halpha.
    - exact Hrootsr.
    - exact Hroots_set. }
  eapply root_env_sctx_support_fresh_let_init; eassumption.
Qed.

Lemma ctx_alpha_lookup_rename_fresh_neq :
  forall rho Σ Σr x xr,
    ctx_alpha rho Σ Σr ->
    In x (ctx_names Σ) ->
    ~ In xr (ctx_names Σr) ->
    lookup_rename x rho <> xr.
Proof.
  intros rho Σ Σr x xr Halpha Hin Hfresh Heq.
  apply Hfresh.
  rewrite <- Heq.
  eapply ctx_alpha_lookup_rename_in_names; eassumption.
Qed.

Lemma ctx_alpha_bound_no_collision_for :
  forall rho Σ Σr x xr y,
    ctx_alpha rho Σ Σr ->
    ~ In xr (ctx_names Σr) ->
    In y (ctx_names Σ) ->
    y <> x ->
    lookup_rename y ((x, xr) :: rho) <> xr.
Proof.
  intros rho Σ Σr x xr y Halpha Hfresh Hin Hyx.
  simpl.
  destruct (ident_eqb y x) eqn:Hyx_b.
  - apply ident_eqb_eq in Hyx_b. contradiction.
  - eapply ctx_alpha_lookup_rename_fresh_neq; eassumption.
Qed.

Lemma root_set_sctx_roots_named_bound_no_collision :
  forall rho Σ Σr roots x xr y,
    ctx_alpha rho Σ Σr ->
    root_set_sctx_roots_named roots Σ ->
    ~ In xr (ctx_names Σr) ->
    In (RStore y) roots ->
    y <> x ->
    lookup_rename y ((x, xr) :: rho) <> xr.
Proof.
  intros rho Σ Σr roots x xr y Halpha Hroots Hfresh Hin Hyx.
  eapply ctx_alpha_bound_no_collision_for.
  - exact Halpha.
  - exact Hfresh.
  - apply Hroots. exact Hin.
  - exact Hyx.
Qed.

Lemma root_env_sctx_roots_named_bound_no_collision :
  forall rho Σ Σr R x xr y roots z,
    ctx_alpha rho Σ Σr ->
    root_env_sctx_roots_named R Σ ->
    ~ In xr (ctx_names Σr) ->
    root_env_lookup y R = Some roots ->
    In (RStore z) roots ->
    z <> x ->
    lookup_rename z ((x, xr) :: rho) <> xr.
Proof.
  intros rho Σ Σr R x xr y roots z Halpha Henv Hfresh
    Hlookup Hin Hzx.
  eapply ctx_alpha_bound_no_collision_for.
  - exact Halpha.
  - exact Hfresh.
  - eapply Henv; eassumption.
  - exact Hzx.
Qed.

Lemma root_env_sctx_keys_named_bound_no_collision :
  forall rho Σ Σr R x xr y,
    ctx_alpha rho Σ Σr ->
    root_env_sctx_keys_named R Σ ->
    ~ In xr (ctx_names Σr) ->
    In y (root_env_names R) ->
    y <> x ->
    lookup_rename y ((x, xr) :: rho) <> xr.
Proof.
  intros rho Σ Σr R x xr y Halpha Hkeys Hfresh Hin Hyx.
  eapply ctx_alpha_bound_no_collision_for.
  - exact Halpha.
  - exact Hfresh.
  - apply Hkeys. exact Hin.
  - exact Hyx.
Qed.

Lemma root_env_sctx_keys_named_added_bound_no_collision :
  forall rho Σ Σr R x xr T m y,
    ctx_alpha rho Σ Σr ->
    root_env_sctx_keys_named R (sctx_add x T m Σ) ->
    ~ In xr (ctx_names Σr) ->
    In y (root_env_names R) ->
    y <> x ->
    lookup_rename y ((x, xr) :: rho) <> xr.
Proof.
  intros rho Σ Σr R x xr T m y Halpha Hkeys Hfresh Hin Hyx.
  eapply ctx_alpha_bound_no_collision_for.
  - exact Halpha.
  - exact Hfresh.
  - specialize (Hkeys y Hin). simpl in Hkeys.
    destruct Hkeys as [Hkeys | Hkeys].
    + subst y. contradiction.
    + exact Hkeys.
  - exact Hyx.
Qed.

Lemma root_env_sctx_keys_named_added_no_collision_for_head :
  forall rho Σ Σr R x xr T m,
    ctx_alpha rho Σ Σr ->
    root_env_sctx_keys_named R (sctx_add x T m Σ) ->
    ~ In xr (ctx_names Σr) ->
    rename_no_collision_for ((x, xr) :: rho) x (root_env_names R).
Proof.
  unfold rename_no_collision_for.
  intros rho Σ Σr R x xr T m Halpha Hkeys Hfresh y Hin Hyx.
  simpl. rewrite ident_eqb_refl.
  eapply root_env_sctx_keys_named_added_bound_no_collision; eassumption.
Qed.

Lemma root_env_sctx_keys_named_lookup_rename_fresh :
  forall rho Σ Σr R xr,
    ctx_alpha rho Σ Σr ->
    root_env_sctx_keys_named R Σ ->
    ~ In xr (ctx_names Σr) ->
    forall y, In y (root_env_names R) -> lookup_rename y rho <> xr.
Proof.
  intros rho Σ Σr R xr Halpha Hkeys Hfresh y Hin.
  eapply ctx_alpha_lookup_rename_fresh_neq; eauto.
Qed.

Lemma rename_no_collision_on_cons_lookup_rename_fresh :
  forall rho x xr names,
    ~ In x names ->
    rename_no_collision_on rho names ->
    (forall y, In y names -> lookup_rename y rho <> xr) ->
    rename_no_collision_on ((x, xr) :: rho) (x :: names).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho x xr names Hx_notin Hnocoll Hfresh x0 Hx0 y Hy Hyx0.
  simpl in Hx0, Hy.
  destruct Hx0 as [Hx0 | Hx0].
  - subst x0.
    destruct Hy as [Hy | Hy].
    + subst y. contradiction.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y. contradiction.
      * intros Heq. apply (Hfresh y Hy).
        rewrite ident_eqb_refl in Heq. exact Heq.
  - destruct Hy as [Hy | Hy].
    + subst y.
      simpl.
      destruct (ident_eqb x0 x) eqn:Hx0x.
      * apply ident_eqb_eq in Hx0x. subst x0. contradiction.
      * intros Heq. apply (Hfresh x0 Hx0).
        rewrite ident_eqb_refl in Heq. symmetry. exact Heq.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y. contradiction.
      * destruct (ident_eqb x0 x) eqn:Hx0x.
        -- apply ident_eqb_eq in Hx0x. subst x0. contradiction.
        -- eapply Hnocoll; eassumption.
Qed.

Lemma root_env_add_shadow_safe_rename_no_collision_on :
  forall rho Σ Σr R x xr roots,
    ctx_alpha rho Σ Σr ->
    root_env_lookup x R = None ->
    root_env_sctx_keys_named R Σ ->
    ~ In xr (ctx_names Σr) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on ((x, xr) :: rho)
      (root_env_names (root_env_add x roots R)).
Proof.
  intros rho Σ Σr R x xr roots Halpha Hlookup Hkeys Hfresh Hnocoll.
  rewrite root_env_names_add.
  apply rename_no_collision_on_cons_lookup_rename_fresh.
  - eapply root_env_lookup_none_not_in_names. exact Hlookup.
  - exact Hnocoll.
  - eapply root_env_sctx_keys_named_lookup_rename_fresh; eassumption.
Qed.

Lemma root_env_add_shadow_safe_rename_equiv :
  forall rho R Rr x xr roots rootsr,
    root_env_no_shadow R ->
    root_env_lookup x R = None ->
    root_env_excludes x R ->
    roots_exclude x roots ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_env_equiv (root_env_add xr rootsr Rr)
      (root_env_rename ((x, xr) :: rho) (root_env_add x roots R)).
Proof.
  intros rho R Rr x xr roots rootsr Hns Hlookup Hexcl Hroots_excl
    HRr Hrootsr.
  rewrite root_env_rename_add.
  simpl. rewrite ident_eqb_refl.
  apply root_env_equiv_add.
  - eapply root_set_equiv_trans.
    + exact Hrootsr.
    + apply root_set_equiv_sym.
      apply root_set_rename_cons_roots_exclude. exact Hroots_excl.
  - eapply root_env_equiv_trans.
    + exact HRr.
    + apply root_env_equiv_sym.
      eapply root_env_rename_cons_root_env_excludes; eassumption.
Qed.

Lemma root_set_shadow_safe_rename_body_equiv :
  forall rho roots rootsr x xr,
    roots_exclude x roots ->
    root_set_equiv rootsr (root_set_rename ((x, xr) :: rho) roots) ->
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros rho roots rootsr x xr Hexcl Heq.
  eapply root_set_equiv_trans.
  - exact Heq.
  - apply root_set_rename_cons_roots_exclude. exact Hexcl.
Qed.

Lemma alpha_rename_params_root_set_rename_excluded :
  forall rho used ps psr rho' used' roots,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    roots_exclude_params ps roots ->
    root_set_equiv (root_set_rename rho' roots) (root_set_rename rho roots).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used' roots
    Hrename Hexcl.
  - simpl in Hrename. inversion Hrename; subst.
    apply root_set_equiv_refl.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hexcl.
    inversion Hexcl as [| ? ? Hexcl_x Hexcl_tail]; subst.
    eapply root_set_equiv_trans.
    + apply root_set_rename_cons_roots_exclude. exact Hexcl_x.
    + eapply IH.
      * exact Htail.
      * exact Hexcl_tail.
Qed.

Lemma alpha_rename_params_lookup_rename_excluded :
  forall rho used ps psr rho' used' x,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ~ In x (ctx_names (params_ctx ps)) ->
    lookup_rename x rho' = lookup_rename x rho.
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m xp T] ps IH]; intros rho used psr rho' used' x
    Hrename Hnotin.
  - simpl in Hrename. inversion Hrename; subst.
    reflexivity.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident xp used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnotin |- *.
    destruct (ident_eqb x xp) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      exfalso. apply Hnotin. left. reflexivity.
    + eapply IH.
      * exact Htail.
      * intro Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma alpha_rename_params_root_env_rename_excluded :
  forall rho used ps psr rho' used' R,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    root_env_no_shadow R ->
    root_env_lookup_params_none_b ps R = true ->
    root_env_excludes_params ps R ->
    root_env_equiv (root_env_rename rho' R) (root_env_rename rho R).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used' R
    Hrename Hns Hlookup Hexcl.
  - simpl in Hrename. inversion Hrename; subst.
    apply root_env_equiv_refl.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hlookup.
    destruct (root_env_lookup x R) as [roots_x |] eqn:Hlookup_x;
      try discriminate.
    simpl in Hexcl.
    inversion Hexcl as [| ? ? Hexcl_x Hexcl_tail]; subst.
    eapply root_env_equiv_trans.
    + eapply root_env_rename_cons_root_env_excludes.
      * exact Hns.
      * exact Hlookup_x.
      * exact Hexcl_x.
    + eapply IH.
      * exact Htail.
      * exact Hns.
      * exact Hlookup.
      * exact Hexcl_tail.
Qed.

Lemma root_env_excludes_add_params_roots_same :
  forall ps roots R x,
    roots_exclude x roots ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_add_params_roots_same ps roots R).
Proof.
  induction ps as [| [m y T] ps IH]; intros roots R x Hroots HR.
  - exact HR.
  - intros z roots_z Hlookup Hzx.
    simpl in Hlookup.
    destruct (ident_eqb z y) eqn:Hzy.
    + inversion Hlookup; subst roots_z. exact Hroots.
    + eapply IH; eassumption.
Qed.

Lemma alpha_rename_params_root_env_add_params_roots_same_rename_equiv :
  forall rho used ps psr rho' used' roots rootsr R Rr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    root_env_no_shadow R ->
    root_env_lookup_params_none_b ps R = true ->
    params_names_nodup_b ps = true ->
    roots_exclude_params ps roots ->
    root_env_excludes_params ps R ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv rootsr (root_set_rename rho' roots) ->
    root_env_equiv
      (root_env_add_params_roots_same psr rootsr Rr)
      (root_env_rename rho'
        (root_env_add_params_roots_same ps roots R)).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used'
    roots rootsr R Rr Hrename HnsR Hfresh Hnodup Hexcl Henv HRr Hrootsr.
  - simpl in Hrename. inversion Hrename; subst.
    simpl. exact HRr.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hfresh, Hnodup, Hexcl, Henv.
    destruct (root_env_lookup x R) as [existing |] eqn:Hlookup;
      try discriminate.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    inversion Hexcl as [| ? ? Hexcl_x Hexcl_tail]; subst.
    inversion Henv as [| ? ? Henv_x Henv_tail]; subst.
    simpl. rewrite ident_eqb_refl.
    apply root_env_equiv_add.
    + exact Hrootsr.
    + assert (Hroots_tail :
        root_set_equiv rootsr (root_set_rename rho_tail roots)).
      { eapply root_set_shadow_safe_rename_body_equiv.
        - exact Hexcl_x.
        - exact Hrootsr. }
      assert (HR_tail :
        root_env_equiv
          (root_env_add_params_roots_same ps_tail rootsr Rr)
          (root_env_rename rho_tail
            (root_env_add_params_roots_same ps roots R))).
      { eapply IH; eassumption. }
      eapply root_env_equiv_trans.
      * exact HR_tail.
      * apply root_env_equiv_sym.
        apply root_env_rename_cons_root_env_excludes.
        -- eapply root_env_add_params_roots_same_no_shadow; eauto.
        -- apply root_env_lookup_add_params_roots_same_none.
           ++ exact Hlookup.
           ++ apply ident_in_b_false_not_in. apply negb_true_iff.
              exact Hnotin_b.
        -- apply root_env_excludes_add_params_roots_same.
           ++ exact Hexcl_x.
           ++ exact Henv_x.
Qed.

Lemma root_env_remove_shadow_safe_rename_body_ext_equiv :
  forall rho R Rr x xr,
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R) ->
    rename_no_collision_for ((x, xr) :: rho) x (root_env_names R) ->
    root_env_equiv Rr (root_env_rename ((x, xr) :: rho) R) ->
    root_env_equiv (root_env_remove xr Rr)
      (root_env_rename ((x, xr) :: rho) (root_env_remove x R)).
Proof.
  intros rho R Rr x xr Hns Hnsr Hnocoll Hnocoll_x Heq.
  rewrite (root_env_rename_remove ((x, xr) :: rho) R x).
  - replace (lookup_rename x ((x, xr) :: rho)) with xr
      by (simpl; rewrite ident_eqb_refl; reflexivity).
    eapply root_env_equiv_remove.
    + exact Hnsr.
    + apply root_env_rename_no_shadow.
      * exact Hns.
      * exact Hnocoll.
    + exact Heq.
  - exact Hnocoll_x.
Qed.

Lemma root_env_remove_shadow_safe_rename_body_equiv :
  forall rho R Rr x xr,
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_excludes x (root_env_remove x R) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R) ->
    rename_no_collision_for ((x, xr) :: rho) x (root_env_names R) ->
    root_env_equiv Rr (root_env_rename ((x, xr) :: rho) R) ->
    root_env_equiv (root_env_remove xr Rr)
      (root_env_rename rho (root_env_remove x R)).
Proof.
  intros rho R Rr x xr Hns Hnsr Hexcl Hnocoll Hnocoll_x Heq.
  assert (Hremove_ext :
    root_env_equiv (root_env_remove xr Rr)
      (root_env_rename ((x, xr) :: rho) (root_env_remove x R))).
  { eapply root_env_remove_shadow_safe_rename_body_ext_equiv; eassumption. }
  eapply root_env_equiv_trans.
  - exact Hremove_ext.
  - eapply root_env_rename_cons_root_env_excludes.
    + apply root_env_no_shadow_remove. exact Hns.
    + apply root_env_lookup_remove_eq_no_shadow. exact Hns.
    + exact Hexcl.
Qed.

Lemma roots_exclude_shadow_safe_rename_body :
  forall rho Σ Σr roots rootsr x xr,
    ctx_alpha rho Σ Σr ->
    root_set_sctx_roots_named roots Σ ->
    ~ In xr (ctx_names Σr) ->
    root_set_equiv rootsr (root_set_rename ((x, xr) :: rho) roots) ->
    roots_exclude x roots ->
    roots_exclude xr rootsr.
Proof.
  intros rho Σ Σr roots rootsr x xr Halpha Hroots Hfresh Heq Hexcl.
  eapply roots_exclude_equiv.
  - apply root_set_equiv_sym. exact Heq.
  - assert (Hlookup_x : lookup_rename x ((x, xr) :: rho) = xr)
      by (simpl; rewrite ident_eqb_refl; reflexivity).
    assert (Hexcl_ren :
      roots_exclude (lookup_rename x ((x, xr) :: rho))
        (root_set_rename ((x, xr) :: rho) roots)).
    { apply roots_exclude_rename.
      - intros y Hin Hyx.
        rewrite Hlookup_x.
        eapply root_set_sctx_roots_named_bound_no_collision;
          eassumption.
      - exact Hexcl. }
    rewrite Hlookup_x in Hexcl_ren. exact Hexcl_ren.
Qed.

Lemma root_env_excludes_shadow_safe_rename_body :
  forall rho Σ Σr R Rr x xr,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    ~ In xr (ctx_names Σr) ->
    root_env_equiv Rr (root_env_rename ((x, xr) :: rho) R) ->
    root_env_excludes x R ->
    root_env_excludes xr Rr.
Proof.
  intros rho Σ Σr R Rr x xr Halpha Hrn Hkeys Henv Hfresh Heq Hexcl.
  eapply root_env_excludes_equiv.
  - apply root_env_equiv_sym. exact Heq.
  - assert (Hlookup_x : lookup_rename x ((x, xr) :: rho) = xr)
      by (simpl; rewrite ident_eqb_refl; reflexivity).
    assert (Hexcl_ren :
      root_env_excludes (lookup_rename x ((x, xr) :: rho))
        (root_env_rename ((x, xr) :: rho) R)).
    { eapply root_env_excludes_rename.
      - exact Hrn.
      - intros y Hin Hyx.
        rewrite Hlookup_x.
        eapply root_env_sctx_keys_named_bound_no_collision;
          eassumption.
      - intros y roots z Hlookup Hyx Hin Hzx.
        rewrite Hlookup_x.
        eapply root_env_sctx_roots_named_bound_no_collision;
          eassumption.
      - exact Hexcl. }
    rewrite Hlookup_x in Hexcl_ren. exact Hexcl_ren.
Qed.

Lemma roots_exclude_params_named_absent :
  forall ps roots Σ,
    root_set_sctx_roots_named roots Σ ->
    (forall x, In x (ctx_names (params_ctx ps)) -> ~ In x (ctx_names Σ)) ->
    roots_exclude_params ps roots.
Proof.
  intros ps roots Σ Hnamed Habsent.
  change (Forall (fun x => roots_exclude x roots)
    (ctx_names (params_ctx ps))).
  rewrite Forall_forall.
  intros x Hin_params.
  unfold roots_exclude, root_set_sctx_roots_named in *.
  intros Hin_roots.
  apply (Habsent x Hin_params). apply Hnamed. exact Hin_roots.
Qed.

Lemma root_env_excludes_params_roots_named_absent :
  forall ps R Σ,
    root_env_sctx_roots_named R Σ ->
    (forall x, In x (ctx_names (params_ctx ps)) -> ~ In x (ctx_names Σ)) ->
    root_env_excludes_params ps R.
Proof.
  intros ps R Σ Hnamed Habsent.
  change (Forall (fun x => root_env_excludes x R)
    (ctx_names (params_ctx ps))).
  rewrite Forall_forall.
  intros x Hin_params.
  unfold root_env_excludes, roots_exclude, root_env_sctx_roots_named in *.
  intros y roots Hlookup Hyx Hin_roots.
  apply (Habsent x Hin_params). eapply Hnamed; eassumption.
Qed.

Lemma root_env_sctx_roots_named_add_env_named :
  forall R Σ x roots,
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    root_env_sctx_roots_named (root_env_add x roots R) Σ.
Proof.
  unfold root_env_sctx_roots_named.
  intros R Σ x roots Henv Hroots y roots_y z Hlookup Hin.
  simpl in Hlookup.
  destruct (ident_eqb y x).
  - inversion Hlookup; subst roots_y. apply Hroots. exact Hin.
  - eapply Henv; eassumption.
Qed.

Lemma root_env_sctx_roots_named_remove_env :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named (root_env_remove x R) Σ.
Proof.
  unfold root_env_sctx_roots_named.
  intros R Σ x Hnodup Henv y roots z Hlookup Hin.
  induction R as [| [w roots_w] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup. simpl in Hnodup.
  inversion Hnodup as [| ? ? Hw_notin Hnodup_tail]; subst.
  destruct (ident_eqb x w) eqn:Hxw.
  - apply ident_eqb_eq in Hxw. subst w.
    eapply Henv.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        exfalso. apply Hw_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup.
      * rewrite Hyx. exact Hlookup.
    + exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y w) eqn:Hyw.
    + eapply Henv.
      * simpl. rewrite Hyw. exact Hlookup.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Henv.
        -- simpl. destruct (ident_eqb y0 w) eqn:Hy0w.
           ++ apply ident_eqb_eq in Hy0w. subst y0.
              exfalso. apply Hw_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0w. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_sctx_roots_named_update_env_named :
  forall R Σ x roots,
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    root_env_sctx_roots_named (root_env_update x roots R) Σ.
Proof.
  unfold root_env_sctx_roots_named.
  intros R Σ x roots Hnodup Henv Hroots y roots_y z Hlookup Hin.
  induction R as [| [w roots_w] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup. simpl in Hnodup.
  inversion Hnodup as [| ? ? Hw_notin Hnodup_tail]; subst.
  destruct (ident_eqb x w) eqn:Hxw; simpl in Hlookup.
  - destruct (ident_eqb y w) eqn:Hyw.
    + inversion Hlookup; subst roots_y. apply Hroots. exact Hin.
    + eapply Henv.
      * simpl. rewrite Hyw. exact Hlookup.
      * exact Hin.
  - destruct (ident_eqb y w) eqn:Hyw.
    + inversion Hlookup; subst roots_y.
      eapply Henv.
      * simpl. rewrite Hyw. reflexivity.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Henv.
        -- simpl. destruct (ident_eqb y0 w) eqn:Hy0w.
           ++ apply ident_eqb_eq in Hy0w. subst y0.
              exfalso. apply Hw_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0w. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma ctx_names_remove_preserve_neq_sctx_roots_named :
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

Lemma root_set_sctx_roots_named_remove_ctx_excluding :
  forall roots Σ x,
    roots_exclude x roots ->
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named roots (sctx_remove x Σ).
Proof.
  unfold root_set_sctx_roots_named, roots_exclude.
  intros roots Σ x Hexclude Hnamed z Hin.
  apply ctx_names_remove_preserve_neq_sctx_roots_named.
  - intros Heq. subst z. apply Hexclude. exact Hin.
  - apply Hnamed. exact Hin.
Qed.

Lemma root_env_sctx_roots_named_remove_ctx_excluding :
  forall R Σ x,
    (forall y roots,
      root_env_lookup y R = Some roots ->
      roots_exclude x roots) ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R (sctx_remove x Σ).
Proof.
  unfold root_env_sctx_roots_named, roots_exclude.
  intros R Σ x Hexclude Hnamed y roots z Hlookup Hin.
  apply ctx_names_remove_preserve_neq_sctx_roots_named.
  - intros Heq. subst z. eapply Hexclude; eassumption.
  - eapply Hnamed; eassumption.
Qed.

Lemma sctx_lookup_in_ctx_names_sctx_roots_named :
  forall x Σ T st,
    sctx_lookup x Σ = Some (T, st) ->
    In x (ctx_names Σ).
Proof.
  unfold sctx_lookup.
  intros x Σ.
  induction Σ as [| [[[y Ty] sty] my] rest IH]; intros T st Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y. left. reflexivity.
  - right. eapply IH. exact Hlookup.
Qed.

Lemma typed_place_type_root_name_in_sctx_names :
  forall env Σ p T,
    typed_place_type_env_structural env Σ p T ->
    In (root_provenance_place_name p) (ctx_names Σ).
Proof.
  intros env Σ p T Htyped.
  induction Htyped; simpl.
  - eapply sctx_lookup_in_ctx_names_sctx_roots_named. exact H.
  - exact IHHtyped.
  - exact IHHtyped.
Qed.

Lemma alpha_root_provenance_place_name_place_root :
  forall p,
    root_provenance_place_name p = place_root p.
Proof.
  induction p; simpl; auto.
Qed.

Lemma typed_place_root_name_in_sctx_names :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    In (root_provenance_place_name p) (ctx_names Σ).
Proof.
  intros env Σ p T Htyped.
  induction Htyped; simpl.
  - eapply sctx_lookup_in_ctx_names_sctx_roots_named. exact H.
  - exact IHHtyped.
  - eapply typed_place_type_root_name_in_sctx_names. exact H.
  - eapply typed_place_type_root_name_in_sctx_names. exact H.
Qed.

Lemma root_of_place_sctx_roots_named :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    root_set_sctx_roots_named (root_of_place p) Σ.
Proof.
  intros env Σ p T Htyped.
  unfold root_of_place.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - apply root_set_sctx_roots_named_single.
    rewrite <- (place_path_root p x path Hpath).
    rewrite <- alpha_root_provenance_place_name_place_root.
    eapply typed_place_root_name_in_sctx_names. exact Htyped.
  - apply root_set_sctx_roots_named_single.
    eapply typed_place_root_name_in_sctx_names. exact Htyped.
Qed.

Lemma root_store_single_sctx_roots_named_of_place_path :
  forall env Σ p T x path,
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x, path) ->
    root_set_sctx_roots_named [RStore x] Σ.
Proof.
  intros env Σ p T x path Htyped Hpath.
  unfold root_set_sctx_roots_named.
  intros z Hin.
  simpl in Hin. destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin. subst z.
  rewrite <- (place_path_root p x path Hpath).
  rewrite <- alpha_root_provenance_place_name_place_root.
  eapply typed_place_root_name_in_sctx_names. exact Htyped.
Qed.

Lemma root_env_sctx_roots_named_add_binding :
  forall R Σ x T m roots,
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    root_env_sctx_roots_named (root_env_add x roots R)
      (sctx_add x T m Σ).
Proof.
  intros R Σ x T m roots Henv Hroots.
  unfold root_env_sctx_roots_named in *.
  intros y roots_y z Hlookup Hin.
  simpl in Hlookup.
  destruct (ident_eqb y x).
  - inversion Hlookup; subst roots_y.
    simpl. right. apply Hroots. exact Hin.
  - simpl. right. eapply Henv; eassumption.
Qed.

Lemma root_set_sctx_roots_named_add_params :
  forall roots ps Σ,
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named roots (sctx_add_params ps Σ).
Proof.
  unfold root_set_sctx_roots_named, sctx_add_params, ctx_add_params.
  intros roots ps Σ Hroots z Hin.
  rewrite ctx_names_app.
  apply in_or_app. right.
  apply Hroots. exact Hin.
Qed.

Lemma root_env_sctx_roots_named_add_params_roots_same :
  forall ps roots R Σ,
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    root_env_sctx_roots_named
      (root_env_add_params_roots_same ps roots R)
      (sctx_add_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros roots R Σ Henv Hroots.
  - simpl. exact Henv.
  - simpl.
    change (root_env_sctx_roots_named
      (root_env_add x roots (root_env_add_params_roots_same ps roots R))
      (sctx_add x T m (sctx_add_params ps Σ))).
    apply root_env_sctx_roots_named_add_binding.
    + apply IH.
      * exact Henv.
      * exact Hroots.
    + apply root_set_sctx_roots_named_add_params. exact Hroots.
Qed.

Lemma root_env_sctx_keys_named_add_binding :
  forall R Σ x T m roots,
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named (root_env_add x roots R)
      (sctx_add x T m Σ).
Proof.
  intros R Σ x T m roots Hkeys.
  unfold root_env_sctx_keys_named.
  apply root_env_keys_named_add.
  - simpl. left. reflexivity.
  - eapply root_env_keys_named_weaken.
    + exact Hkeys.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_sctx_keys_named_add_params_roots_same :
  forall ps roots R Σ,
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named
      (root_env_add_params_roots_same ps roots R)
      (sctx_add_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros roots R Σ Hkeys.
  - simpl. exact Hkeys.
  - simpl.
    change (root_env_sctx_keys_named
      (root_env_add x roots (root_env_add_params_roots_same ps roots R))
      (sctx_add x T m (sctx_add_params ps Σ))).
    apply root_env_sctx_keys_named_add_binding.
    apply IH. exact Hkeys.
Qed.

Lemma alpha_rename_params_root_env_add_params_roots_same_no_collision_on :
  forall rho used ps psr rho' used' roots R Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_env_sctx_keys_named R Σ ->
    root_env_lookup_params_none_b ps R = true ->
    params_names_nodup_b ps = true ->
    ctx_lookup_params_none_b ps Σ = true ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho'
      (root_env_names (root_env_add_params_roots_same ps roots R)).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used' roots R
    Σ Σr Hrename Hctx Hkeys Hroot_none Hnodup Hctx_none Hctx_used
    Hrange_used Hnocoll.
  - simpl in Hrename. inversion Hrename; subst.
    simpl. exact Hnocoll.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hroot_none, Hnodup, Hctx_none.
    destruct (root_env_lookup x R) as [roots_x |] eqn:Hlookup_x;
      try discriminate.
    destruct (ctx_lookup_state x Σ) as [[Tx st] |] eqn:Hctx_lookup;
      try discriminate.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    set (used1 := fresh_ident x used :: used).
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ) (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy. }
    assert (Hkeys_tail :
      root_env_sctx_keys_named
        (root_env_add_params_roots_same ps roots R)
        (sctx_add_params ps Σ)).
    { apply root_env_sctx_keys_named_add_params_roots_same. exact Hkeys. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    assert (Hnocoll_tail :
      rename_no_collision_on rho_tail
        (root_env_names (root_env_add_params_roots_same ps roots R))).
    { eapply IH.
      - exact Htail.
      - exact Hctx.
      - exact Hkeys.
      - exact Hroot_none.
      - exact Hnodup_tail.
      - exact Hctx_none.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy.
      - exact Hnocoll. }
    eapply root_env_add_shadow_safe_rename_no_collision_on
      with (Σ := sctx_add_params ps Σ)
           (Σr := sctx_add_params ps_tail Σr).
    + exact Hctx_tail.
    + apply root_env_lookup_add_params_roots_same_none.
      * exact Hlookup_x.
      * apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnotin_b.
    + exact Hkeys_tail.
    + exact Hfresh_tail.
    + exact Hnocoll_tail.
Qed.

Lemma root_env_remove_excludes_roots_exclude_sctx :
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

Lemma root_env_sctx_roots_named_remove_binding :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_excludes x (root_env_remove x R) ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named (root_env_remove x R) (sctx_remove x Σ).
Proof.
  intros R Σ x Hrn Hexcl Henv.
  apply root_env_sctx_roots_named_remove_ctx_excluding.
  - intros y roots Hlookup.
    eapply root_env_remove_excludes_roots_exclude_sctx; eassumption.
  - apply root_env_sctx_roots_named_remove_env; assumption.
Qed.

Lemma root_env_remove_preserve_lookup_none :
  forall R x y,
    root_env_lookup y R = None ->
    root_env_lookup y (root_env_remove x R) = None.
Proof.
  intros R x y Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - apply ident_eqb_eq in Hyx. subst y.
    induction R as [| [z roots] rest IH]; simpl; try reflexivity.
    destruct (ident_eqb x z) eqn:Hxz.
    + simpl in Hlookup. rewrite Hxz in Hlookup.
      discriminate.
    + simpl in Hlookup. rewrite Hxz in Hlookup.
      simpl. rewrite Hxz. apply IH. exact Hlookup.
  - apply ident_eqb_neq in Hyx.
    rewrite root_env_lookup_remove_neq by exact Hyx.
    exact Hlookup.
Qed.

Lemma root_env_remove_match_params_preserve_lookup_none :
  forall ps R x,
    root_env_lookup x R = None ->
    root_env_lookup x (root_env_remove_match_params ps R) = None.
Proof.
  induction ps as [| p ps IH]; intros R x Hlookup; simpl.
  - exact Hlookup.
  - apply IH. apply root_env_remove_preserve_lookup_none. exact Hlookup.
Qed.

Lemma root_env_remove_match_params_lookup_param_none :
  forall ps R x,
    root_env_no_shadow R ->
    In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_remove_match_params ps R) = None.
Proof.
  induction ps as [| [m y T] ps IH]; intros R x Hrn Hin; simpl in Hin.
  - contradiction.
  - simpl.
    destruct Hin as [Heq | Hin].
    + subst x.
      apply root_env_remove_match_params_preserve_lookup_none.
      apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
    + apply IH.
      * apply root_env_no_shadow_remove. exact Hrn.
      * exact Hin.
Qed.

Lemma root_env_lookup_params_none_b_remove_match_params :
  forall ps R,
    root_env_no_shadow R ->
    root_env_lookup_params_none_b ps
      (root_env_remove_match_params ps R) = true.
Proof.
  induction ps as [| [m x T] ps IH]; intros R Hrn; simpl.
  - reflexivity.
  - rewrite root_env_remove_match_params_preserve_lookup_none.
    + apply IH. apply root_env_no_shadow_remove. exact Hrn.
    + apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
Qed.

Lemma root_env_sctx_roots_named_remove_match_params :
  forall ps R Σ,
    root_env_no_shadow R ->
    root_env_excludes_params ps (root_env_remove_match_params ps R) ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named
      (root_env_remove_match_params ps R)
      (sctx_remove_params ps Σ).
Proof.
  intros ps R Σ Hrn Hexcl Henv.
  assert (Henv_removed :
    root_env_sctx_roots_named (root_env_remove_match_params ps R) Σ).
  { clear Hexcl. revert R Hrn Henv.
    induction ps as [| [m x T] ps IH]; intros R Hrn Henv0; simpl.
    - exact Henv0.
    - apply IH.
      + apply root_env_no_shadow_remove. exact Hrn.
      + apply root_env_sctx_roots_named_remove_env; assumption. }
  assert (Hremoved_lookup_none :
    forall x, In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x (root_env_remove_match_params ps R) = None).
  { intros x Hin. eapply root_env_remove_match_params_lookup_param_none;
      eassumption. }
  clear Henv Hrn.
  remember (root_env_remove_match_params ps R) as Rremoved.
  clear HeqRremoved R.
  revert Σ Henv_removed Hexcl Hremoved_lookup_none.
  induction ps as [| [m x T] ps IH]; intros Σ Henv_removed Hexcl
    Hremoved_lookup_none; simpl in *.
  - exact Henv_removed.
  - inversion Hexcl as [| ? ? Hhead Htail]; subst.
    apply IH.
    + eapply root_env_sctx_roots_named_remove_ctx_excluding.
      * intros y roots Hlookup.
        destruct (ident_eqb y x) eqn:Hyx.
        -- apply ident_eqb_eq in Hyx. subst y.
           specialize (Hremoved_lookup_none x (or_introl eq_refl)).
           rewrite Hlookup in Hremoved_lookup_none. discriminate.
        -- apply ident_eqb_neq in Hyx.
           eapply Hhead; eassumption.
      * exact Henv_removed.
    + exact Htail.
    + intros y Hy.
      apply Hremoved_lookup_none. right. exact Hy.
Qed.

Lemma root_env_sctx_keys_named_remove_binding :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named (root_env_remove x R) (sctx_remove x Σ).
Proof.
  unfold root_env_sctx_keys_named.
  intros R Σ x Hrn Hkeys.
  induction R as [| [z roots] rest IH]; intros y Hin; simpl in *;
    try contradiction.
  unfold root_env_no_shadow in Hrn. simpl in Hrn.
  inversion Hrn as [| ? ? Hz_notin Hrn_tail]; subst.
  destruct (ident_eqb x z) eqn:Hxz.
  - apply ident_eqb_eq in Hxz. subst z.
    apply ctx_names_remove_preserve_neq_sctx_roots_named.
    + intros Heq. subst y. contradiction.
    + apply Hkeys. right. exact Hin.
  - simpl in Hin.
    destruct Hin as [Hy | Hin].
    + subst y.
      apply ctx_names_remove_preserve_neq_sctx_roots_named.
      * intros Heq. subst z. rewrite ident_eqb_refl in Hxz. discriminate.
      * apply Hkeys. left. reflexivity.
    + apply IH.
      * exact Hrn_tail.
      * intros w Hw. apply Hkeys. right. exact Hw.
      * exact Hin.
Qed.

Lemma root_env_sctx_keys_named_remove_match_params :
  forall ps R Σ,
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named
      (root_env_remove_match_params ps R)
      (sctx_remove_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros R Σ Hrn Hkeys.
  - simpl. exact Hkeys.
  - simpl.
    apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + apply root_env_sctx_keys_named_remove_binding; assumption.
Qed.

Lemma root_env_sctx_keys_named_remove_fresh_not_in :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    ~ In x (root_env_names (root_env_remove x R)).
Proof.
  intros R Σ x Hrn _.
  eapply root_env_lookup_none_not_in_names.
  apply root_env_lookup_remove_eq_no_shadow.
  exact Hrn.
Qed.

Lemma root_set_sctx_roots_named_remove_binding :
  forall roots Σ x,
    roots_exclude x roots ->
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named roots (sctx_remove x Σ).
Proof.
  intros roots Σ x Hexcl Hroots.
  apply root_set_sctx_roots_named_remove_ctx_excluding; assumption.
Qed.

Lemma root_set_sctx_roots_named_remove_match_params :
  forall ps roots Σ,
    roots_exclude_params ps roots ->
    root_set_sctx_roots_named roots Σ ->
    root_set_sctx_roots_named roots (sctx_remove_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros roots Σ Hexcl Hroots.
  - simpl. exact Hroots.
  - simpl in *.
    inversion Hexcl as [| ? ? Hhead Htail]; subst.
    apply IH.
    + exact Htail.
    + apply root_set_sctx_roots_named_remove_binding; assumption.
Qed.

Lemma root_set_sctx_roots_named_strip_added_same_bindings :
  forall roots Σ Σ2 x T m,
    roots_exclude x roots ->
    root_set_sctx_roots_named roots Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    root_set_sctx_roots_named roots Σ.
Proof.
  intros roots Σ Σ2 x T m Hexcl Hroots Hsame.
  eapply root_set_sctx_roots_named_same_bindings.
  - apply sctx_same_bindings_sym.
    eapply sctx_same_bindings_remove_added.
    + apply sctx_same_bindings_refl.
    + exact Hsame.
  - apply root_set_sctx_roots_named_remove_binding; assumption.
Qed.

Lemma alpha_rename_params_roots_exclude_params_rename :
  forall rho used ps psr rho' used' roots rootsr Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_set_sctx_roots_named roots (sctx_add_params ps Σ) ->
    roots_exclude_params ps roots ->
    root_set_equiv rootsr (root_set_rename rho' roots) ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    roots_exclude_params psr rootsr.
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used'
    roots rootsr Σ Σr Hrename Hctx Hroots_named Hexcl Hrootsr
    Hctx_used Hrange_used.
  - simpl in Hrename. inversion Hrename; subst.
    simpl. constructor.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hexcl.
    inversion Hexcl as [| ? ? Hx_excl Htail_excl]; subst.
    assert (Hroots_tail_named :
      root_set_sctx_roots_named roots (sctx_add_params ps Σ)).
    { eapply root_set_sctx_roots_named_strip_added_same_bindings.
      - exact Hx_excl.
      - exact Hroots_named.
      - apply sctx_same_bindings_refl. }
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ)
        (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    constructor.
    + eapply roots_exclude_shadow_safe_rename_body.
      * exact Hctx_tail.
      * exact Hroots_tail_named.
      * exact Hfresh_tail.
      * exact Hrootsr.
      * exact Hx_excl.
    + eapply IH.
      * exact Htail.
      * exact Hctx.
      * exact Hroots_tail_named.
      * exact Htail_excl.
      * eapply root_set_shadow_safe_rename_body_equiv.
        -- exact Hx_excl.
        -- exact Hrootsr.
      * intros y Hy. right. apply Hctx_used. exact Hy.
      * intros y Hy. right. apply Hrange_used. exact Hy.
Qed.

Lemma root_env_sctx_roots_named_strip_added_same_bindings_lookup_none :
  forall R Σ Σ2 x T m,
    root_env_lookup x R = None ->
    root_env_excludes x R ->
    root_env_sctx_roots_named R Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    root_env_sctx_roots_named R Σ.
Proof.
  intros R Σ Σ2 x T m Hlookup_none Hexcl Hroots Hsame.
  eapply root_env_sctx_roots_named_same_bindings.
  - apply sctx_same_bindings_sym.
    eapply sctx_same_bindings_remove_added.
    + apply sctx_same_bindings_refl.
    + exact Hsame.
  - eapply root_env_sctx_roots_named_remove_ctx_excluding.
    + intros y roots Hlookup.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        rewrite Hlookup_none in Hlookup. discriminate.
      * apply ident_eqb_neq in Hyx.
        eapply Hexcl; eassumption.
    + exact Hroots.
Qed.

Lemma root_env_sctx_keys_named_strip_added_same_bindings_lookup_none :
  forall R Σ Σ2 x T m,
    root_env_lookup x R = None ->
    root_env_sctx_keys_named R Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    root_env_sctx_keys_named R Σ.
Proof.
  intros R Σ Σ2 x T m Hlookup_none Hkeys Hsame.
  eapply root_env_sctx_keys_named_same_bindings.
  - apply sctx_same_bindings_sym.
    eapply sctx_same_bindings_remove_added.
    + apply sctx_same_bindings_refl.
    + exact Hsame.
  - unfold root_env_sctx_keys_named in *.
    intros y Hy.
    apply ctx_names_remove_preserve_neq_sctx_roots_named.
    + intros Heq. subst y.
      eapply root_env_lookup_none_not_in_names; eassumption.
    + apply Hkeys. exact Hy.
Qed.

Lemma rename_no_collision_on_remove_weaken :
  forall rho R x,
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)).
Proof.
  intros rho R x Hnocoll.
  unfold rename_no_collision_on in *.
  intros y Hy.
  assert (HyR : In y (root_env_names R)).
  { eapply root_env_names_remove_subset. exact Hy. }
  unfold rename_no_collision_for in *.
  intros z Hz Hzy.
  apply (Hnocoll y HyR z).
  - eapply root_env_names_remove_subset. exact Hz.
  - exact Hzy.
Qed.

Lemma root_env_remove_lookup_rename_equiv :
  forall rho R Rr x,
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_equiv
      (root_env_remove (lookup_rename x rho) Rr)
      (root_env_rename rho (root_env_remove x R)).
Proof.
  intros rho R Rr x Hns Hnsr Hnocoll Hnocoll_x HR.
  rewrite root_env_rename_remove.
  - apply root_env_equiv_remove.
    + exact Hnsr.
    + apply root_env_rename_no_shadow; assumption.
    + exact HR.
  - exact Hnocoll_x.
Qed.

Lemma alpha_rename_params_root_env_remove_match_params_full_rename_equiv :
  forall rho used ps psr rho' used' rho_full R Rr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    params_names_nodup_b ps = true ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho_full R) ->
    rename_no_collision_on rho_full (root_env_names R) ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      rename_no_collision_for rho_full x (root_env_names R)) ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      lookup_rename x rho_full = lookup_rename x rho') ->
    root_env_equiv
      (root_env_remove_match_params psr Rr)
      (root_env_rename rho_full (root_env_remove_match_params ps R)).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used'
    rho_full R Rr Hrename Hnodup Hns Hnsr HR Hnocoll Hnocoll_params
    Hmap.
  - simpl in Hrename. inversion Hrename; subst. simpl. exact HR.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnodup.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    assert (Hmap_head :
      lookup_rename x rho_full = fresh_ident x used).
    { specialize (Hmap x (or_introl eq_refl)).
      simpl in Hmap. rewrite ident_eqb_refl in Hmap. exact Hmap. }
    assert (Hremove :
      root_env_equiv (root_env_remove (fresh_ident x used) Rr)
        (root_env_rename rho_full (root_env_remove x R))).
    { rewrite <- Hmap_head.
      eapply root_env_remove_lookup_rename_equiv; eauto.
      apply Hnocoll_params. left. reflexivity. }
    simpl.
    eapply IH.
    + exact Htail.
    + exact Hnodup_tail.
    + apply root_env_no_shadow_remove. exact Hns.
    + apply root_env_no_shadow_remove. exact Hnsr.
    + exact Hremove.
    + apply rename_no_collision_on_remove_weaken. exact Hnocoll.
    + intros y Hy.
      unfold rename_no_collision_for in *.
      intros z Hz Hzy.
      eapply Hnocoll_params.
      * right. exact Hy.
      * eapply root_env_names_remove_subset. exact Hz.
      * exact Hzy.
    + intros y Hy.
      assert (Hy_ne_x : y <> x).
      { intros Heq. subst y.
        apply negb_true_iff in Hnotin_b.
        apply ident_in_b_false_not_in in Hnotin_b.
        apply Hnotin_b.
        exact Hy. }
      specialize (Hmap y (or_intror Hy)).
      simpl in Hmap.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. contradiction.
      * exact Hmap.
Qed.

Lemma alpha_rename_params_root_env_excludes_params_rename :
  forall rho used ps psr rho' used' R Rr Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add_params ps Σ) ->
    root_env_sctx_roots_named R (sctx_add_params ps Σ) ->
    root_env_lookup_params_none_b ps R = true ->
    root_env_excludes_params ps R ->
    root_env_equiv Rr (root_env_rename rho' R) ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    root_env_excludes_params psr Rr.
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used'
    R Rr Σ Σr Hrename Hctx Hns Hkeys Hroots Hroot_none Hexcl HR
    Hctx_used Hrange_used.
  - simpl in Hrename. inversion Hrename; subst. constructor.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hroot_none.
    destruct (root_env_lookup x R) as [roots_x |] eqn:Hlookup_x;
      try discriminate.
    simpl in Hexcl.
    inversion Hexcl as [| ? ? Hx_excl Htail_excl]; subst.
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ)
        (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    assert (Hkeys_tail :
      root_env_sctx_keys_named R (sctx_add_params ps Σ)).
    { eapply root_env_sctx_keys_named_strip_added_same_bindings_lookup_none.
      - exact Hlookup_x.
      - exact Hkeys.
      - apply sctx_same_bindings_refl. }
    assert (Hroots_tail :
      root_env_sctx_roots_named R (sctx_add_params ps Σ)).
    { eapply root_env_sctx_roots_named_strip_added_same_bindings_lookup_none.
      - exact Hlookup_x.
      - exact Hx_excl.
      - exact Hroots.
      - apply sctx_same_bindings_refl. }
    assert (HR_tail :
      root_env_equiv Rr (root_env_rename rho_tail R)).
    { eapply root_env_equiv_trans.
      - exact HR.
      - eapply root_env_rename_cons_root_env_excludes.
        + exact Hns.
        + exact Hlookup_x.
        + exact Hx_excl. }
    constructor.
    + eapply root_env_excludes_shadow_safe_rename_body.
      * exact Hctx_tail.
      * exact Hns.
      * exact Hkeys_tail.
      * exact Hroots_tail.
      * exact Hfresh_tail.
      * exact HR.
      * exact Hx_excl.
    + eapply IH.
      * exact Htail.
      * exact Hctx.
      * exact Hns.
      * exact Hkeys_tail.
      * exact Hroots_tail.
      * exact Hroot_none.
      * exact Htail_excl.
      * exact HR_tail.
      * intros y Hy. right. apply Hctx_used. exact Hy.
      * intros y Hy. right. apply Hrange_used. exact Hy.
Qed.

Lemma root_env_sctx_roots_named_remove_strip_added_same_bindings :
  forall R Σ Σ2 x T m,
    root_env_no_shadow R ->
    root_env_excludes x (root_env_remove x R) ->
    root_env_sctx_roots_named R Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    root_env_sctx_roots_named (root_env_remove x R) Σ.
Proof.
  intros R Σ Σ2 x T m Hns Hexcl Hroots Hsame.
  eapply root_env_sctx_roots_named_same_bindings.
  - apply sctx_same_bindings_sym.
    eapply sctx_same_bindings_remove_added.
    + apply sctx_same_bindings_refl.
    + exact Hsame.
  - apply root_env_sctx_roots_named_remove_binding; assumption.
Qed.

Lemma root_env_sctx_keys_named_remove_strip_added_same_bindings :
  forall R Σ Σ2 x T m,
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    root_env_sctx_keys_named (root_env_remove x R) Σ.
Proof.
  intros R Σ Σ2 x T m Hns Hkeys Hsame.
  eapply root_env_sctx_keys_named_same_bindings.
  - apply sctx_same_bindings_sym.
    eapply sctx_same_bindings_remove_added.
    + apply sctx_same_bindings_refl.
    + exact Hsame.
  - apply root_env_sctx_keys_named_remove_binding; assumption.
Qed.

Lemma rename_no_collision_on_tail_remove :
  forall rho R x xr,
    root_env_no_shadow R ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho R x xr Hns Hnocoll y Hy z Hz Hzy Heq.
  assert (HyR : In y (root_env_names R)).
  { eapply root_env_names_remove_subset. exact Hy. }
  assert (HzR : In z (root_env_names R)).
  { eapply root_env_names_remove_subset. exact Hz. }
  assert (Hyx : y <> x).
  { intros Heq_yx. subst y.
    eapply root_env_lookup_none_not_in_names.
    - apply root_env_lookup_remove_eq_no_shadow. exact Hns.
    - exact Hy. }
  assert (Hzx : z <> x).
  { intros Heq_zx. subst z.
    eapply root_env_lookup_none_not_in_names.
    - apply root_env_lookup_remove_eq_no_shadow. exact Hns.
    - exact Hz. }
  apply (Hnocoll y HyR z HzR Hzy).
  simpl. destruct (ident_eqb y x) eqn:Hyeq.
  - apply ident_eqb_eq in Hyeq. contradiction.
  - destruct (ident_eqb z x) eqn:Hzeq.
    + apply ident_eqb_eq in Hzeq. contradiction.
    + exact Heq.
Qed.

Lemma root_env_sctx_roots_named_update_union :
  forall R Σ x roots_old roots_new,
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots_old Σ ->
    root_set_sctx_roots_named roots_new Σ ->
    root_env_sctx_roots_named
      (root_env_update x (root_set_union roots_old roots_new) R) Σ.
Proof.
  intros R Σ x roots_old roots_new Hrn Henv Hold Hnew.
  apply root_env_sctx_roots_named_update_env_named.
  - exact Hrn.
  - exact Henv.
  - apply root_set_sctx_roots_named_union; assumption.
Qed.

Lemma root_env_sctx_keys_named_update :
  forall R Σ x roots,
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named (root_env_update x roots R) Σ.
Proof.
  intros R Σ x roots Hkeys.
  unfold root_env_sctx_keys_named.
  apply root_env_keys_named_update.
  exact Hkeys.
Qed.

Lemma root_env_sctx_roots_named_update_union_restore_path :
  forall R Σ1 Σ2 x path roots_old roots_new,
    sctx_restore_path Σ1 x path = infer_ok Σ2 ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ1 ->
    root_set_sctx_roots_named roots_old Σ1 ->
    root_set_sctx_roots_named roots_new Σ1 ->
    root_env_sctx_roots_named
      (root_env_update x (root_set_union roots_old roots_new) R) Σ2.
Proof.
  intros R Σ1 Σ2 x path roots_old roots_new Hrestore Hrn Henv Hold Hnew.
  eapply root_env_sctx_roots_named_same_bindings.
  - eapply sctx_restore_path_same_bindings. exact Hrestore.
  - apply root_env_sctx_roots_named_update_union; assumption.
Qed.

Lemma root_env_lookup_result_sctx_roots_named_after_typed :
  forall env Ω n R Σ e_new T_new Σ1 R1 roots_new x roots_result,
    root_env_lookup x R = Some roots_result ->
    root_env_sctx_roots_named R Σ ->
    typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
    root_set_sctx_roots_named roots_result Σ1.
Proof.
  intros env Ω n R Σ e_new T_new Σ1 R1 roots_new x roots_result
    Hlookup Henv Htyped.
  eapply root_set_sctx_roots_named_same_bindings.
  - eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped.
  - eapply root_env_lookup_sctx_roots_named; eassumption.
Qed.

Lemma root_env_lookup_result_sctx_roots_named_after_typed_restore_path :
  forall env Ω n R Σ e_new T_new Σ1 Σ2 R1 roots_new x path
      roots_result,
    root_env_lookup x R = Some roots_result ->
    root_env_sctx_roots_named R Σ ->
    typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
    sctx_restore_path Σ1 x path = infer_ok Σ2 ->
    root_set_sctx_roots_named roots_result Σ2.
Proof.
  intros env Ω n R Σ e_new T_new Σ1 Σ2 R1 roots_new x path
    roots_result Hlookup Henv Htyped Hrestore.
  eapply root_set_sctx_roots_named_same_bindings.
  - eapply sctx_restore_path_same_bindings. exact Hrestore.
  - eapply root_env_lookup_result_sctx_roots_named_after_typed;
      eassumption.
Qed.

Lemma root_set_sctx_roots_named_ctx_merge_left :
  forall roots Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_sctx_roots_named roots Σ2 ->
    root_set_sctx_roots_named roots Σ4.
Proof.
  intros roots Σ2 Σ3 Σ4 Hmerge Hroots.
  eapply root_set_sctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
  - exact Hroots.
Qed.

Lemma root_env_sctx_roots_named_ctx_merge_left :
  forall R Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_env_sctx_roots_named R Σ2 ->
    root_env_sctx_roots_named R Σ4.
Proof.
  intros R Σ2 Σ3 Σ4 Hmerge Henv.
  eapply root_env_sctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
  - exact Henv.
Qed.

Lemma root_set_sctx_roots_named_ctx_merge_right :
  forall env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2
      e3 T3 Σ3 R3 roots3 Σ4,
    typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
    typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_sctx_roots_named roots3 Σ3 ->
    root_set_sctx_roots_named roots3 Σ4.
Proof.
  intros env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 e3 T3 Σ3 R3
    roots3 Σ4 Htyped2 Htyped3 Hmerge Hroots.
  eapply root_set_sctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_right.
    + eapply sctx_same_bindings_trans.
      * apply sctx_same_bindings_sym.
        eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural.
        eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      * eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural.
        eapply typed_env_roots_shadow_safe_roots. exact Htyped3.
    + exact Hmerge.
  - exact Hroots.
Qed.

Lemma root_set_sctx_roots_named_if_merge :
  forall env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2
      e3 T3 Σ3 R3 roots3 Σ4,
    typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
    typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_sctx_roots_named roots2 Σ2 ->
    root_set_sctx_roots_named roots3 Σ3 ->
    root_set_sctx_roots_named (root_set_union roots2 roots3) Σ4.
Proof.
  intros env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 e3 T3 Σ3 R3
    roots3 Σ4 Htyped2 Htyped3 Hmerge Hroots2 Hroots3.
  apply root_set_sctx_roots_named_union.
  - eapply root_set_sctx_roots_named_ctx_merge_left; eassumption.
  - eapply root_set_sctx_roots_named_ctx_merge_right.
    + exact Htyped2.
    + exact Htyped3.
    + exact Hmerge.
    + exact Hroots3.
Qed.

Lemma root_set_sctx_roots_named_typed_args_tail :
  forall env Ω n Σ1 R1 roots args ps Σ2 R2 roots_rest,
    typed_args_roots_shadow_safe env Ω n R1 Σ1 args ps Σ2 R2 roots_rest ->
    root_set_sctx_roots_named roots Σ1 ->
    root_set_sctx_roots_named roots Σ2.
Proof.
  intros env Ω n Σ1 R1 roots args ps Σ2 R2 roots_rest Htyped_args Hroots.
  eapply root_set_sctx_roots_named_same_bindings.
  - eapply typed_args_env_structural_same_bindings.
    eapply typed_args_roots_structural.
    eapply typed_args_roots_shadow_safe_roots. exact Htyped_args.
  - exact Hroots.
Qed.

Lemma root_set_sctx_roots_named_typed_fields_tail :
  forall env Ω n lts ty_args Σ1 R1 roots fields defs Σ2 R2 roots_rest,
    typed_fields_roots_shadow_safe env Ω n lts ty_args R1 Σ1 fields defs
      Σ2 R2 roots_rest ->
    root_set_sctx_roots_named roots Σ1 ->
    root_set_sctx_roots_named roots Σ2.
Proof.
  intros env Ω n lts ty_args Σ1 R1 roots fields defs Σ2 R2 roots_rest
    Htyped_fields Hroots.
  eapply root_set_sctx_roots_named_same_bindings.
  - eapply typed_fields_env_structural_same_bindings.
    eapply typed_fields_roots_structural.
    eapply typed_fields_roots_shadow_safe_roots. exact Htyped_fields.
  - exact Hroots.
Qed.

Theorem typed_roots_shadow_safe_sctx_keys_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    True).
Proof.
  intros env Ω n.
  apply typed_roots_shadow_safe_ind; intros; try assumption.
  - eapply root_env_sctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - eapply root_env_sctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_single_ih.
  - match goal with
    | Hscrut : typed_env_roots_shadow_safe env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHscrut : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ1,
      Hpayload : ?Rpayload = root_env_add_params_roots_same ?ps ?roots_scrut ?R1,
      Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
        (sctx_add_params ?ps ?Σ1) _ _ ?Σhead_payload ?Rhead_payload _,
      IHhead : root_env_no_shadow ?Rpayload ->
        root_env_sctx_keys_named ?Rpayload (sctx_add_params ?ps ?Σ1) ->
        root_env_sctx_keys_named ?Rhead_payload ?Σhead_payload,
      Hout : ?Rout = root_env_remove_match_params ?ps ?Rhead_payload,
      HΣhead : ?Σhead = sctx_remove_params ?ps ?Σhead_payload,
      Hmerge : ctx_merge_many (ctx_of_sctx ?Σhead) (map ctx_of_sctx ?tail) =
        Some ?Γout,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHscrut Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Hscrut
              | exact Hrn]);
        assert (Hkeys_payload :
          root_env_sctx_keys_named Rpayload (sctx_add_params ps Σ1))
          by (subst Rpayload;
              apply root_env_sctx_keys_named_add_params_roots_same;
              exact Hkeys1);
        assert (Hrn_payload : root_env_no_shadow Rpayload)
          by (subst Rpayload;
              eapply root_env_add_params_roots_same_no_shadow; eauto);
        pose proof (IHhead Hrn_payload Hkeys_payload) as Hkeys_head_payload;
        assert (Hrn_head_payload : root_env_no_shadow Rhead_payload)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Hhead
              | exact Hrn_payload]);
        assert (Hkeys_head :
          root_env_sctx_keys_named Rout Σhead)
          by (subst Rout Σhead;
              apply root_env_sctx_keys_named_remove_match_params;
              assumption);
        eapply root_env_sctx_keys_named_same_bindings;
        [ eapply ctx_merge_many_same_bindings_left; exact Hmerge
        | exact Hkeys_head ]
    end.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    apply root_env_sctx_keys_named_remove_binding; assumption.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    apply root_env_sctx_keys_named_remove_binding; assumption.
  - solve_sctx_keys_single_ih.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ',
      Hrestore : sctx_restore_path ?Σ1 ?x ?path = infer_ok ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        apply root_env_sctx_keys_named_update;
        eapply root_env_sctx_keys_named_same_bindings;
        [ eapply sctx_restore_path_same_bindings; exact Hrestore
        | exact (IH Hrn Henv) ]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        apply root_env_sctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - repeat match goal with
    | Hstep : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        let Hkeys' := fresh "Hkeys_step" in
        let Hrn' := fresh "Hrn_step" in
        pose proof (Hstep Hrn Hkeys) as Hkeys';
        assert (Hrn' : root_env_no_shadow R')
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption
              | exact Hrn]);
        clear Hstep
    end.
    eapply root_env_sctx_keys_named_same_bindings.
    + eapply ctx_merge_same_bindings_left. eassumption.
    + eassumption.
  - solve_sctx_keys_callee_args.
  - match goal with
    | Hfield : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ1,
      Hrest : root_env_no_shadow ?R1 ->
        root_env_sctx_keys_named ?R1 ?Σ1 ->
        root_env_sctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hfield Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption
              | exact Hrn]);
        exact (Hrest Hrn1 Hkeys1)
    end.
  - exact I.
  - exact I.
Qed.

Theorem typed_roots_shadow_safe_sctx_roots_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ' /\
    root_set_sctx_roots_named roots Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ' /\
    Forall (fun roots => root_set_sctx_roots_named roots Σ') roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ' /\
    root_set_sctx_roots_named roots Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots_scrut Σ ->
    Forall (fun roots => root_set_sctx_roots_named roots Σ) rootss).
Proof.
  intros env Ω n.
  apply typed_roots_shadow_safe_ind; intros; try solve
    [ split; try assumption; apply root_set_sctx_roots_named_nil ].
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split.
    + eapply root_env_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_set_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split.
    + eapply root_env_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_set_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * eapply root_env_lookup_sctx_roots_named; eassumption.
  - solve_sctx_roots_args_union.
  - solve_sctx_roots_args_union.
  - solve_sctx_roots_args_union.
  - (* TERS_CallExpr_Fn: callee roots_callee in Σ1, arg_roots in Σ', need both in Σ' *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_Closure: same pattern as Fn *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_TypeForall: same pattern as Fn/Closure *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_MixedForall: same pattern as Fn/Closure/TypeForall *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_Forall_Fn: same pattern as Fn/Closure/TypeForall *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_Forall_Closure: same pattern as Forall_Fn *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - solve_sctx_roots_single_ih.
  - solve_sctx_roots_args_union.
	  - destruct (H H2 H3) as [Henv1 Hroots_scrut_named].
	    assert (Hrn1 : root_env_no_shadow R1)
	      by (eapply typed_env_roots_no_shadow;
	          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H2]).
	    assert (Henv_payload :
	      root_env_sctx_roots_named R_payload (sctx_add_params ps_head Σ1)).
	    { subst R_payload.
	      apply root_env_sctx_roots_named_add_params_roots_same; assumption. }
	    assert (Hrn_payload : root_env_no_shadow R_payload).
	    { subst R_payload.
	      eapply root_env_add_params_roots_same_no_shadow; eauto. }
	    destruct (H0 Hrn_payload Henv_payload) as
	      [Henv_head_payload Hroots_head_payload].
	    assert (Hrn_head_payload : root_env_no_shadow R_head_payload).
	    { eapply typed_env_roots_no_shadow.
	      - eapply typed_env_roots_shadow_safe_roots. exact t0.
	      - exact Hrn_payload. }
	    assert (Henv_head : root_env_sctx_roots_named R_out Σ_head).
	    { subst R_out Σ_head.
	      apply root_env_sctx_roots_named_remove_match_params; assumption. }
	    assert (Hroots_head : root_set_sctx_roots_named roots_head Σ_head).
	    { subst Σ_head.
	      apply root_set_sctx_roots_named_remove_match_params; assumption. }
	    pose proof (H1 Hrn1 Henv1 Hroots_scrut_named) as Hroots_tail.
	    assert (Hsame_head_final :
	      sctx_same_bindings Σ_head (sctx_of_ctx Γ_out)).
	    { eapply ctx_merge_many_same_bindings_left. exact e16. }
    assert (Hsame_1_head : sctx_same_bindings Σ1 Σ_head).
    { subst Σ_head.
      apply sctx_same_bindings_remove_added_params.
      eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact t0. }
    assert (Hsame_1_final :
      sctx_same_bindings Σ1 (sctx_of_ctx Γ_out)).
    { eapply sctx_same_bindings_trans; eassumption. }
    assert (Hroots_tail_final :
      Forall (fun roots => root_set_sctx_roots_named roots (sctx_of_ctx Γ_out))
        roots_tail).
    { eapply Forall_impl.
      - intros roots Hnamed.
        eapply root_set_sctx_roots_named_same_bindings.
        + exact Hsame_1_final.
        + exact Hnamed.
      - exact Hroots_tail. }
    split.
    + eapply root_env_sctx_roots_named_same_bindings.
      * exact Hsame_head_final.
      * exact Henv_head.
    + apply root_sets_sctx_roots_named_union.
      simpl. constructor.
      * eapply root_set_sctx_roots_named_same_bindings.
        -- exact Hsame_head_final.
        -- exact Hroots_head.
      * exact Hroots_tail_final.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Henv_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    split.
    + apply root_env_sctx_roots_named_remove_binding; assumption.
    + apply root_set_sctx_roots_named_remove_binding; assumption.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Henv_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    split.
    + apply root_env_sctx_roots_named_remove_binding; assumption.
    + apply root_set_sctx_roots_named_remove_binding; assumption.
  - destruct (H H0 H1) as [Henv Hroots].
    split; [exact Henv | apply root_set_sctx_roots_named_nil].
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]).
    assert (Hroots_old : root_set_sctx_roots_named roots_old Σ1)
      by (eapply root_env_lookup_sctx_roots_named; eassumption).
    split.
    + eapply root_env_sctx_roots_named_update_union_restore_path;
        eassumption.
    + eapply root_env_lookup_result_sctx_roots_named_after_typed_restore_path;
        eassumption.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]).
    assert (Hroots_old : root_set_sctx_roots_named roots_old Σ')
      by (eapply root_env_lookup_sctx_roots_named; eassumption).
    split.
    + eapply root_env_sctx_roots_named_update_union; eassumption.
    + apply root_set_sctx_roots_named_nil.
  - split; try assumption.
    eapply root_of_place_sctx_roots_named. eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_borrow_roots ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_borrow_roots_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply root_store_single_sctx_roots_named_of_place_path; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_borrow_roots ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_borrow_roots_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_root_lookup ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_root_lookup ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - match goal with
    | IHcond : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\
        root_set_sctx_roots_named ?roots_cond ?Σ1,
      IHthen : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R2 ?Σ2 /\
        root_set_sctx_roots_named ?roots2 ?Σ2,
      IHelse : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R3 ?Σ3 /\
        root_set_sctx_roots_named ?roots3 ?Σ3,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcond Hrn Henv) as [Henv1 _];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption | exact Hrn]);
        destruct (IHthen Hrn1 Henv1) as [Henv2 Hroots2];
        destruct (IHelse Hrn1 Henv1) as [_ Hroots3];
        split;
        [ eapply root_env_sctx_roots_named_ctx_merge_left; eassumption
        | eapply root_set_sctx_roots_named_if_merge; eassumption ]
    end.
  - split; try assumption. constructor.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\
        root_set_sctx_roots_named ?roots ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ2)
          ?roots_rest,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_rest];
        split; [exact Henv2 | constructor; [| exact Hroots_rest]];
        eapply root_set_sctx_roots_named_typed_args_tail; eassumption
    end.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\
        root_set_sctx_roots_named ?roots_field ?Σ1,
      IHfields : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R2 ?Σ2 /\
        root_set_sctx_roots_named ?roots_rest ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption | exact Hrn]);
        destruct (IHfields Hrn1 Henv1) as [Henv2 Hroots_rest];
        split;
        [ exact Henv2
        | apply root_set_sctx_roots_named_union; [| exact Hroots_rest] ];
        eapply root_set_sctx_roots_named_typed_fields_tail; eassumption
    end.
  - constructor.
  - match goal with
    | Htyped : typed_env_roots_shadow_safe env Ω n ?Rpayload
        (sctx_add_params ?ps ?Σ) _ _ ?Σv_payload ?Rv_payload ?roots,
      IHtyped : root_env_no_shadow ?Rpayload ->
        root_env_sctx_roots_named ?Rpayload (sctx_add_params ?ps ?Σ) ->
        root_env_sctx_roots_named ?Rv_payload ?Σv_payload /\
        root_set_sctx_roots_named ?roots ?Σv_payload,
      IHtail : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_set_sctx_roots_named ?roots_scrut ?Σ ->
        Forall (fun roots0 => root_set_sctx_roots_named roots0 ?Σ) ?rootss,
      HRpayload : ?Rpayload = root_env_add_params_roots_same ?ps ?roots_scrut ?R,
      HΣv : ?Σv = sctx_remove_params ?ps ?Σv_payload,
      Hroots_excl : roots_exclude_params ?ps ?roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ,
      Hroots_scrut : root_set_sctx_roots_named ?roots_scrut ?Σ |- _ =>
        assert (Henv_payload :
          root_env_sctx_roots_named Rpayload (sctx_add_params ps Σ))
          by (subst Rpayload;
              apply root_env_sctx_roots_named_add_params_roots_same;
              assumption);
        assert (Hrn_payload : root_env_no_shadow Rpayload)
          by (subst Rpayload;
              eapply root_env_add_params_roots_same_no_shadow; eauto);
        destruct (IHtyped Hrn_payload Henv_payload) as [_ Hroots_payload];
        assert (Hsame_payload :
          sctx_same_bindings (sctx_add_params ps Σ) Σv_payload)
          by (eapply typed_env_structural_same_bindings;
              eapply typed_env_roots_structural;
              eapply typed_env_roots_shadow_safe_roots; exact Htyped);
        assert (Hsame_branch : sctx_same_bindings Σ Σv)
          by (subst Σv;
              apply sctx_same_bindings_remove_added_params;
              exact Hsame_payload);
        pose proof (IHtail Hrn Henv Hroots_scrut) as Hroots_tail;
        constructor; [| exact Hroots_tail];
        eapply root_set_sctx_roots_named_same_bindings;
        [ apply sctx_same_bindings_sym; exact Hsame_branch
        | subst Σv;
          apply root_set_sctx_roots_named_remove_match_params; assumption ]
    end.
Qed.

Lemma alpha_rename_typed_env_roots_trivial_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    (e = EUnit \/ exists l, e = ELit l) ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hshape Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  destruct Hshape as [Heq | [l Heq]]; subst e.
  - simpl in Hrename. injection Hrename as <- <-.
    inversion Htyped; subst.
    exists Σr, Rr, []. repeat split;
      try solve [apply TER_Unit | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
  - simpl in Hrename. injection Hrename as <- <-.
    destruct l; inversion Htyped; subst;
      exists Σr, Rr, []; repeat split;
      try solve [constructor | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
Qed.

Lemma alpha_rename_typed_env_roots_fn_forward :
  forall env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EFn fname) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EFn fname)) (rename_range rho) ->
    alpha_rename_expr rho used (EFn fname) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots
    Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  inversion Htyped; subst.
  exists Σr, Rr, [].
  split; [| split; [| split; [| split]]].
  - eapply TER_Fn; eauto.
  - exact Hctx.
  - exact HnsRr.
  - exact HRr.
  - apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_trivial_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    (e = EUnit \/ exists l, e = ELit l) ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hshape Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  destruct Hshape as [Heq | [l Heq]]; subst e.
  - simpl in Hrename. injection Hrename as <- <-.
    inversion Htyped; subst.
    exists Σr, Rr, []. repeat split;
      try solve [apply TERS_Unit | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
  - simpl in Hrename. injection Hrename as <- <-.
    destruct l; inversion Htyped; subst;
      exists Σr, Rr, []; repeat split;
      try solve [constructor | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
Qed.

Lemma alpha_rename_typed_env_roots_fn_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EFn fname) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EFn fname)) (rename_range rho) ->
    alpha_rename_expr rho used (EFn fname) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots
    Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  inversion Htyped; subst.
  exists Σr, Rr, [].
  split; [| split; [| split; [| split]]].
  - eapply TERS_Fn; eauto.
  - exact Hctx.
  - exact HnsRr.
  - exact HRr.
  - apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_drop_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots env Ω n R Σ (EDrop e) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EDrop e)) (rename_range rho) ->
    alpha_rename_expr rho used (EDrop e) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (alpha_rename_expr rho used e) as [er0 used1] eqn:Hrename_e.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (Hexpr R Rr Σ Σr used er0 used1 T0 Σ' R' roots0)
    as [Σr' [Rr' [rootsr
      [Htyped_r [Hctx_r [HnsRr' [HRr' _]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e T0 Σ' R' roots0 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename_e.
  - exists Σr', Rr', [].
    split; [| split; [| split; [| split]]].
    + eapply TER_Drop. exact Htyped_r.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_drop_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EDrop e) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EDrop e)) (rename_range rho) ->
    alpha_rename_expr rho used (EDrop e) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (alpha_rename_expr rho used e) as [er0 used1] eqn:Hrename_e.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (Hexpr R Rr Σ Σr used er0 used1 T0 Σ' R' roots0)
    as [Σr' [Rr' [rootsr
      [Htyped_r [Hctx_r [HnsRr' [HRr' _]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e T0 Σ' R' roots0 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename_e.
  - exists Σr', Rr', [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Drop. exact Htyped_r.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_trivial_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    (e = EUnit \/ exists l, e = ELit l) ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hshape Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_trivial_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_fn_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EFn fname) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EFn fname)) (rename_range rho) ->
    alpha_rename_expr rho used (EFn fname) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_fn_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_drop_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EDrop e) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EDrop e)) (rename_range rho) ->
    alpha_rename_expr rho used (EDrop e) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (alpha_rename_expr rho used e) as [er0 used1] eqn:Hrename_e.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (Hexpr R Rr Σ Σr used er0 used1 T0 Σ' R' roots0)
    as [Σr' [Rr' [rootsr
      [Htyped_r [Hctx_r [HnsRr' [HRr' _]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e T0 Σ' R' roots0 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename_e.
  - exists Σr', Rr', [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Drop. exact Htyped_r.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_replace_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots env Ω n R Σ (EReplace p e_new) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EReplace p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EReplace p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ1 R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (ctx_alpha_restore_path_forward
      rho Σ1 Σr1 x path Σ' Hctx_new_r Hsafe_x
      ltac:(match goal with
        | H : sctx_restore_path Σ1 x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr2 [Hrestore_r Hctx_restore]].
    destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_result_r Hroots_result]].
    destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr2,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TER_Replace_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Hlookup_result_r.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
      * exact Hrestore_r.
    + exact Hctx_restore.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + exact Hroots_result.
Qed.

Lemma alpha_rename_typed_env_roots_assign_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots env Ω n R Σ (EAssign p e_new) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EAssign p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EAssign p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr1,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      [].
    split; [| split; [| split; [| split]]].
    + eapply TER_Assign_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T_old <> ULinear |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
    + exact Hctx_new_r.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_var_forward :
  forall env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EVar x) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (EVar x)) (rename_range rho) ->
    alpha_rename_expr rho used (EVar x) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TER_Var_Copy.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- apply Hdisj. simpl. left. reflexivity.
        -- match goal with
           | H : typed_place_env_structural env _ (PVar x) T |- _ =>
               exact H
           end.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe : ~ In x (rename_range rho)).
    { apply Hdisj. simpl. left. reflexivity. }
    destruct (ctx_alpha_consume_path_forward
      rho _ Σr x [] Σ' Hctx Hsafe
      ltac:(match goal with
        | H : sctx_consume_path _ x [] = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TER_Var_Move.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_place_forward :
  forall env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EPlace p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EPlace p)) (rename_range rho) ->
    alpha_rename_expr rho used (EPlace p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TER_Place_Copy.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    destruct (ctx_alpha_consume_path_forward
      rho Σ Σr x path Σ' Hctx Hsafe_x
      ltac:(match goal with
        | H : sctx_consume_path Σ x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TER_Place_Move.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_borrow_forward :
  forall env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EBorrow rk p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EBorrow rk p)) (rename_range rho) ->
    alpha_rename_expr rho used (EBorrow rk p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. destruct rk; injection Hrename as <- <-;
    inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    exists Σr, Rr, (root_of_place (rename_place rho p)). repeat split.
    + eapply TER_BorrowShared.
      eapply alpha_rename_typed_place_env_structural_forward; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + rewrite root_of_place_rename_place. simpl. tauto.
    + rewrite root_of_place_rename_place. simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TER_BorrowShared_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    exists Σr, Rr, [RStore (lookup_rename x rho)]. repeat split.
    + eapply TER_BorrowUnique.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply ctx_alpha_lookup_mut_forward; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + simpl. tauto.
    + simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TER_BorrowUnique_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
Qed.
Lemma root_env_names_remove_preserve_neq :
  forall x y R,
    x <> y ->
    In y (root_env_names R) ->
    In y (root_env_names (root_env_remove x R)).
Proof.
  intros x y R Hneq Hin.
  induction R as [| [z roots] rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hy | Hin].
    + subst z.
      destruct (ident_eqb x y) eqn:Hxy.
      * apply ident_eqb_eq in Hxy. contradiction.
      * simpl. left. reflexivity.
    + destruct (ident_eqb x z); simpl.
      * exact Hin.
      * right. apply IH. exact Hin.
Qed.

Lemma root_env_add_params_roots_same_preserve_name :
  forall ps roots R x,
    In x (root_env_names R) ->
    In x (root_env_names (root_env_add_params_roots_same ps roots R)).
Proof.
  induction ps as [| p ps IH]; intros roots R x Hin; simpl.
  - exact Hin.
  - right. apply IH. exact Hin.
Qed.

Lemma root_env_lookup_params_none_b_not_in :
  forall ps R x,
    root_env_lookup_params_none_b ps R = true ->
    In x (ctx_names (params_ctx ps)) ->
    ~ In x (root_env_names R).
Proof.
  induction ps as [| [m y T] ps IH]; intros R x Hfresh Hin; simpl in *.
  - contradiction.
  - destruct (root_env_lookup y R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct Hin as [Heq | Hin].
    + subst x.
      apply root_env_lookup_none_not_in_names. exact Hlookup.
    + eapply IH; eassumption.
Qed.

Lemma root_env_remove_match_params_preserve_name_not_params :
  forall ps R x,
    (forall y, In y (ctx_names (params_ctx ps)) -> x <> y) ->
    In x (root_env_names R) ->
    In x (root_env_names (root_env_remove_match_params ps R)).
Proof.
  induction ps as [| [m y T] ps IH]; intros R x Hnot Hin; simpl.
  - exact Hin.
  - apply IH.
    + intros z Hz. apply Hnot. right. exact Hz.
    + apply root_env_names_remove_preserve_neq.
      * intros Heq. apply (Hnot y); [left; reflexivity | symmetry; exact Heq].
      * exact Hin.
Qed.

Lemma root_env_remove_shadow_safe_rename_no_collision_on :
  forall rho Σ Σr R x xr T m,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add x T m Σ) ->
    ~ In xr (ctx_names Σr) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho Σ Σr R x xr T m Halpha Hns Hkeys Hfresh Hnocoll
    y Hy z Hz Hneq.
  destruct (ident_eqb y x) eqn:Hxy.
  - apply ident_eqb_eq in Hxy. subst y.
    simpl. rewrite ident_eqb_refl.
    destruct (ident_eqb z x) eqn:Hzx.
    + apply ident_eqb_eq in Hzx. subst z. contradiction.
    + assert (Hno :
        lookup_rename z ((x, xr) :: rho) <> xr).
      { eapply root_env_sctx_keys_named_added_bound_no_collision.
        - exact Halpha.
        - exact Hkeys.
        - exact Hfresh.
        - exact Hz.
        - intros Heq. subst z. rewrite ident_eqb_refl in Hzx.
          discriminate. }
      simpl in Hno. rewrite Hzx in Hno. exact Hno.
  - destruct (ident_eqb z x) eqn:Hzx.
    + apply ident_eqb_eq in Hzx. subst z.
      simpl. rewrite Hxy. rewrite ident_eqb_refl.
      assert (Hno : lookup_rename y ((x, xr) :: rho) <> xr).
      { eapply root_env_sctx_keys_named_added_bound_no_collision.
        - exact Halpha.
        - exact Hkeys.
        - exact Hfresh.
        - exact Hy.
        - intros Heq'. subst y. rewrite ident_eqb_refl in Hxy.
          discriminate. }
      simpl in Hno. rewrite Hxy in Hno.
      intros Heq. apply Hno. symmetry. exact Heq.
    + simpl. rewrite Hxy. rewrite Hzx.
      eapply Hnocoll.
      * eapply root_env_names_remove_preserve_neq.
        -- intros Heq. subst y. rewrite ident_eqb_refl in Hxy.
           discriminate.
        -- exact Hy.
      * eapply root_env_names_remove_preserve_neq.
        -- intros Heq. subst z. rewrite ident_eqb_refl in Hzx.
           discriminate.
        -- exact Hz.
      * exact Hneq.
Qed.

Lemma root_env_remove_shadow_safe_rename_no_collision_on_same_bindings :
  forall rho Σ Σ2 Σr R x xr T m,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    ~ In xr (ctx_names Σr) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R).
Proof.
  intros rho Σ Σ2 Σr R x xr T m Halpha Hns Hkeys Hsame Hfresh
    Hnocoll.
  eapply root_env_remove_shadow_safe_rename_no_collision_on.
  - exact Halpha.
  - exact Hns.
  - eapply root_env_sctx_keys_named_same_bindings.
    + apply sctx_same_bindings_sym. exact Hsame.
    + exact Hkeys.
  - exact Hfresh.
  - exact Hnocoll.
Qed.

Lemma alpha_rename_params_root_env_remove_match_params_no_collision_on :
  forall rho used ps psr rho' used' R Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add_params ps Σ) ->
    params_names_nodup_b ps = true ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    rename_no_collision_on rho
      (root_env_names (root_env_remove_match_params ps R)) ->
    rename_no_collision_on rho' (root_env_names R).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used' R
    Σ Σr Hrename Hctx Hns Hkeys Hnodup Hctx_used Hrange_used Hnocoll.
  - simpl in Hrename. inversion Hrename; subst.
    simpl in Hnocoll. exact Hnocoll.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnodup.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    set (R_tail := root_env_remove x R).
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ) (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    assert (Hkeys_tail :
      root_env_sctx_keys_named R_tail (sctx_add_params ps Σ)).
    { unfold R_tail.
      eapply root_env_sctx_keys_named_same_bindings.
      - apply sctx_same_bindings_sym.
        eapply sctx_same_bindings_remove_added.
        + apply sctx_same_bindings_refl.
        + apply sctx_same_bindings_refl.
      - apply root_env_sctx_keys_named_remove_binding.
        + exact Hns.
        + exact Hkeys. }
    assert (Hnocoll_tail :
      rename_no_collision_on rho_tail (root_env_names R_tail)).
    { unfold R_tail.
      eapply IH.
      - exact Htail.
      - exact Hctx.
      - apply root_env_no_shadow_remove. exact Hns.
      - exact Hkeys_tail.
      - exact Hnodup_tail.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy.
      - exact Hnocoll. }
    eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings
      with (Σ := sctx_add_params ps Σ)
           (Σ2 := sctx_add x T m (sctx_add_params ps Σ))
           (Σr := sctx_add_params ps_tail Σr).
    + exact Hctx_tail.
    + exact Hns.
    + exact Hkeys.
    + apply sctx_same_bindings_refl.
    + exact Hfresh_tail.
    + exact Hnocoll_tail.
Qed.

Lemma rename_no_collision_on_weaken_names :
  forall rho names names',
    rename_no_collision_on rho names' ->
    (forall x, In x names -> In x names') ->
    rename_no_collision_on rho names.
Proof.
  unfold rename_no_collision_on.
  intros rho names names' Hnocoll Hsub x Hin.
  eapply rename_no_collision_for_weaken_names.
  - apply Hnocoll. apply Hsub. exact Hin.
  - exact Hsub.
Qed.

Lemma alpha_rename_params_rename_no_collision_for_params :
  forall rho used ps psr rho' used' R Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add_params ps Σ) ->
    params_names_nodup_b ps = true ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    rename_no_collision_on rho' (root_env_names R) ->
    forall x,
      In x (ctx_names (params_ctx ps)) ->
      rename_no_collision_for rho' x (root_env_names R).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used'
    R Σ Σr Hrename Hctx Hns Hkeys Hnodup Hctx_used Hrange_used Hnocoll_result
    y Hy.
  - simpl in Hy. contradiction.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnodup, Hy.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ)
        (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros z Hz. right. apply Hctx_used. exact Hz.
      - intros z Hz. right. apply Hrange_used. exact Hz. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    destruct Hy as [Hy | Hy].
    + subst y.
      eapply root_env_sctx_keys_named_added_no_collision_for_head.
      * exact Hctx_tail.
      * exact Hkeys.
      * exact Hfresh_tail.
    + unfold rename_no_collision_for.
      intros z Hz Hzy.
      simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        apply negb_true_iff in Hnotin_b.
        apply ident_in_b_false_not_in in Hnotin_b.
        contradiction.
      * destruct (ident_eqb z x) eqn:Hzx.
        -- apply ident_eqb_eq in Hzx. subst z.
           intros Heq.
           assert (Hneq :
             lookup_rename y ((x, fresh_ident x used) :: rho_tail) <>
             fresh_ident x used).
           { eapply ctx_alpha_bound_no_collision_for.
             - exact Hctx_tail.
             - exact Hfresh_tail.
             - unfold sctx_add_params, ctx_add_params.
               rewrite ctx_names_app. apply in_or_app. left. exact Hy.
             - intros Heq_yx. subst y.
               apply negb_true_iff in Hnotin_b.
               apply ident_in_b_false_not_in in Hnotin_b.
               contradiction. }
           apply Hneq. simpl. rewrite Hyx. symmetry. exact Heq.
        -- simpl.
           eapply (IH rho (fresh_ident x used :: used) ps_tail rho_tail
             used' (root_env_remove x R) Σ Σr).
           ++ exact Htail.
           ++ exact Hctx.
           ++ apply root_env_no_shadow_remove. exact Hns.
           ++ eapply root_env_sctx_keys_named_remove_strip_added_same_bindings.
              ** exact Hns.
              ** exact Hkeys.
              ** apply sctx_same_bindings_refl.
           ++ exact Hnodup_tail.
           ++ intros w Hw. right. apply Hctx_used. exact Hw.
           ++ intros w Hw. right. apply Hrange_used. exact Hw.
           ++ eapply rename_no_collision_on_tail_remove; eassumption.
           ++ exact Hy.
           ++ apply root_env_names_remove_preserve_neq.
              ** intros Heq_zx. subst z. rewrite ident_eqb_refl in Hzx.
                 discriminate.
              ** exact Hz.
           ++ exact Hzy.
Qed.

Lemma typed_roots_root_env_names_subset_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    forall x, In x (root_env_names R) -> In x (root_env_names R')) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    forall x, In x (root_env_names R) -> In x (root_env_names R')) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    forall x, In x (root_env_names R) -> In x (root_env_names R')) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    True).
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros; subst; try assumption.
  - eapply H. exact H0.
  - eapply H. exact H0.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H. exact H0.
  - eapply H. exact H0.
  - eapply H. exact H0.
  - eapply root_env_remove_match_params_preserve_name_not_params.
	    + intros y Hy Heq.
	      subst y.
		      match goal with
		      | Hnone : root_env_lookup_params_none_b _ _ = true |- _ =>
		          pose proof (root_env_lookup_params_none_b_not_in _ _ _ Hnone Hy)
		            as Hnot
		      end.
	      apply Hnot. eapply H. exact H2.
    + eapply H0.
      apply root_env_add_params_roots_same_preserve_name.
      eapply H. exact H2.
  - eapply root_env_names_remove_preserve_neq.
    + intros Heq. subst x0.
      eapply root_env_lookup_none_not_in_names; eauto.
    + eapply H0. simpl. right. eapply H. exact H1.
  - eapply root_env_names_remove_preserve_neq.
    + intros Heq. subst x0.
      eapply root_env_lookup_none_not_in_names; eauto.
    + eapply H0. simpl. right. eapply H. exact H1.
  - eapply H. exact H0.
  - rewrite root_env_names_update. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - rewrite root_env_names_update. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - eapply H0. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - eapply H0. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - eapply H0. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - exact I.
Qed.

Lemma typed_env_roots_root_env_names_subset :
  forall env Ω n R Σ e T Σ' R' roots x,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros env Ω n R Σ e T Σ' R' roots x Htyped Hin.
  exact (proj1 (typed_roots_root_env_names_subset_mutual env Ω n)
    R Σ e T Σ' R' roots Htyped x Hin).
Qed.

Lemma typed_env_roots_let_body_no_collision_from_removed :
  forall env Ω n rho x roots1 R1 Σ1 e2 T m T2 Σ2 R2 roots2,
    typed_env_roots env Ω n (root_env_add x roots1 R1)
      (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
    root_env_lookup x R1 = None ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
    rename_no_collision_on rho (root_env_names R1).
Proof.
  intros env Ω n rho x roots1 R1 Σ1 e2 T m T2 Σ2 R2 roots2
    Htyped Hlookup Hnocoll.
  eapply rename_no_collision_on_weaken_names.
  - exact Hnocoll.
  - intros y Hin.
    eapply root_env_names_remove_preserve_neq.
    + intros Heq. subst y.
      eapply root_env_lookup_none_not_in_names; eauto.
    + eapply typed_env_roots_root_env_names_subset.
      * exact Htyped.
      * simpl. right. exact Hin.
Qed.

Lemma typed_args_roots_root_env_names_subset :
  forall env Ω n R Σ args ps Σ' R' roots x,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros env Ω n R Σ args ps Σ' R' roots x Htyped Hin.
  exact (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))
    R Σ args ps Σ' R' roots Htyped x Hin).
Qed.

Lemma typed_fields_roots_root_env_names_subset :
  forall env Ω n lts args R Σ fields defs Σ' R' roots x,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots x Htyped Hin.
  exact (proj1 (proj2 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n)))
    lts args R Σ fields defs Σ' R' roots Htyped x Hin).
Qed.

Lemma alpha_rename_typed_env_roots_let_forward :
  forall env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x Tann m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr Tann m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        typed_env_roots env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr Tann m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots env Ω n R Σ (ELet m x Tann e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELet m x Tann e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELet m x Tann e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed; eauto. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr Tann m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Htyped2_r &
        Hctx2_r & HnsRr2 & HRremove & Hroots2 & Hexcl_roots_r &
        Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots env Ω n (root_env_add x roots1 R1)
          (sctx_add x Tann m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TER_Let.
        -- exact Htyped1_r.
        -- match goal with
        | H : ty_compatible_b Ω T1 Tann = true |- _ => exact H
        end.
        -- exact Hlookup_xr_none.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x Tann Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_letinfer_forward :
  forall env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr T1 m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        typed_env_roots env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr T1 m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots env Ω n R Σ (ELetInfer m x e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELetInfer m x e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed; eauto. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 T1 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Htyped2_r &
        Hctx2_r & HnsRr2 & HRremove & Hroots2 & Hexcl_roots_r &
        Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots env Ω n (root_env_add x roots1 R1)
          (sctx_add x T1 m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TER_LetInfer.
        -- exact Htyped1_r.
        -- exact Hlookup_xr_none.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x T1 Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_let_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x Tann m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr Tann m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr Tann m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELet m x Tann e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELet m x Tann e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELet m x Tann e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr Tann m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x Tann m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_Let.
        -- exact Htyped1_r.
        -- match goal with
        | H : ty_compatible_b Ω T1 Tann = true |- _ => exact H
        end.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x Tann Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_letinfer_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr T1 m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr T1 m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELetInfer m x e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELetInfer m x e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 T1 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x T1 m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_LetInfer.
        -- exact Htyped1_r.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x T1 Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_let_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x Tann m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      root_env_no_shadow R1r ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      rename_no_collision_on rho (root_env_names R1) ->
      rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      root_env_equiv R1r (root_env_rename rho R1) ->
      root_set_equiv roots1r (root_set_rename rho roots1) ->
      root_env_sctx_keys_named R1 Σ1 ->
      root_env_sctx_roots_named R1 Σ1 ->
      root_set_sctx_roots_named roots1 Σ1 ->
      (forall y, In y (ctx_names (sctx_add xr Tann m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr Tann m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELet m x Tann e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELet m x Tann e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELet m x Tann e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow;
      [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [Hroots_env1 _].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_env1. }
  assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [_ Hroots_set1].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_set1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr Tann m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x Tann m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact HnsRr1.
    + match goal with
      | H : root_env_lookup x R1 = None |- _ => exact H
      end.
    + match goal with
      | H : roots_exclude x roots1 |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x R1 |- _ => exact H
      end.
    + exact HnocollR1.
    + exact HnocollR'.
    + match goal with
      | H : roots_exclude x roots |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x (root_env_remove x R2) |- _ => exact H
      end.
    + exact HRr1.
    + exact Hroots1.
    + exact HkeysR1.
    + exact HrootsR1.
    + exact Hroots1_named.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_Let.
        -- exact Htyped1_r.
        -- match goal with
        | H : ty_compatible_b Ω T1 Tann = true |- _ => exact H
        end.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x Tann Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_letinfer_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      root_env_no_shadow R1r ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      rename_no_collision_on rho (root_env_names R1) ->
      rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      root_env_equiv R1r (root_env_rename rho R1) ->
      root_set_equiv roots1r (root_set_rename rho roots1) ->
      root_env_sctx_keys_named R1 Σ1 ->
      root_env_sctx_roots_named R1 Σ1 ->
      root_set_sctx_roots_named roots1 Σ1 ->
      (forall y, In y (ctx_names (sctx_add xr T1 m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr T1 m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELetInfer m x e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELetInfer m x e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow;
      [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [Hroots_env1 _].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_env1. }
  assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [_ Hroots_set1].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_set1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 T1 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x T1 m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact HnsRr1.
    + match goal with
      | H : root_env_lookup x R1 = None |- _ => exact H
      end.
    + match goal with
      | H : roots_exclude x roots1 |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x R1 |- _ => exact H
      end.
    + exact HnocollR1.
    + exact HnocollR'.
    + match goal with
      | H : roots_exclude x roots |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x (root_env_remove x R2) |- _ => exact H
      end.
    + exact HRr1.
    + exact Hroots1.
    + exact HkeysR1.
    + exact HrootsR1.
    + exact Hroots1_named.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_LetInfer.
        -- exact Htyped1_r.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x T1 Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_if_forward :
  forall env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots env Ω n R Σ (EIf e1 e2 e3) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EIf e1 e2 e3)) (rename_range rho) ->
  alpha_rename_expr rho used (EIf e1 e2 e3) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l (free_vars_expr e1)
    (free_vars_expr e2 ++ free_vars_expr e3) (rename_range rho))
    as [Hdisj1 Hdisj23].
  { intros x Hin. apply Hdisj. exact Hin. }
  destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
    (rename_range rho) Hdisj23) as [Hdisj2 Hdisj3].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
  destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnsR2 : root_env_no_shadow R').
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnsR3 : root_env_no_shadow R3).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      eapply typed_env_roots_root_env_names_subset; eassumption. }
  assert (HnocollR3 : rename_no_collision_on rho (root_env_names R3)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      destruct (root_env_lookup x R3) as [roots3_x |] eqn:Hlookup3.
      + match goal with
        | H : root_env_equiv R' R3 |- _ =>
            specialize (H x) as HeqR
        end.
        rewrite Hlookup3 in HeqR.
        destruct (root_env_lookup x R') as [roots2_x |] eqn:Hlookup2;
          try contradiction.
        eapply root_env_lookup_some_in_names. exact Hlookup2.
      + exfalso. eapply root_env_lookup_none_not_in_names; eauto. }
  destruct (Hexpr R Rr Σ Σr used e1 e1r used1 T_cond Σ1 R1 roots_cond)
    as [Σr1 [Rr1 [roots_condr
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots_cond]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall x, In x (ctx_names Σr1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hin.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped1_r. }
    assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used1).
    { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
    destruct (Hexpr R1 Rr1 Σ1 Σr1 used1 e2 e2r used2 T2 Σ2 R' roots2)
      as [Σr2 [Rr2 [roots2r
        [Htyped2_r [Hctx2_r [HnsRr2 [HRr2 Hroots2]]]]]]].
    + match goal with
      | H : typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R' roots2 |- _ =>
          exact H
      end.
    + exact Hctx1_r.
    + exact HnsR1.
    + exact HnsRr1.
    + exact HRr1.
    + exact HnocollR1.
    + exact HnocollR'.
    + exact Hctx_used1.
    + exact Hrange_used1.
    + exact Hdisj2.
    + exact He2.
    + assert (Hctx_used2 : forall x, In x (ctx_names Σr1) -> In x used2).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact He2 |].
        apply Hctx_used1. exact Hin. }
      assert (Hrange_used2 : forall x, In x (rename_range rho) -> In x used2).
      { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
      destruct (Hexpr R1 Rr1 Σ1 Σr1 used2 e3 e3r used3 T3 Σ3 R3 roots3)
        as [Σr3 [Rr3 [roots3r
          [Htyped3_r [Hctx3_r [HnsRr3 [HRr3 Hroots3]]]]]]].
      * match goal with
        | H : typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 |- _ =>
            exact H
        end.
      * exact Hctx1_r.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR3.
      * exact Hctx_used2.
      * exact Hrange_used2.
      * exact Hdisj3.
      * exact He3.
      * destruct (ctx_alpha_merge_forward
          rho Σ2 Σr2 Σ3 Σr3 Σ' Hctx2_r Hctx3_r
          ltac:(match goal with
          | H : ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ' |- _ =>
              exact H
          end)) as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4, Rr2, (root_set_union roots2r roots3r).
        split; [| split; [| split; [| split]]].
        -- eapply TER_If.
           ++ exact Htyped1_r.
           ++ match goal with
              | H : ty_core T_cond = TBooleans |- _ => exact H
              end.
           ++ exact Htyped2_r.
           ++ exact Htyped3_r.
           ++ match goal with
              | H : ty_core T2 = ty_core T3 |- _ => exact H
              end.
           ++ exact Hmerge_r.
           ++ eapply root_env_equiv_trans.
              ** exact HRr2.
              ** eapply root_env_equiv_trans.
                 --- eapply root_env_equiv_rename;
                     [ match goal with
                       | H : root_env_equiv R' R3 |- _ => exact H
                       end
                     | exact HnsR2
                     | exact HnsR3
                     | exact HnocollR'
                     | exact HnocollR3 ].
                 --- apply root_env_equiv_sym. exact HRr3.
        -- exact Hctx_merge.
        -- exact HnsRr2.
        -- exact HRr2.
        -- eapply root_set_equiv_trans.
           ++ apply root_set_union_equiv; eassumption.
           ++ apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_env_roots_var_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (EVar x)) (rename_range rho) ->
    alpha_rename_expr rho used (EVar x) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TERS_Var_Copy.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- apply Hdisj. simpl. left. reflexivity.
        -- match goal with
           | H : typed_place_env_structural env _ (PVar x) T |- _ =>
               exact H
           end.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe : ~ In x (rename_range rho)).
    { apply Hdisj. simpl. left. reflexivity. }
    destruct (ctx_alpha_consume_path_forward
      rho _ Σr x [] Σ' Hctx Hsafe
      ltac:(match goal with
        | H : sctx_consume_path _ x [] = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TERS_Var_Move.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_var_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (EVar x)) (rename_range rho) ->
    alpha_rename_expr rho used (EVar x) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_var_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_place_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EPlace p)) (rename_range rho) ->
    alpha_rename_expr rho used (EPlace p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TERS_Place_Copy.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    destruct (ctx_alpha_consume_path_forward
      rho Σ Σr x path Σ' Hctx Hsafe_x
      ltac:(match goal with
        | H : sctx_consume_path Σ x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TERS_Place_Move.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_place_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EPlace p)) (rename_range rho) ->
    alpha_rename_expr rho used (EPlace p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_place_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_borrow_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EBorrow rk p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EBorrow rk p)) (rename_range rho) ->
    alpha_rename_expr rho used (EBorrow rk p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. destruct rk; injection Hrename as <- <-;
    inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    exists Σr, Rr, (root_of_place (rename_place rho p)). repeat split.
    + eapply TERS_BorrowShared.
      eapply alpha_rename_typed_place_env_structural_forward; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + rewrite root_of_place_rename_place. simpl. tauto.
    + rewrite root_of_place_rename_place. simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TERS_BorrowShared_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    exists Σr, Rr, [RStore (lookup_rename x rho)]. repeat split.
    + eapply TERS_BorrowUnique.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply ctx_alpha_lookup_mut_forward; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + simpl. tauto.
    + simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TERS_BorrowUnique_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
Qed.
Lemma alpha_rename_typed_env_roots_borrow_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EBorrow rk p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EBorrow rk p)) (rename_range rho) ->
    alpha_rename_expr rho used (EBorrow rk p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_borrow_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_replace_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EReplace p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EReplace p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ1 R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (ctx_alpha_restore_path_forward
      rho Σ1 Σr1 x path Σ' Hctx_new_r Hsafe_x
      ltac:(match goal with
        | H : sctx_restore_path Σ1 x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr2 [Hrestore_r Hctx_restore]].
    destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_result_r Hroots_result]].
    destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr2,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Replace_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Hlookup_result_r.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
      * exact Hrestore_r.
    + exact Hctx_restore.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + exact Hroots_result.
Qed.

Lemma alpha_rename_typed_env_roots_replace_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EReplace p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EReplace p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ1 R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (ctx_alpha_restore_path_forward
      rho Σ1 Σr1 x path Σ' Hctx_new_r Hsafe_x
      ltac:(match goal with
        | H : sctx_restore_path Σ1 x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr2 [Hrestore_r Hctx_restore]].
    destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_result_r Hroots_result]].
    destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr2,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Replace_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Hlookup_result_r.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
      * exact Hrestore_r.
    + exact Hctx_restore.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + exact Hroots_result.
Qed.

Lemma alpha_rename_typed_env_roots_assign_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EAssign p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EAssign p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr1,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Assign_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T_old <> ULinear |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
    + exact Hctx_new_r.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_assign_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EAssign p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EAssign p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr1,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Assign_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T_old <> ULinear |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
    + exact Hctx_new_r.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_if_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (EIf e1 e2 e3)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EIf e1 e2 e3)) (rename_range rho) ->
  alpha_rename_expr rho used (EIf e1 e2 e3) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l (free_vars_expr e1)
    (free_vars_expr e2 ++ free_vars_expr e3) (rename_range rho))
    as [Hdisj1 Hdisj23].
  { intros x Hin. apply Hdisj. exact Hin. }
  destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
    (rename_range rho) Hdisj23) as [Hdisj2 Hdisj3].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
  destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR. }
  assert (HnsR2 : root_env_no_shadow R').
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnsR3 : root_env_no_shadow R3).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      eapply typed_env_roots_root_env_names_subset.
      + eapply typed_env_roots_shadow_safe_roots. eassumption.
      + exact Hin. }
  assert (HnocollR3 : rename_no_collision_on rho (root_env_names R3)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      destruct (root_env_lookup x R3) as [roots3_x |] eqn:Hlookup3.
      + match goal with
        | H : root_env_equiv R' R3 |- _ =>
            specialize (H x) as HeqR
        end.
        rewrite Hlookup3 in HeqR.
        destruct (root_env_lookup x R') as [roots2_x |] eqn:Hlookup2;
          try contradiction.
        eapply root_env_lookup_some_in_names. exact Hlookup2.
      + exfalso. eapply root_env_lookup_none_not_in_names; eauto. }
  destruct (Hexpr R Rr Σ Σr used e1 e1r used1 T_cond Σ1 R1 roots_cond)
    as [Σr1 [Rr1 [roots_condr
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots_cond]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall x, In x (ctx_names Σr1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hin.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used1).
    { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
    destruct (Hexpr R1 Rr1 Σ1 Σr1 used1 e2 e2r used2 T2 Σ2 R' roots2)
      as [Σr2 [Rr2 [roots2r
        [Htyped2_r [Hctx2_r [HnsRr2 [HRr2 Hroots2]]]]]]].
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R' roots2 |- _ =>
          exact H
      end.
    + exact Hctx1_r.
    + exact HnsR1.
    + exact HnsRr1.
    + exact HRr1.
    + exact HnocollR1.
    + exact HnocollR'.
    + exact Hctx_used1.
    + exact Hrange_used1.
    + exact Hdisj2.
    + exact He2.
    + assert (Hctx_used2 : forall x, In x (ctx_names Σr1) -> In x used2).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact He2 |].
        apply Hctx_used1. exact Hin. }
      assert (Hrange_used2 : forall x, In x (rename_range rho) -> In x used2).
      { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
      destruct (Hexpr R1 Rr1 Σ1 Σr1 used2 e3 e3r used3 T3 Σ3 R3 roots3)
        as [Σr3 [Rr3 [roots3r
          [Htyped3_r [Hctx3_r [HnsRr3 [HRr3 Hroots3]]]]]]].
      * match goal with
        | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 |- _ =>
            exact H
        end.
      * exact Hctx1_r.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR3.
      * exact Hctx_used2.
      * exact Hrange_used2.
      * exact Hdisj3.
      * exact He3.
      * destruct (ctx_alpha_merge_forward
          rho Σ2 Σr2 Σ3 Σr3 Σ' Hctx2_r Hctx3_r
          ltac:(match goal with
          | H : ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ' |- _ =>
              exact H
          end)) as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4, Rr2, (root_set_union roots2r roots3r).
        split; [| split; [| split; [| split]]].
        -- eapply TERS_If.
           ++ exact Htyped1_r.
           ++ match goal with
              | H : ty_core T_cond = TBooleans |- _ => exact H
              end.
           ++ exact Htyped2_r.
           ++ exact Htyped3_r.
           ++ match goal with
              | H : ty_core T2 = ty_core T3 |- _ => exact H
              end.
           ++ exact Hmerge_r.
           ++ eapply root_env_equiv_trans.
              ** exact HRr2.
              ** eapply root_env_equiv_trans.
                 --- eapply root_env_equiv_rename;
                     [ match goal with
                       | H : root_env_equiv R' R3 |- _ => exact H
                       end
                     | exact HnsR2
                     | exact HnsR3
                     | exact HnocollR'
                     | exact HnocollR3 ].
                 --- apply root_env_equiv_sym. exact HRr3.
        -- exact Hctx_merge.
        -- exact HnsRr2.
        -- exact HRr2.
        -- eapply root_set_equiv_trans.
           ++ apply root_set_union_equiv; eassumption.
           ++ apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_env_roots_if_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      expr_size e < expr_size (EIf e1 e2 e3) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (EIf e1 e2 e3)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EIf e1 e2 e3)) (rename_range rho) ->
  alpha_rename_expr rho used (EIf e1 e2 e3) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l (free_vars_expr e1)
    (free_vars_expr e2 ++ free_vars_expr e3) (rename_range rho))
    as [Hdisj1 Hdisj23].
  { intros x Hin. apply Hdisj. exact Hin. }
  destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
    (rename_range rho) Hdisj23) as [Hdisj2 Hdisj3].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
  destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR. }
  assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T_cond Σ1 R1 roots_cond)
      as [Hroots_env1 _].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_env1. }
  assert (HnsR2 : root_env_no_shadow R').
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnsR3 : root_env_no_shadow R3).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      eapply typed_env_roots_root_env_names_subset.
      + eapply typed_env_roots_shadow_safe_roots. eassumption.
      + exact Hin. }
  assert (HnocollR3 : rename_no_collision_on rho (root_env_names R3)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      destruct (root_env_lookup x R3) as [roots3_x |] eqn:Hlookup3.
      + match goal with
        | H : root_env_equiv R' R3 |- _ =>
            specialize (H x) as HeqR
        end.
        rewrite Hlookup3 in HeqR.
        destruct (root_env_lookup x R') as [roots2_x |] eqn:Hlookup2;
          try contradiction.
        eapply root_env_lookup_some_in_names. exact Hlookup2.
      + exfalso. eapply root_env_lookup_none_not_in_names; eauto. }
  destruct (Hexpr R Rr Σ Σr used e1 e1r used1 T_cond Σ1 R1 roots_cond)
    as [Σr1 [Rr1 [roots_condr
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots_cond]]]]]]].
  - simpl; lia.
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall x, In x (ctx_names Σr1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hin.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used1).
    { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
    destruct (Hexpr R1 Rr1 Σ1 Σr1 used1 e2 e2r used2 T2 Σ2 R' roots2)
      as [Σr2 [Rr2 [roots2r
        [Htyped2_r [Hctx2_r [HnsRr2 [HRr2 Hroots2]]]]]]].
    + simpl; lia.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R' roots2 |- _ =>
          exact H
      end.
    + exact Hctx1_r.
    + exact HnsR1.
    + exact HnsRr1.
    + exact HRr1.
    + exact HkeysR1.
    + exact HrootsR1.
    + exact HnocollR1.
    + exact HnocollR'.
    + exact Hctx_used1.
    + exact Hrange_used1.
    + exact Hdisj2.
    + exact He2.
    + assert (Hctx_used2 : forall x, In x (ctx_names Σr1) -> In x used2).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact He2 |].
        apply Hctx_used1. exact Hin. }
      assert (Hrange_used2 : forall x, In x (rename_range rho) -> In x used2).
      { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
      destruct (Hexpr R1 Rr1 Σ1 Σr1 used2 e3 e3r used3 T3 Σ3 R3 roots3)
        as [Σr3 [Rr3 [roots3r
          [Htyped3_r [Hctx3_r [HnsRr3 [HRr3 Hroots3]]]]]]].
      * simpl; lia.
      * match goal with
        | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 |- _ =>
            exact H
        end.
      * exact Hctx1_r.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR3.
      * exact Hctx_used2.
      * exact Hrange_used2.
      * exact Hdisj3.
      * exact He3.
      * destruct (ctx_alpha_merge_forward
          rho Σ2 Σr2 Σ3 Σr3 Σ' Hctx2_r Hctx3_r
          ltac:(match goal with
          | H : ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ' |- _ =>
              exact H
          end)) as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4, Rr2, (root_set_union roots2r roots3r).
        split; [| split; [| split; [| split]]].
        -- eapply TERS_If.
           ++ exact Htyped1_r.
           ++ match goal with
              | H : ty_core T_cond = TBooleans |- _ => exact H
              end.
           ++ exact Htyped2_r.
           ++ exact Htyped3_r.
           ++ match goal with
              | H : ty_core T2 = ty_core T3 |- _ => exact H
              end.
           ++ exact Hmerge_r.
           ++ eapply root_env_equiv_trans.
              ** exact HRr2.
              ** eapply root_env_equiv_trans.
                 --- eapply root_env_equiv_rename;
                     [ match goal with
                       | H : root_env_equiv R' R3 |- _ => exact H
                       end
                     | exact HnsR2
                     | exact HnsR3
                     | exact HnocollR'
                     | exact HnocollR3 ].
                 --- apply root_env_equiv_sym. exact HRr3.
        -- exact Hctx_merge.
        -- exact HnsRr2.
        -- exact HRr2.
        -- eapply root_set_equiv_trans.
           ++ apply root_set_union_equiv; eassumption.
           ++ apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_args_roots_forward :
  forall env Ω n rho R Rr Σ Σr args argsr used used' ps psr Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e args ->
      typed_env_roots env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range rho) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exists Σr' Rr' rootsr,
    typed_args_roots env Ω n Rr Σr argsr psr Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots).
Proof.
  intros env Ω n rho R Rr Σ Σr args.
  revert R Rr Σ Σr.
  induction args as [| arg rest IH]; intros R Rr Σ Σr argsr used used'
    ps psr Σ' R' roots Hexpr Htyped_args Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hparams Hrename;
    simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr, Rr, []. repeat split; try constructor; assumption.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range rho) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr rho used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct ps as [| p ps_tail]; [inversion Htyped_args|].
    destruct psr as [| pr psr_tail]; [inversion Hparams|].
    inversion Htyped_args; subst.
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_args_roots_root_env_names_subset; eassumption. }
    destruct (Hexpr R Rr Σ Σr used arg ar used1 T_e Σ1 R1 roots0)
      as [Σr1 [Rr1 [rootsr0
        [Htyped_arg_r [Hctx_arg [HnsRr1 [HRr1 Hroots0]]]]]]].
    + left. reflexivity.
    + assumption.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range rho) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH R1 Rr1 Σ1 Σr1 restr used1 used2 ps_tail psr_tail
        Σ' R' roots_rest)
        as [Σr2 [Rr2 [rootsr_rest
          [Htyped_tail_r [Hctx_tail [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      * intros R0 R0r Σa Σb used0 e er used_tail T Σa' R0' roots_e
          Hin Htyped_e Halpha HnsR0 HnsR0r HR0r HnocollR0 HnocollR0'
          Hcu Hru Hd Hr.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Htyped_e.
        -- exact Halpha.
        -- exact HnsR0.
        -- exact HnsR0r.
        -- exact HR0r.
        -- exact HnocollR0.
        -- exact HnocollR0'.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
      * assumption.
      * exact Hctx_arg.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exists Σr2, Rr2, (rootsr0 :: rootsr_rest). repeat split.
        -- eapply TERArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              assumption.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
        -- exact HnsRr2.
        -- exact HRr2.
        -- simpl. constructor; assumption.
Qed.

Lemma alpha_rename_typed_fields_roots_forward :
  forall env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_fields_roots env Ω n lts args_ty R Σ fields defs Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr rho used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  exists Σr' Rr' rootsr,
    typed_fields_roots env Ω n lts args_ty Rr Σr fieldsr defs Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots Hexpr Htyped_fields Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  revert Rr Σr used fieldsr used' Hctx HnsRr HRr HnocollR Hctx_used
    Hrange_used Hrename.
  induction Htyped_fields; intros Rr0 Σr0 used0 fieldsr0 used_out
    Hctx HnsRr0 HRr0 HnocollR0 Hctx_used0 Hrange_used0 Hrename0.
  - exists Σr0, Rr0, [].
    split; [eapply TERFields_Nil|].
    split; [exact Hctx|].
    split; [exact HnsRr0|].
    split; [exact HRr0|].
    simpl. apply root_set_equiv_refl.
  - destruct (alpha_rename_struct_fields_lookup_exists_forward rho used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename0 H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_fields_roots_root_env_names_subset; eassumption. }
    destruct (Hexpr R Rr0 Σ Σr0 used_field e_field e_fieldr
      used_field_out T_field Σ1 R1 roots_field)
      as [Σr1 [Rr1 [roots_fieldr
        [Htyped_field_r [Hctx_field [HnsRr1 [HRr1 Hroots_field]]]]]]].
    + exact Hfield_in.
    + exact H0.
    + exact Hctx.
    + assumption.
    + exact HnsRr0.
    + exact HRr0.
    + exact HnocollR0.
    + exact HnocollR1.
    + intros x Hin. apply Hused_prefix. apply Hctx_used0. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used0. exact Hin.
    + clear -H Hdisj.
      induction fields as [| [fname0 e0] rest IH]; simpl in H, Hdisj.
      * discriminate.
      * destruct (String.eqb (Program.field_name f) fname0) eqn:Hname.
        -- injection H as <-.
           destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [_ Hrest_disj].
           eapply IH; eauto.
    + exact Hrename_field.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used0.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr HnsR1 HnocollR' Hdisj
        Rr1 Σr1 used0 fieldsr0 used_out Hctx_field HnsRr1 HRr1
        HnocollR1 Hctx_used_tail Hrange_used0 Hrename0)
        as [Σr2 [Rr2 [roots_restr
          [Htyped_rest_r [Hctx_rest [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      exists Σr2, Rr2, (root_set_union roots_fieldr roots_restr).
      split.
      * eapply TERFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * split; [exact Hctx_rest|].
        split; [exact HnsRr2|].
        split; [exact HRr2|].
        eapply root_set_equiv_trans.
        -- apply root_set_union_equiv; eassumption.
        -- apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_args_roots_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr args argsr used used' ps psr Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range rho) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exists Σr' Rr' rootsr,
    typed_args_roots_shadow_safe env Ω n Rr Σr argsr psr Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots).
Proof.
  intros env Ω n rho R Rr Σ Σr args.
  revert R Rr Σ Σr.
  induction args as [| arg rest IH]; intros R Rr Σ Σr argsr used used'
    ps psr Σ' R' roots Hexpr Htyped_args Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hparams Hrename;
    simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr, Rr, []. repeat split; try constructor; assumption.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range rho) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr rho used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct ps as [| p ps_tail]; [inversion Htyped_args|].
    destruct psr as [| pr psr_tail]; [inversion Hparams|].
    inversion Htyped_args; subst.
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_args_roots_root_env_names_subset.
        + eapply typed_args_roots_shadow_safe_roots. exact H10.
        + exact Hin. }
    destruct (Hexpr R Rr Σ Σr used arg ar used1 T_e Σ1 R1 roots0)
      as [Σr1 [Rr1 [rootsr0
        [Htyped_arg_r [Hctx_arg [HnsRr1 [HRr1 Hroots0]]]]]]].
    + left. reflexivity.
    + assumption.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range rho) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH R1 Rr1 Σ1 Σr1 restr used1 used2 ps_tail psr_tail
        Σ' R' roots_rest)
        as [Σr2 [Rr2 [rootsr_rest
          [Htyped_tail_r [Hctx_tail [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      * intros R0 R0r Σa Σb used0 e er used_tail T Σa' R0' roots_e
          Hin Htyped_e Halpha HnsR0 HnsR0r HR0r HnocollR0 HnocollR0'
          Hcu Hru Hd Hr.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Htyped_e.
        -- exact Halpha.
        -- exact HnsR0.
        -- exact HnsR0r.
        -- exact HR0r.
        -- exact HnocollR0.
        -- exact HnocollR0'.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
      * assumption.
      * exact Hctx_arg.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exists Σr2, Rr2, (rootsr0 :: rootsr_rest). repeat split.
        -- eapply TERSArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              assumption.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
        -- exact HnsRr2.
        -- exact HRr2.
        -- simpl. constructor; assumption.
Qed.

Lemma alpha_rename_typed_fields_roots_shadow_safe_forward :
  forall env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_fields_roots_shadow_safe env Ω n lts args_ty R Σ fields defs
    Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr rho used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  exists Σr' Rr' rootsr,
    typed_fields_roots_shadow_safe env Ω n lts args_ty Rr Σr fieldsr defs
      Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots Hexpr Htyped_fields Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  revert Rr Σr used fieldsr used' Hctx HnsRr HRr HnocollR Hctx_used
    Hrange_used Hrename.
  induction Htyped_fields; intros Rr0 Σr0 used0 fieldsr0 used_out
    Hctx HnsRr0 HRr0 HnocollR0 Hctx_used0 Hrange_used0 Hrename0.
  - exists Σr0, Rr0, [].
    split; [eapply TERSFields_Nil|].
    split; [exact Hctx|].
    split; [exact HnsRr0|].
    split; [exact HRr0|].
    simpl. apply root_set_equiv_refl.
  - destruct (alpha_rename_struct_fields_lookup_exists_forward rho used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename0 H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_fields_roots_root_env_names_subset.
        + match goal with
          | Htail : typed_fields_roots_shadow_safe _ _ _ _ _ R1 Σ1 fields rest _ _ _ |- _ =>
              eapply typed_fields_roots_shadow_safe_roots; exact Htail
          end.
        + exact Hin. }
    destruct (Hexpr R Rr0 Σ Σr0 used_field e_field e_fieldr
      used_field_out T_field Σ1 R1 roots_field)
      as [Σr1 [Rr1 [roots_fieldr
        [Htyped_field_r [Hctx_field [HnsRr1 [HRr1 Hroots_field]]]]]]].
    + exact Hfield_in.
    + exact H0.
    + exact Hctx.
    + assumption.
    + exact HnsRr0.
    + exact HRr0.
    + exact HnocollR0.
    + exact HnocollR1.
    + intros x Hin. apply Hused_prefix. apply Hctx_used0. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used0. exact Hin.
    + clear -H Hdisj.
      induction fields as [| [fname0 e0] rest IH]; simpl in H, Hdisj.
      * discriminate.
      * destruct (String.eqb (Program.field_name f) fname0) eqn:Hname.
        -- injection H as <-.
           destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [_ Hrest_disj].
           eapply IH; eauto.
    + exact Hrename_field.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used0.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr HnsR1 HnocollR' Hdisj
        Rr1 Σr1 used0 fieldsr0 used_out Hctx_field HnsRr1 HRr1
        HnocollR1 Hctx_used_tail Hrange_used0 Hrename0)
        as [Σr2 [Rr2 [roots_restr
          [Htyped_rest_r [Hctx_rest [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      exists Σr2, Rr2, (root_set_union roots_fieldr roots_restr).
      split.
      * eapply TERSFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * split; [exact Hctx_rest|].
        split; [exact HnsRr2|].
        split; [exact HRr2|].
        eapply root_set_equiv_trans.
        -- apply root_set_union_equiv; eassumption.
        -- apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_args_roots_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr args argsr used used' ps psr Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range rho) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exists Σr' Rr' rootsr,
    typed_args_roots_shadow_safe env Ω n Rr Σr argsr psr Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots).
Proof.
  intros env Ω n rho R Rr Σ Σr args.
  revert R Rr Σ Σr.
  induction args as [| arg rest IH]; intros R Rr Σ Σr argsr used used'
    ps psr Σ' R' roots Hexpr Htyped_args Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj
    Hparams Hrename; simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr, Rr, []. repeat split; try constructor; assumption.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range rho) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr rho used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct ps as [| p ps_tail]; [inversion Htyped_args|].
    destruct psr as [| pr psr_tail]; [inversion Hparams|].
    inversion Htyped_args; subst.
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ arg T_e Σ1 R1 roots0) as [Hroots_env1 _].
      - match goal with
        | H : typed_env_roots_shadow_safe env Ω n R Σ arg T_e Σ1 R1 roots0 |- _ =>
            exact H
        end.
      - exact HnsR.
      - exact Hroots.
      - exact Hroots_env1. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_args_roots_root_env_names_subset.
        + eapply typed_args_roots_shadow_safe_roots. exact H10.
        + exact Hin. }
    destruct (Hexpr R Rr Σ Σr used arg ar used1 T_e Σ1 R1 roots0)
      as [Σr1 [Rr1 [rootsr0
        [Htyped_arg_r [Hctx_arg [HnsRr1 [HRr1 Hroots0]]]]]]].
    + left. reflexivity.
    + assumption.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact Hkeys.
    + exact Hroots.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range rho) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH R1 Rr1 Σ1 Σr1 restr used1 used2 ps_tail psr_tail
        Σ' R' roots_rest)
        as [Σr2 [Rr2 [rootsr_rest
          [Htyped_tail_r [Hctx_tail [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      * intros R0 R0r Σa Σb used0 e er used_tail T Σa' R0' roots_e
          Hin Htyped_e Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots_support
          HnocollR0 HnocollR0' Hcu Hru Hd Hr.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Htyped_e.
        -- exact Halpha.
        -- exact HnsR0.
        -- exact HnsR0r.
        -- exact HR0r.
        -- exact Hkeys0.
        -- exact Hroots_support.
        -- exact HnocollR0.
        -- exact HnocollR0'.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
      * assumption.
      * exact Hctx_arg.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exists Σr2, Rr2, (rootsr0 :: rootsr_rest). repeat split.
        -- eapply TERSArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              assumption.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
        -- exact HnsRr2.
        -- exact HRr2.
        -- simpl. constructor; assumption.
Qed.

Lemma alpha_rename_typed_fields_roots_shadow_safe_support_forward :
  forall env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_fields_roots_shadow_safe env Ω n lts args_ty R Σ fields defs
    Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr rho used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  exists Σr' Rr' rootsr,
    typed_fields_roots_shadow_safe env Ω n lts args_ty Rr Σr fieldsr defs
      Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots Hexpr Htyped_fields Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj
    Hrename.
  revert Rr Σr used fieldsr used' Hctx HnsRr HRr Hkeys Hroots
    HnocollR Hctx_used Hrange_used Hrename.
  induction Htyped_fields; intros Rr0 Σr0 used0 fieldsr0 used_out
    Hctx HnsRr0 HRr0 Hkeys0 Hroots0 HnocollR0 Hctx_used0
    Hrange_used0 Hrename0.
  - exists Σr0, Rr0, [].
    split; [eapply TERSFields_Nil|].
    split; [exact Hctx|].
    split; [exact HnsRr0|].
    split; [exact HRr0|].
    simpl. apply root_set_equiv_refl.
  - destruct (alpha_rename_struct_fields_lookup_exists_forward rho used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename0 H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e_field T_field Σ1 R1 roots_field)
        as [Hroots_env1 _].
      - exact H0.
      - exact HnsR.
      - exact Hroots0.
      - exact Hroots_env1. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_fields_roots_root_env_names_subset.
        + match goal with
          | Htail : typed_fields_roots_shadow_safe _ _ _ _ _ R1 Σ1 fields rest _ _ _ |- _ =>
              eapply typed_fields_roots_shadow_safe_roots; exact Htail
          end.
        + exact Hin. }
    destruct (Hexpr R Rr0 Σ Σr0 used_field e_field e_fieldr
      used_field_out T_field Σ1 R1 roots_field)
      as [Σr1 [Rr1 [roots_fieldr
        [Htyped_field_r [Hctx_field [HnsRr1 [HRr1 Hroots_field]]]]]]].
    + exact Hfield_in.
    + exact H0.
    + exact Hctx.
    + assumption.
    + exact HnsRr0.
    + exact HRr0.
    + exact Hkeys0.
    + exact Hroots0.
    + exact HnocollR0.
    + exact HnocollR1.
    + intros x Hin. apply Hused_prefix. apply Hctx_used0. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used0. exact Hin.
    + clear -H Hdisj.
      induction fields as [| [fname0 e0] rest IH]; simpl in H, Hdisj.
      * discriminate.
      * destruct (String.eqb (Program.field_name f) fname0) eqn:Hname.
        -- injection H as <-.
           destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [_ Hrest_disj].
           eapply IH; eauto.
    + exact Hrename_field.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used0.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr HnsR1 HnocollR'
        Hdisj Rr1 Σr1 used0 fieldsr0 used_out Hctx_field HnsRr1
        HRr1 HkeysR1 HrootsR1 HnocollR1 Hctx_used_tail Hrange_used0
        Hrename0)
        as [Σr2 [Rr2 [roots_restr
          [Htyped_rest_r [Hctx_rest [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      exists Σr2, Rr2, (root_set_union roots_fieldr roots_restr).
      split.
      * eapply TERSFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * split; [exact Hctx_rest|].
        split; [exact HnsRr2|].
        split; [exact HRr2|].
        eapply root_set_equiv_trans.
        -- apply root_set_union_equiv; eassumption.
        -- apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma root_env_names_in_lookup :
  forall x R,
    In x (root_env_names R) ->
    exists roots, root_env_lookup x R = Some roots.
Proof.
  intros x R Hin.
  induction R as [| [y roots_y] rest IH]; simpl in Hin; try contradiction.
  simpl.
  destruct Hin as [Heq | Hin].
  - subst y. rewrite ident_eqb_refl. eauto.
  - destruct (ident_eqb x y); eauto.
Qed.

Lemma root_env_equiv_names_subset_l :
  forall R R' x,
    root_env_equiv R R' ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros R R' x Heq Hin.
  destruct (root_env_names_in_lookup x R Hin) as [roots Hlookup].
  destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
    as [roots' [Hlookup' _]].
  eapply root_env_lookup_some_in_names. exact Hlookup'.
Qed.

Lemma alpha_rename_typed_match_tail_roots_shadow_safe_forward :
  forall env Ω n rho lts args R roots_scrut roots_scrutr Rr Σ Σr branches branchesr used used'
      variants expected_core R_out Rr_out Σs Ts rootss,
  (forall rho0 R0 R0r Σa Σb used0 variant binders e er used1 T Σa' R0' roots0,
      In (variant, binders, e) branches ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho0 Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho0 R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho0 (root_env_names R0) ->
      rename_no_collision_on rho0 (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho0) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho0) ->
      alpha_rename_expr rho0 used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T
          Σb' R0r' roots0r /\
        ctx_alpha rho0 Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho0 R0') /\
        root_set_equiv roots0r (root_set_rename rho0 roots0)) ->
  typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
    expected_core R_out Σs Ts rootss ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow R_out ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  root_set_sctx_roots_named roots_scrut Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R_out) ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  root_set_equiv roots_scrutr (root_set_rename rho roots_scrut) ->
  disjoint_names
    ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
        match branches0 with
        | [] => []
        | (_, _, e) :: rest => free_vars_expr e ++ go rest
        end) branches)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name, binders, e) :: rest =>
          let binder_seed := binders ++ free_vars_expr e ++ used0 in
          let '(binders', rho_branch, used1) :=
            alpha_rename_idents rho binder_seed binders in
          let (e', used2) := alpha_rename_expr rho_branch used1 e in
          let (rest', used3) := go used2 rest in
          ((name, binders', e') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  root_env_equiv Rr_out (root_env_rename rho R_out) ->
  exists Σrs rootssr,
    typed_match_tail_roots_shadow_safe env Ω n lts args Rr roots_scrutr Σr branchesr variants
      expected_core Rr_out Σrs Ts rootssr /\
    Forall2 (ctx_alpha rho) Σs Σrs /\
    Forall2 root_set_equiv rootssr (map (root_set_rename rho) rootss).
Proof.
  intros env Ω n rho lts args R roots_scrut roots_scrutr Rr Σ Σr branches branchesr used used'
    variants expected_core R_out Rr_out Σs Ts rootss Hexpr Htyped_tail
    Hctx HnsR HnsRout HnsRr HRr Hkeys Hroots Hroots_scrut_named
    HnocollR HnocollRout Hctx_used Hrange_used Hroots_scrutr Hdisj Hrename HRout.
  induction Htyped_tail.
  - exists [], []. repeat split; constructor.
	  - destruct (alpha_rename_match_branches_lookup_payload_forward
	      rho used branches branchesr used' (Program.enum_variant_name v) binders e
	      Hrename H H4)
      as [bindersr [rho_branch [er [used_pre [used_branch [used_branch_out
        [Hbinders_r [Hlookup_r [Hrename_binders
          [Hrename_branch Hused_prefix]]]]]]]]]].
	    pose proof (lookup_expr_branch_binders_expr_in_alpha _ _ _ _ H H4)
	      as Hbranch_in.
	    unfold match_payload_params in H0.
	    destruct (match_binder_params_alpha_rename_idents
	      rho (binders ++ free_vars_expr e ++ used_pre) binders bindersr rho_branch
	      used_branch (instantiate_enum_variant_field_tys lts args v) ps
	      Hrename_binders H0) as [psr [Hparams_r [Hparams_alpha Hrename_params]]].
    assert (Hparams_nodup_r : params_names_nodup_b psr = true).
    { apply params_names_nodup_b_complete_alpha.
      rewrite (match_binder_params_names _ _ _ Hparams_r).
      eapply alpha_rename_idents_outputs_nodup. exact Hrename_binders. }
    assert (Hctx_none_r : ctx_lookup_params_none_b psr Σr = true).
    { eapply ctx_lookup_params_none_b_fresh_used with (used := used_pre).
      - intros x Hin. apply Hused_prefix. apply Hctx_used. exact Hin.
      - rewrite (match_binder_params_names _ _ _ Hparams_r).
        eapply Forall_fresh_weaken.
        + intros x Hin.
          apply in_or_app. right. apply in_or_app. right. exact Hin.
        + eapply alpha_rename_idents_fresh_used. exact Hrename_binders. }
    assert (Hctx_payload :
      ctx_alpha rho_branch (sctx_add_params ps Σ) (sctx_add_params psr Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Hrename_params.
      - exact Hctx.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin. }
    assert (Hkeys_r : root_env_sctx_keys_named Rr Σr).
    { eapply root_env_sctx_keys_named_rename; eassumption. }
    assert (Hroots_r : root_env_sctx_roots_named Rr Σr).
    { eapply root_env_sctx_roots_named_rename.
      - exact Hctx.
      - exact HnsR.
      - exact HRr.
      - exact Hroots. }
    assert (Hroots_scrutr_named : root_set_sctx_roots_named roots_scrutr Σr).
    { eapply root_set_sctx_roots_named_rename.
      - exact Hctx.
      - exact Hroots_scrutr.
      - exact Hroots_scrut_named. }
    assert (Hroots_scrut_excl : roots_exclude_params ps roots_scrut).
    { unfold roots_exclude_params.
      apply Forall_forall. intros x Hin.
      eapply root_set_sctx_roots_named_fresh_exclude.
      - exact Hroots_scrut_named.
      - eapply ctx_lookup_params_none_b_not_in_names; eassumption. }
    assert (Henv_excl_R : root_env_excludes_params ps R).
    { unfold root_env_excludes_params.
      apply Forall_forall. intros x Hin.
      eapply root_env_sctx_roots_named_fresh_excludes.
      - exact Hroots.
      - eapply ctx_lookup_params_none_b_not_in_names; eassumption. }
    assert (Hroot_none_r : root_env_lookup_params_none_b psr Rr = true).
    { eapply root_env_lookup_params_none_b_from_sctx_keys; eassumption. }
    pose (R_payload_r := root_env_add_params_roots_same psr roots_scrutr Rr).
    assert (Hroots_scrutr_branch :
      root_set_equiv roots_scrutr (root_set_rename rho_branch roots_scrut)).
    { eapply root_set_equiv_trans.
      - exact Hroots_scrutr.
      - apply root_set_equiv_sym.
        eapply alpha_rename_params_root_set_rename_excluded.
        + exact Hrename_params.
        + exact Hroots_scrut_excl. }
    assert (HRpayload_r :
	      root_env_equiv R_payload_r (root_env_rename rho_branch R_payload)).
	    { unfold R_payload_r. subst R_payload.
	      eapply alpha_rename_params_root_env_add_params_roots_same_rename_equiv.
	      - exact Hrename_params.
	      - exact HnsR.
	      - exact H3.
	      - exact H1.
	      - exact Hroots_scrut_excl.
	      - exact Henv_excl_R.
	      - exact HRr.
      - exact Hroots_scrutr_branch. }
    assert (Hkeys_payload_r :
      root_env_sctx_keys_named R_payload_r (sctx_add_params psr Σr)).
    { unfold R_payload_r.
      apply root_env_sctx_keys_named_add_params_roots_same. exact Hkeys_r. }
    assert (Hkeys_payload :
      root_env_sctx_keys_named R_payload (sctx_add_params ps Σ)).
    { subst R_payload.
      apply root_env_sctx_keys_named_add_params_roots_same. exact Hkeys. }
    assert (Hroots_payload_r :
      root_env_sctx_roots_named R_payload_r (sctx_add_params psr Σr)).
    { unfold R_payload_r.
      apply root_env_sctx_roots_named_add_params_roots_same; assumption. }
    assert (Hns_payload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hns_payload_r : root_env_no_shadow R_payload_r).
    { unfold R_payload_r.
      eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hnocoll_payload :
      rename_no_collision_on rho_branch (root_env_names R_payload)).
    { subst R_payload.
	      eapply alpha_rename_params_root_env_add_params_roots_same_no_collision_on.
	      - exact Hrename_params.
	      - exact Hctx.
	      - exact Hkeys.
	      - exact H3.
	      - exact H1.
	      - exact H2.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin.
      - exact HnocollR. }
    assert (HnocollRv : rename_no_collision_on rho (root_env_names Rv)).
    { eapply rename_no_collision_on_weaken_names.
	      - exact HnocollRout.
	      - intros x Hin.
	        eapply root_env_equiv_names_subset_l.
	        + exact H13.
	        + exact Hin. }
    assert (HnsRv : root_env_no_shadow Rv).
    { subst Rv.
	      apply root_env_remove_match_params_no_shadow.
	      eapply typed_env_roots_no_shadow.
	      - eapply typed_env_roots_shadow_safe_roots. exact H6.
      - subst R_payload.
        eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hkeys_Rv_payload :
      root_env_sctx_keys_named Rv_payload (sctx_add_params ps Σ)).
    { assert (Hkeys_Rv_payload0 :
	        root_env_sctx_keys_named Rv_payload Σv_payload).
	      { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
	          as [Hkeys_expr _].
	        eapply Hkeys_expr.
	        - exact H6.
        - exact Hns_payload.
        - exact Hkeys_payload. }
      eapply root_env_sctx_keys_named_same_bindings.
      - apply sctx_same_bindings_sym.
	        eapply typed_env_structural_same_bindings.
	        eapply typed_env_roots_structural.
	        eapply typed_env_roots_shadow_safe_roots. exact H6.
      - exact Hkeys_Rv_payload0. }
    assert (Hnocoll_Rv_payload :
      rename_no_collision_on rho_branch (root_env_names Rv_payload)).
    { subst Rv.
      eapply alpha_rename_params_root_env_remove_match_params_no_collision_on.
      - exact Hrename_params.
	      - exact Hctx.
	      - eapply typed_env_roots_no_shadow.
	        + eapply typed_env_roots_shadow_safe_roots. exact H6.
	        + exact Hns_payload.
	      - exact Hkeys_Rv_payload.
	      - exact H1.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin.
      - exact HnocollRv. }
    destruct (Hexpr rho_branch R_payload R_payload_r
      (sctx_add_params ps Σ) (sctx_add_params psr Σr) used_branch
      (Program.enum_variant_name v) binders e er used_branch_out T
      Σv_payload Rv_payload roots)
      as [Σvr [Rvr [rootsr
        [Htyped_branch_r [Hctx_branch [HnsRvr [HRvr Hrootsr]]]]]]].
	    + exact Hbranch_in.
	    + exact H6.
    + exact Hctx_payload.
    + exact Hns_payload.
    + exact Hns_payload_r.
    + exact HRpayload_r.
    + exact Hkeys_payload.
    + subst R_payload.
      apply root_env_sctx_roots_named_add_params_roots_same; assumption.
    + exact Hnocoll_payload.
    + exact Hnocoll_Rv_payload.
    + intros x Hin.
      unfold sctx_add_params, ctx_add_params in Hin.
      rewrite ctx_names_app in Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      * eapply alpha_rename_params_names_in_used.
        -- exact Hrename_params.
        -- exact Hin_params.
      * eapply alpha_rename_params_used_extends.
        -- exact Hrename_params.
        -- apply in_or_app. right. apply in_or_app. right.
           apply Hused_prefix. apply Hctx_used. exact Hin_tail.
    + intros x Hin.
      destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _
        Hrename_params _ Hin) as [Hin_params | Hin_range].
      * eapply alpha_rename_params_names_in_used.
        -- exact Hrename_params.
        -- exact Hin_params.
      * eapply alpha_rename_params_used_extends.
        -- exact Hrename_params.
        -- apply in_or_app. right. apply in_or_app. right.
           apply Hused_prefix. apply Hrange_used. exact Hin_range.
    + intros x Hfree Hrange.
      destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _
        Hrename_params _ Hrange) as [Hin_params | Hin_range].
      * eapply alpha_rename_params_names_fresh_used.
        -- exact Hrename_params.
        -- exact Hin_params.
        -- apply in_or_app. right. apply in_or_app. left. exact Hfree.
	      * eapply lookup_expr_branch_disjoint_alpha.
	        -- exact H4.
        -- exact Hdisj.
        -- exact Hfree.
        -- exact Hin_range.
    + exact Hrename_branch.
    + destruct (IHHtyped_tail Hexpr Hctx HnsR HnsRout HRr Hkeys Hroots
        Hroots_scrut_named HnocollR HnocollRout Hroots_scrutr Hdisj Hrename HRout)
        as [Σrs [rootssr [Htail_r [Hctx_tail Hroots_tail]]]].
      pose (Rv_r := root_env_remove_match_params psr Rvr).
      pose (Σv_r := sctx_remove_params psr Σvr).
      assert (Hparams_ok_r :
        params_ok_sctx_b env psr Σvr = true).
	      { eapply alpha_rename_params_params_ok_sctx_b_forward_gen.
	        - exact Hrename_params.
	        - rewrite <- params_ctx_names_param_names.
	          eapply params_names_nodup_b_sound. exact H1.
	        - intros x Hin.
	          rewrite <- params_ctx_names_param_names in Hin.
	          rewrite (match_binder_params_names _ _ _ H0) in Hin.
          apply in_or_app. left. exact Hin.
        - intros x Hin.
          apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hrange_used. exact Hin.
	        - exact Hctx_branch.
	        - exact H7. }
      assert (Hrootsr_outer :
        root_set_equiv rootsr (root_set_rename rho roots)).
	      { eapply root_set_equiv_trans.
	        - exact Hrootsr.
	        - eapply alpha_rename_params_root_set_rename_excluded.
	          + exact Hrename_params.
	          + exact H8. }
      assert (Hroots_branch_named :
        root_set_sctx_roots_named roots (sctx_add_params ps Σ)).
      { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
          as [Hroots_env _].
	        destruct (Hroots_env R_payload (sctx_add_params ps Σ) e T
	          Σv_payload Rv_payload roots H6 Hns_payload) as [_ Hroots_branch].
        - subst R_payload.
          apply root_env_sctx_roots_named_add_params_roots_same; assumption.
        - eapply root_set_sctx_roots_named_same_bindings.
          + apply sctx_same_bindings_sym.
	            eapply typed_env_structural_same_bindings.
	            eapply typed_env_roots_structural.
	            eapply typed_env_roots_shadow_safe_roots. exact H6.
          + exact Hroots_branch. }
	      assert (Hns_Rv_payload : root_env_no_shadow Rv_payload).
	      { eapply typed_env_roots_no_shadow.
	        - eapply typed_env_roots_shadow_safe_roots. exact H6.
	        - exact Hns_payload. }
      assert (Hroots_Rv_payload :
        root_env_sctx_roots_named Rv_payload (sctx_add_params ps Σ)).
      { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
          as [Hroots_env _].
	        destruct (Hroots_env R_payload (sctx_add_params ps Σ) e T
	          Σv_payload Rv_payload roots H6 Hns_payload) as [Hroots_env_branch _].
        - subst R_payload.
          apply root_env_sctx_roots_named_add_params_roots_same; assumption.
        - eapply root_env_sctx_roots_named_same_bindings.
          + apply sctx_same_bindings_sym.
	            eapply typed_env_structural_same_bindings.
	            eapply typed_env_roots_structural.
	            eapply typed_env_roots_shadow_safe_roots. exact H6.
          + exact Hroots_env_branch. }
      assert (Hkeys_Rv :
        root_env_sctx_keys_named Rv (sctx_add_params ps Σ)).
      { eapply root_env_sctx_keys_named_add_params_env.
        eapply root_env_sctx_keys_named_same_bindings.
        - apply sctx_same_bindings_sym.
          eapply sctx_same_bindings_remove_added_params.
          apply sctx_same_bindings_refl.
	        - rewrite H9.
	          eapply root_env_sctx_keys_named_remove_match_params.
          + exact Hns_Rv_payload.
          + exact Hkeys_Rv_payload. }
      assert (Hroots_Rv :
        root_env_sctx_roots_named Rv (sctx_add_params ps Σ)).
      { eapply root_env_sctx_roots_named_add_params_env.
        eapply root_env_sctx_roots_named_same_bindings.
        - apply sctx_same_bindings_sym.
          eapply sctx_same_bindings_remove_added_params.
          apply sctx_same_bindings_refl.
	        - rewrite H9.
	          eapply root_env_sctx_roots_named_remove_match_params.
	          + exact Hns_Rv_payload.
	          + rewrite <- H9. exact H10.
	          + exact Hroots_Rv_payload. }
	      assert (Hroot_none_Rv : root_env_lookup_params_none_b ps Rv = true).
	      { rewrite H9.
	        apply root_env_lookup_params_none_b_remove_match_params.
	        exact Hns_Rv_payload. }
      assert (Hnocoll_params_Rv_payload :
        forall x, In x (ctx_names (params_ctx ps)) ->
          rename_no_collision_for rho_branch x (root_env_names Rv_payload)).
      { intros x Hin.
        eapply alpha_rename_params_rename_no_collision_for_params.
        - exact Hrename_params.
	        - exact Hctx.
	        - exact Hns_Rv_payload.
	        - exact Hkeys_Rv_payload.
	        - exact H1.
        - intros y Hy. apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hctx_used. exact Hy.
        - intros y Hy. apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hrange_used. exact Hy.
        - exact Hnocoll_Rv_payload.
        - exact Hin. }
	      assert (HRv_r_branch :
	        root_env_equiv Rv_r (root_env_rename rho_branch Rv)).
	      { unfold Rv_r. rewrite H9.
	        eapply alpha_rename_params_root_env_remove_match_params_full_rename_equiv.
	        - exact Hrename_params.
	        - exact H1.
        - exact Hns_Rv_payload.
        - exact HnsRvr.
        - exact HRvr.
        - exact Hnocoll_Rv_payload.
        - exact Hnocoll_params_Rv_payload.
        - intros x Hin. reflexivity. }
	      assert (Henv_excl_r : root_env_excludes_params psr Rv_r).
	      { eapply alpha_rename_params_root_env_excludes_params_rename.
	        - exact Hrename_params.
	        - exact Hctx.
        - exact HnsRv.
	        - exact Hkeys_Rv.
	        - exact Hroots_Rv.
	        - exact Hroot_none_Rv.
	        - exact H10.
        - exact HRv_r_branch.
        - intros x Hin. apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hctx_used. exact Hin.
	        - intros x Hin. apply in_or_app. right. apply in_or_app. right.
	          apply Hused_prefix. apply Hrange_used. exact Hin. }
	      exists (Σv_r :: Σrs), (rootsr :: rootssr).
	      split.
	      * eapply TERSMatchTail_Cons.
	        -- exact Hbinders_r.
	        -- unfold match_payload_params. exact Hparams_r.
        -- exact Hparams_nodup_r.
        -- exact Hctx_none_r.
        -- exact Hroot_none_r.
        -- exact Hlookup_r.
        -- reflexivity.
        -- exact Htyped_branch_r.
        -- exact Hparams_ok_r.
        -- eapply alpha_rename_params_roots_exclude_params_rename.
           ++ exact Hrename_params.
           ++ exact Hctx.
           ++ exact Hroots_branch_named.
	           ++ exact H8.
           ++ exact Hrootsr.
           ++ intros x Hin. apply in_or_app. right. apply in_or_app. right.
              apply Hused_prefix. apply Hctx_used. exact Hin.
           ++ intros x Hin. apply in_or_app. right. apply in_or_app. right.
              apply Hused_prefix. apply Hrange_used. exact Hin.
	        -- reflexivity.
	        -- exact Henv_excl_r.
	        -- reflexivity.
	        -- exact H12.
	        -- eapply root_env_equiv_trans.
	           ++ exact HRv_r_branch.
	           ++ eapply root_env_equiv_trans.
	              ** eapply alpha_rename_params_root_env_rename_excluded.
	                 --- exact Hrename_params.
	                 --- exact HnsRv.
	                 --- exact Hroot_none_Rv.
	                 --- exact H10.
	              ** eapply root_env_equiv_trans.
	                 --- eapply root_env_equiv_rename with (rho := rho).
	                     +++ exact H13.
                     +++ exact HnsRv.
                     +++ exact HnsRout.
                     +++ exact HnocollRv.
                     +++ exact HnocollRout.
                 --- apply root_env_equiv_sym. exact HRout.
        -- exact Htail_r.
      * split.
        -- constructor.
           ++ subst Σv_r Σv.
              eapply alpha_rename_params_ctx_alpha_remove.
              ** exact Hrename_params.
              ** exact Hctx_branch.
           ++ assumption.
        -- constructor; assumption.
Qed.

Lemma alpha_rename_typed_env_roots_call_forward :
  forall env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
      typed_env_roots env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECall fname args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECall fname args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (fn_params fdef))
    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots _ _ _ _ _ args
          (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TER_Call; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_struct_forward :
  forall env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots env Ω n R Σ (EStruct sname lts args fields)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EStruct sname lts args fields))
    (rename_range rho) ->
  alpha_rename_expr rho used (EStruct sname lts args fields) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
              : list (string * expr) * list ident :=
              match fields0 with
              | [] => ([], used0)
              | (fname, e) :: rest =>
                  let (e', used1) := alpha_rename_expr rho used0 e in
                  let (rest', used2) := go used1 rest in
                  ((fname, e') :: rest', used2)
              end) used fields) as [fieldsr used_fields] eqn:Hfields.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_fields_roots_forward
    env Ω n rho lts args R Rr Σ Σr fields fieldsr used used_fields
    (Program.struct_fields sdef) Σ' R' roots)
    as [Σr' [Rr' [rootsr
      [Hfields_r [Hctx_r [HnsRr' [HRr' Hroots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_fields_roots _ _ _ lts args _ _ fields
          (Program.struct_fields sdef) _ _ roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hfields.
  - exists Σr', Rr', rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TER_Struct; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + exact Hroots.
Qed.

Lemma alpha_rename_typed_env_roots_call_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (ECall fname args)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECall fname args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECall fname args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_shadow_safe_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (fn_params fdef))
    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots_shadow_safe _ _ _ _ _ args
          (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_Call; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_struct_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ
    (EStruct sname lts args fields) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EStruct sname lts args fields))
    (rename_range rho) ->
  alpha_rename_expr rho used (EStruct sname lts args fields) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
              : list (string * expr) * list ident :=
              match fields0 with
              | [] => ([], used0)
              | (fname, e) :: rest =>
                  let (e', used1) := alpha_rename_expr rho used0 e in
                  let (rest', used2) := go used1 rest in
                  ((fname, e') :: rest', used2)
              end) used fields) as [fieldsr used_fields] eqn:Hfields.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_fields_roots_shadow_safe_forward
    env Ω n rho lts args R Rr Σ Σr fields fieldsr used used_fields
    (Program.struct_fields sdef) Σ' R' roots)
    as [Σr' [Rr' [rootsr
      [Hfields_r [Hctx_r [HnsRr' [HRr' Hroots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_fields_roots_shadow_safe _ _ _ lts args _ _ fields
          (Program.struct_fields sdef) _ _ roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hfields.
  - exists Σr', Rr', rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Struct; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + exact Hroots.
Qed.

Lemma alpha_rename_typed_env_roots_call_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (ECall fname args)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECall fname args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECall fname args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (fn_params fdef))
    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots_shadow_safe _ _ _ _ _ args
          (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_Call; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_call_generic_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname type_args args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (ECallGeneric fname type_args args)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECallGeneric fname type_args args))
    (rename_range rho) ->
  alpha_rename_expr rho used (ECallGeneric fname type_args args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname type_args args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (apply_type_params type_args (fn_params fdef)))
    (apply_lt_params σ (apply_type_params type_args (fn_params fdef))) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots_shadow_safe _ _ _ _ _ args
          (apply_lt_params σ (apply_type_params type_args (fn_params fdef)))
          _ _ arg_roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_CallGeneric; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_call_expr_fn_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr callee args er used used' T Σ' R' roots,
  (* IH for callee *)
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa callee T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr callee) (rename_range rho) ->
      alpha_rename_expr rho used0 callee = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (* IH for args *)
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECallExpr callee args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECallExpr callee args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr callee args er used used' T Σ' R' roots
    Hcallee_ih Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  simpl in Hdisj.
  destruct (alpha_rename_expr rho used callee) as [callee_r used_callee] eqn:Hcallee_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used_callee args) as [argsr used_args] eqn:Hargs_rename.
  injection Hrename as <- <-.
  destruct (disjoint_names_app_l (free_vars_expr callee)
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args) (rename_range rho) Hdisj) as [Hdisj_callee Hdisj_args].
  inversion Htyped; subst.
  - (* TERS_CallExpr_MakeClosure *)
    simpl in Hcallee_rename; injection Hcallee_rename as <- <-.
    destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
      env Ω n rho R Rr Σ Σr args argsr used used_args
      (apply_lt_params σ (fn_params fdef))
      (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
      as [Σr' [Rr' [arg_rootsr
        [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
    + exact Hexpr.
    + match goal with
      | H : typed_args_roots_shadow_safe _ _ _ _ _ args
            (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
          exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact Hkeys.
    + exact Hroots.
    + exact HnocollR.
    + exact HnocollR'.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_args.
    + apply params_alpha_refl.
    + exact Hargs_rename.
    + exists Σr', Rr', (root_sets_union arg_rootsr).
      split; [| split; [| split; [| split]]].
      * eapply TERS_CallExpr_MakeClosure; eauto.
        eapply check_make_closure_captures_sctx_with_env_alpha_forward;
          eauto using disjoint_names_app_l.
      * exact Hctx_r.
      * exact HnsRr'.
      * exact HRr'.
      * eapply root_sets_union_rename_equiv. exact Harg_roots.
  - (* TERS_CallExpr_Fn *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys param_tys) (params_of_tys param_tys) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys param_tys) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Fn.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_Closure *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys param_tys) (params_of_tys param_tys) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys param_tys) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Closure.
          - intros fname caps Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname caps used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_TypeForall: same structure as Fn/Closure *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys (map (subst_type_params_ty type_args) param_tys)) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_TypeForall.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_MixedForall: same structure as TypeForall *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys)))
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys))) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys
                (map (open_bound_ty σ)
                  (map (subst_type_params_ty type_args) param_tys))) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_MixedForall.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_Forall_Fn: same structure as TypeForall *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys (map (open_bound_ty σ) param_tys))
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys (map (open_bound_ty σ) param_tys)) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Forall_Fn.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_Forall_Closure: same structure as Forall_Fn *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys (map (open_bound_ty σ) param_tys))
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys (map (open_bound_ty σ) param_tys)) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Forall_Closure.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
Qed.


Lemma alpha_rename_typed_env_roots_struct_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ
    (EStruct sname lts args fields) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EStruct sname lts args fields))
    (rename_range rho) ->
  alpha_rename_expr rho used (EStruct sname lts args fields) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
              : list (string * expr) * list ident :=
              match fields0 with
              | [] => ([], used0)
              | (fname, e) :: rest =>
                  let (e', used1) := alpha_rename_expr rho used0 e in
                  let (rest', used2) := go used1 rest in
                  ((fname, e') :: rest', used2)
              end) used fields) as [fieldsr used_fields] eqn:Hfields.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_fields_roots_shadow_safe_support_forward
    env Ω n rho lts args R Rr Σ Σr fields fieldsr used used_fields
    (Program.struct_fields sdef) Σ' R' roots)
    as [Σr' [Rr' [rootsr
      [Hfields_r [Hctx_r [HnsRr' [HRr' Hroots_equiv]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_fields_roots_shadow_safe _ _ _ lts args _ _ fields
          (Program.struct_fields sdef) _ _ roots |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hfields.
  - exists Σr', Rr', rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Struct; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + exact Hroots_equiv.
Qed.

Lemma alpha_rename_typed_env_roots_shadow_safe_full_support_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  assert (Hsize : forall fuel env Ω n rho R Rr Σ Σr e er used used'
      T Σ' R' roots,
    expr_size e < fuel ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots)).
  {
    induction fuel as [| fuel IH]; intros env Ω n rho R Rr Σ Σr e er
      used used' T Σ' R' roots Hlt Htyped Hctx HnsR HnsRr HRr Hkeys
      Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
    - lia.
    - destruct e.
      + eapply alpha_rename_typed_env_roots_trivial_shadow_safe_support_forward;
          try eassumption.
        left. reflexivity.
      + eapply alpha_rename_typed_env_roots_trivial_shadow_safe_support_forward;
          try eassumption.
        right. eexists. reflexivity.
      + eapply alpha_rename_typed_env_roots_var_shadow_safe_support_forward;
          eauto.
      + eapply (alpha_rename_typed_env_roots_let_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr m i t e1 e2 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e1 er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * intros xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
            roots1r T2 Σ2 R2 roots2 Hxr Hused2 He2 Htyped2 Hctx_body
            Hns_add HnsR1r Hlookup_x Hroots1_excl Henv1_excl HnocollR1
            Hnocoll_remove Hroots2_excl Henv2_excl HR1r Hroots1r HkeysR1
            HrootsR1 Hroots1_named Hctx_used2 Hrange_used2 Hdisj2.
          destruct (ctx_alpha_add_fresh_inv rho Σ1 Σ1r i xr t m Hctx_body)
            as [Hctx1 [Hfresh_ctx _]].
          assert (HnsR1 : root_env_no_shadow R1).
          { unfold root_env_no_shadow, root_env_add in Hns_add.
            simpl in Hns_add. inversion Hns_add; assumption. }
          destruct (root_env_sctx_support_fresh_renamed_let_init rho R1 R1r
            roots1 roots1r Σ1 Σ1r xr Hctx1 HnsR1 HnsR1r HR1r
            Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
            as [Hlookup_xr [Hroots1r_excl Henv1r_excl]].
          assert (Hns_add_r :
            root_env_no_shadow (root_env_add xr roots1r R1r)).
          { eapply root_env_no_shadow_add.
            - exact HnsR1r.
            - exact Hlookup_xr. }
          assert (HRadd :
            root_env_equiv (root_env_add xr roots1r R1r)
              (root_env_rename ((i, xr) :: rho)
                (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
          assert (Hkeys_add :
            root_env_sctx_keys_named (root_env_add i roots1 R1)
              (sctx_add i t m Σ1)).
          { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
          assert (Hroots_add :
            root_env_sctx_roots_named (root_env_add i roots1 R1)
              (sctx_add i t m Σ1)).
          { apply root_env_sctx_roots_named_add_binding; assumption. }
          assert (Hnocoll_add :
            rename_no_collision_on ((i, xr) :: rho)
              (root_env_names (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_no_collision_on;
              eassumption. }
          assert (HnsR2 : root_env_no_shadow R2).
          { eapply typed_env_roots_no_shadow.
            - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
            - exact Hns_add. }
          assert (HkeysR2 : root_env_sctx_keys_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
              as [Hkeys_env _].
            eapply Hkeys_env; eassumption. }
          assert (HrootsR2 : root_env_sctx_roots_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i t m Σ1) e2 T2 Σ2 R2 roots2)
              as [Hroots_env2 _].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_env2. }
          assert (Hroots2_named : root_set_sctx_roots_named roots2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i t m Σ1) e2 T2 Σ2 R2 roots2)
              as [_ Hroots_set2].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_set2. }
          assert (Hsame_body :
            sctx_same_bindings (sctx_add i t m Σ1) Σ2).
          { eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
          assert (HnocollR2_cons :
            rename_no_collision_on ((i, xr) :: rho) (root_env_names R2)).
          { eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings.
            - exact Hctx1.
            - exact HnsR2.
            - exact HkeysR2.
            - exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hnocoll_remove. }
          destruct (IH env Ω n ((i, xr) :: rho)
            (root_env_add i roots1 R1) (root_env_add xr roots1r R1r)
            (sctx_add i t m Σ1) (sctx_add xr t m Σ1r)
            e2 e2r used2 used3 T2 Σ2 R2 roots2)
            as [Σ2r [R2r [roots2r
              [Htyped2r [Hctx2r [HnsR2r [HR2r Hroots2r_cons]]]]]]].
          { simpl in Hlt. lia. }
          { exact Htyped2. }
          { exact Hctx_body. }
          { exact Hns_add. }
          { exact Hns_add_r. }
          { exact HRadd. }
          { exact Hkeys_add. }
          { exact Hroots_add. }
          { exact Hnocoll_add. }
          { exact HnocollR2_cons. }
          { exact Hctx_used2. }
          { exact Hrange_used2. }
          { exact Hdisj2. }
          { exact He2. }
          assert (Hnocoll_x :
            rename_no_collision_for ((i, xr) :: rho) i (root_env_names R2)).
          { eapply root_env_sctx_keys_named_added_no_collision_for_head.
            - exact Hctx1.
            - eapply root_env_sctx_keys_named_same_bindings.
              + apply sctx_same_bindings_sym. exact Hsame_body.
              + exact HkeysR2.
            - exact Hfresh_ctx. }
          assert (HRremove :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename rho (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_equiv;
              eassumption. }
          assert (Hroots2r :
            root_set_equiv roots2r (root_set_rename rho roots2)).
          { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
          assert (Hroots2r_excl : roots_exclude xr roots2r).
          { eapply roots_exclude_shadow_safe_rename_body.
            - exact Hctx1.
            - eapply root_set_sctx_roots_named_strip_added_same_bindings.
              + exact Hroots2_excl.
              + exact Hroots2_named.
              + exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hroots2r_cons.
            - exact Hroots2_excl. }
          assert (Hremove_ext :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename ((i, xr) :: rho) (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
              eassumption. }
          assert (Henv2r_excl :
            root_env_excludes xr (root_env_remove xr R2r)).
          { eapply root_env_excludes_shadow_safe_rename_body.
            - exact Hctx1.
            - apply root_env_no_shadow_remove. exact HnsR2.
            - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
                eassumption.
            - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
                eassumption.
            - exact Hfresh_ctx.
            - exact Hremove_ext.
            - exact Henv2_excl. }
	          exists Σ2r, R2r, roots2r.
	          refine (conj Hlookup_xr
	            (conj Hroots1r_excl
	            (conj Henv1r_excl
	            (conj Htyped2r
	            (conj Hctx2r
	            (conj HnsR2r
	            (conj HRremove
	            (conj Hroots2r
	            (conj Hroots2r_excl Henv2r_excl))))))))).
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_letinfer_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr m i e1 e2 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e1 er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * intros xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
            roots1r T2 Σ2 R2 roots2 Hxr Hused2 He2 Htyped2 Hctx_body
            Hns_add HnsR1r Hlookup_x Hroots1_excl Henv1_excl HnocollR1
            Hnocoll_remove Hroots2_excl Henv2_excl HR1r Hroots1r HkeysR1
            HrootsR1 Hroots1_named Hctx_used2 Hrange_used2 Hdisj2.
          destruct (ctx_alpha_add_fresh_inv rho Σ1 Σ1r i xr T1 m Hctx_body)
            as [Hctx1 [Hfresh_ctx _]].
          assert (HnsR1 : root_env_no_shadow R1).
          { unfold root_env_no_shadow, root_env_add in Hns_add.
            simpl in Hns_add. inversion Hns_add; assumption. }
          destruct (root_env_sctx_support_fresh_renamed_let_init rho R1 R1r
            roots1 roots1r Σ1 Σ1r xr Hctx1 HnsR1 HnsR1r HR1r
            Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
            as [Hlookup_xr [Hroots1r_excl Henv1r_excl]].
          assert (Hns_add_r :
            root_env_no_shadow (root_env_add xr roots1r R1r)).
          { eapply root_env_no_shadow_add.
            - exact HnsR1r.
            - exact Hlookup_xr. }
          assert (HRadd :
            root_env_equiv (root_env_add xr roots1r R1r)
              (root_env_rename ((i, xr) :: rho)
                (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
          assert (Hkeys_add :
            root_env_sctx_keys_named (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1)).
          { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
          assert (Hroots_add :
            root_env_sctx_roots_named (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1)).
          { apply root_env_sctx_roots_named_add_binding; assumption. }
          assert (Hnocoll_add :
            rename_no_collision_on ((i, xr) :: rho)
              (root_env_names (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_no_collision_on;
              eassumption. }
          assert (HnsR2 : root_env_no_shadow R2).
          { eapply typed_env_roots_no_shadow.
            - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
            - exact Hns_add. }
          assert (HkeysR2 : root_env_sctx_keys_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
              as [Hkeys_env _].
            eapply Hkeys_env; eassumption. }
          assert (HrootsR2 : root_env_sctx_roots_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1) e2 T2 Σ2 R2 roots2)
              as [Hroots_env2 _].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_env2. }
          assert (Hroots2_named : root_set_sctx_roots_named roots2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1) e2 T2 Σ2 R2 roots2)
              as [_ Hroots_set2].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_set2. }
          assert (Hsame_body :
            sctx_same_bindings (sctx_add i T1 m Σ1) Σ2).
          { eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
          assert (HnocollR2_cons :
            rename_no_collision_on ((i, xr) :: rho) (root_env_names R2)).
          { eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings.
            - exact Hctx1.
            - exact HnsR2.
            - exact HkeysR2.
            - exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hnocoll_remove. }
          destruct (IH env Ω n ((i, xr) :: rho)
            (root_env_add i roots1 R1) (root_env_add xr roots1r R1r)
            (sctx_add i T1 m Σ1) (sctx_add xr T1 m Σ1r)
            e2 e2r used2 used3 T2 Σ2 R2 roots2)
            as [Σ2r [R2r [roots2r
              [Htyped2r [Hctx2r [HnsR2r [HR2r Hroots2r_cons]]]]]]].
          { simpl in Hlt. lia. }
          { exact Htyped2. }
          { exact Hctx_body. }
          { exact Hns_add. }
          { exact Hns_add_r. }
          { exact HRadd. }
          { exact Hkeys_add. }
          { exact Hroots_add. }
          { exact Hnocoll_add. }
          { exact HnocollR2_cons. }
          { exact Hctx_used2. }
          { exact Hrange_used2. }
          { exact Hdisj2. }
          { exact He2. }
          assert (Hnocoll_x :
            rename_no_collision_for ((i, xr) :: rho) i (root_env_names R2)).
          { eapply root_env_sctx_keys_named_added_no_collision_for_head.
            - exact Hctx1.
            - eapply root_env_sctx_keys_named_same_bindings.
              + apply sctx_same_bindings_sym. exact Hsame_body.
              + exact HkeysR2.
            - exact Hfresh_ctx. }
          assert (HRremove :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename rho (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_equiv;
              eassumption. }
          assert (Hroots2r :
            root_set_equiv roots2r (root_set_rename rho roots2)).
          { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
          assert (Hroots2r_excl : roots_exclude xr roots2r).
          { eapply roots_exclude_shadow_safe_rename_body.
            - exact Hctx1.
            - eapply root_set_sctx_roots_named_strip_added_same_bindings.
              + exact Hroots2_excl.
              + exact Hroots2_named.
              + exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hroots2r_cons.
            - exact Hroots2_excl. }
          assert (Hremove_ext :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename ((i, xr) :: rho) (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
              eassumption. }
          assert (Henv2r_excl :
            root_env_excludes xr (root_env_remove xr R2r)).
          { eapply root_env_excludes_shadow_safe_rename_body.
            - exact Hctx1.
            - apply root_env_no_shadow_remove. exact HnsR2.
            - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
                eassumption.
            - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
                eassumption.
            - exact Hfresh_ctx.
            - exact Hremove_ext.
            - exact Henv2_excl. }
	          exists Σ2r, R2r, roots2r.
	          refine (conj Hlookup_xr
	            (conj Hroots1r_excl
	            (conj Henv1r_excl
	            (conj Htyped2r
	            (conj Hctx2r
	            (conj HnsR2r
	            (conj HRremove
	            (conj Hroots2r
	            (conj Hroots2r_excl Henv2r_excl))))))))).
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply alpha_rename_typed_env_roots_fn_shadow_safe_support_forward;
          eauto.
	      + injection Hrename as <- <-.
	        inversion Htyped; subst.
	        * do 3 eexists.
	          repeat split; try exact Hctx; try exact HnsRr; try exact HRr;
	            try apply root_set_equiv_refl.
	          eapply TERS_MakeClosure; eauto.
	          eapply check_make_closure_captures_sctx_with_env_alpha_forward; eauto.
	        * do 3 eexists.
	          repeat split; try exact Hctx; try exact HnsRr; try exact HRr;
	            try apply root_set_equiv_refl.
	          eapply TERS_MakeClosure_Static; eauto.
	          eapply check_make_closure_captures_sctx_alpha_forward; eauto.
      + eapply alpha_rename_typed_env_roots_place_shadow_safe_support_forward;
          eauto.
	      + eapply (alpha_rename_typed_env_roots_call_shadow_safe_support_forward
	          env Ω n rho R Rr Σ Σr i l er used used' T Σ' R' roots).
	        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
	            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_call_arg_lt i l e0 Hin) as Harg_lt.
            simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
	        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * exact Hrename.
	      + eapply (alpha_rename_typed_env_roots_call_generic_shadow_safe_support_forward
	          env Ω n rho R Rr Σ Σr i l l0 er used used' T Σ' R' roots).
	        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
	            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
	            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
	          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
	            T0 Σa' R0' roots0).
	          { pose proof (expr_size_call_generic_arg_lt i l l0 e0 Hin)
	              as Harg_lt.
	            simpl in *. lia. }
	          all: eassumption.
	        * exact Htyped.
	        * exact Hctx.
	        * exact HnsR.
	        * exact HnsRr.
	        * exact HRr.
	        * exact Hkeys.
	        * exact Hroots.
	        * exact HnocollR.
	        * exact HnocollR'.
	        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * exact Hrename.
	      + eapply alpha_rename_typed_env_roots_call_expr_fn_shadow_safe_support_forward.
        * (* callee IH *)
          intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
            simpl in *. lia. }
          all: eassumption.
        * (* args IH *)
          intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_callexpr_arg_lt e l e0 Hin) as Harg_lt.
            simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_struct_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr s l l0 l1 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_struct_field_snd_lt s l l0 l1 e0 Hin)
              as Hfield_lt.
            simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * exact Hrename.
	      + simpl in Hrename.
	        destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
	                    : list expr * list ident :=
	                    match args0 with
	                    | [] => ([], used0)
	                    | arg :: rest =>
	                        let (arg', used1) := alpha_rename_expr rho used0 arg in
	                        let (rest', used2) := go used1 rest in
	                        (arg' :: rest', used2)
	                    end) used l1) as [payloadsr used_payloads] eqn:Hpayloads.
	        injection Hrename as <- <-.
	        inversion Htyped; subst.
	        destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
	          env Ω n rho R Rr Σ Σr l1 payloadsr used used_payloads
	          (params_of_tys
	            (map (instantiate_enum_variant_field_ty l l0)
	              (enum_variant_fields vdef)))
	          (params_of_tys
	            (map (instantiate_enum_variant_field_ty l l0)
	              (enum_variant_fields vdef))) Σ' R' payload_roots)
	          as [Σr' [Rr' [payload_rootsr
	            [Hpayloads_r [Hctx_r [HnsRr' [HRr' Hpayload_roots]]]]]]].
	        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
	            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
	            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
	          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
	            T0 Σa' R0' roots0).
	          { pose proof (expr_size_enum_payload_lt s s0 l l0 l1 e0 Hin)
	              as Hpayload_lt.
	            simpl in *. lia. }
	          all: eassumption.
	        * match goal with
	          | H : typed_args_roots_shadow_safe _ _ _ _ _ l1
	                (params_of_tys
	                  (map (instantiate_enum_variant_field_ty l l0)
	                    (enum_variant_fields vdef))) _ _ payload_roots |- _ =>
	              exact H
	          end.
	        * exact Hctx.
	        * exact HnsR.
	        * exact HnsRr.
	        * exact HRr.
	        * exact Hkeys.
	        * exact Hroots.
	        * exact HnocollR.
	        * exact HnocollR'.
	        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * apply params_alpha_refl.
		        * exact Hpayloads.
		        * exists Σr', Rr', (root_sets_union payload_rootsr).
		          split; [| split; [| split; [| split]]].
		          -- eapply TERS_Enum; eauto.
		          -- exact Hctx_r.
		          -- exact HnsRr'.
		          -- exact HRr'.
		          -- eapply root_sets_union_rename_equiv. exact Hpayload_roots.
		      + simpl in Hrename.
		        destruct (alpha_rename_expr rho used e) as [scrutr used_scrut] eqn:Hscrut.
		        destruct ((fix go
		                    (used0 : list ident)
		                    (branches0 : list (string * list ident * expr)) {struct branches0}
		                    : list (string * list ident * expr) * list ident :=
		                    match branches0 with
		                    | [] => ([], used0)
		                    | (variant_name, binders, e0) :: rest =>
		                        let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
		                        let '(binders', rho_branch, used1) :=
		                          alpha_rename_idents rho binder_seed binders in
		                        let (e0', used2) := alpha_rename_expr rho_branch used1 e0 in
		                        let (rest', used3) := go used2 rest in
		                        ((variant_name, binders', e0') :: rest', used3)
		                    end) used_scrut l) as [branchesr used_branches] eqn:Hbranches.
		        injection Hrename as <- <-.
		        destruct (disjoint_names_app_l (free_vars_expr e)
		          ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
		              match branches0 with
		              | [] => []
		              | (_, _, e0) :: rest => free_vars_expr e0 ++ go rest
		              end) l) (rename_range rho) Hdisj)
		          as [Hdisj_scrut Hdisj_branches].
		        inversion Htyped; subst.
		        assert (HnsR1 : root_env_no_shadow R1).
		        { eapply typed_env_roots_no_shadow.
		          - eapply typed_env_roots_shadow_safe_roots. eassumption.
		          - exact HnsR. }
			        match goal with
			        | Htail0 : typed_match_tail_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _
			            ?Rout _ _ _ |- _ =>
			            assert (HnsRout : root_env_no_shadow Rout)
			        end.
				        { match goal with
				          | Hpayload : ?Rpayload =
		              root_env_add_params_roots_same ?ps ?roots R1,
		            Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
		              ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
		              ?roots_head0,
		            Hout : ?Rout = root_env_remove_match_params ?ps
		              ?Rhead_payload |- root_env_no_shadow ?Rout =>
		              rewrite Hout;
		              apply root_env_remove_match_params_no_shadow;
		                eapply typed_env_roots_no_shadow;
		              [eapply typed_env_roots_shadow_safe_roots; exact Hhead
		              | subst Rpayload;
		                eapply root_env_add_params_roots_same_no_shadow; eauto]
		          | Hhead : typed_env_roots_shadow_safe env Ω n
		              (root_env_add_params_roots_same ?ps ?roots R1)
		              ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
		              ?roots_head0
		            |- root_env_no_shadow
		                 (root_env_remove_match_params ?ps ?Rhead_payload) =>
		              apply root_env_remove_match_params_no_shadow;
		              eapply typed_env_roots_no_shadow;
		              [eapply typed_env_roots_shadow_safe_roots; exact Hhead
		              | eapply root_env_add_params_roots_same_no_shadow; eauto]
		          end. }
		        assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
		        { eapply rename_no_collision_on_weaken_names.
			          - exact HnocollR'.
			          - intros x Hin.
			            match goal with
			            | Hpayload : ?Rpayload =
			                root_env_add_params_roots_same ?ps ?roots R1,
			              Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
			                ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
			                ?roots_head0,
			              Hout : ?Rout = root_env_remove_match_params ?ps
			                ?Rhead_payload,
			              Hnone : root_env_lookup_params_none_b ?ps R1 = true |- _ =>
			                rewrite Hout;
			                eapply root_env_remove_match_params_preserve_name_not_params
			            | Hhead : typed_env_roots_shadow_safe env Ω n
			                (root_env_add_params_roots_same ?ps ?roots R1)
			                ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
			                ?roots_head0,
			              Hnone : root_env_lookup_params_none_b ?ps R1 = true
			                |- In x (root_env_names
			                     (root_env_remove_match_params ?ps ?Rhead_payload)) =>
			                eapply root_env_remove_match_params_preserve_name_not_params
			            end.
			            + intros y Hy Heq. subst y.
			              match goal with
			              | Hnone : root_env_lookup_params_none_b ?ps R1 = true |- _ =>
			                  pose proof (root_env_lookup_params_none_b_not_in
			                    _ _ _ Hnone Hy) as Hnot;
			                  apply Hnot; exact Hin
			              end.
			            + eapply typed_env_roots_root_env_names_subset.
			              * eapply typed_env_roots_shadow_safe_roots.
			                match goal with
			                | Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
			                    ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
			                    ?roots_head0 |- _ => exact Hhead
			                end.
			              * match goal with
			                | Hpayload : ?Rpayload =
			                    root_env_add_params_roots_same ?ps ?roots R1 |- _ =>
			                    subst Rpayload;
			                    apply root_env_add_params_roots_same_preserve_name;
			                    exact Hin
			                | |- In x (root_env_names
			                    (root_env_add_params_roots_same ?ps ?roots R1)) =>
			                    apply root_env_add_params_roots_same_preserve_name;
			                    exact Hin
			                end. }
		        destruct (IH env Ω n rho R Rr Σ Σr e scrutr used used_scrut
		          T_scrut Σ1 R1 roots_scrut)
		          as [Σr1 [Rr1 [roots_scrutr
		            [Hscrut_r [Hctx1_r [HnsRr1 [HRr1 Hroots_scrut]]]]]]].
		        * simpl in *. lia.
		        * match goal with
		          | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                Σ1 R1 roots_scrut |- _ => exact H
		          end.
		        * exact Hctx.
		        * exact HnsR.
		        * exact HnsRr.
		        * exact HRr.
		        * exact Hkeys.
		        * exact Hroots.
		        * exact HnocollR.
		        * exact HnocollR1.
		        * exact Hctx_used.
		        * exact Hrange_used.
		        * exact Hdisj_scrut.
		        * exact Hscrut.
		        * assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used_scrut).
		          { intros y Hy.
		            eapply alpha_rename_expr_used_extends.
		            - exact Hscrut.
		            - apply Hctx_used.
		              rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
		              + exact Hy.
		              + eapply typed_env_structural_same_bindings.
		                eapply typed_env_roots_structural.
		                eapply typed_env_roots_shadow_safe_roots. exact Hscrut_r. }
		          assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used_scrut).
		          { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
			          destruct (alpha_rename_match_branches_lookup_payload_forward
			            rho used_scrut l branchesr used_branches
			            (Program.enum_variant_name v_head) binders_head e_head
			            Hbranches
			            ltac:(match goal with
			              | H : lookup_expr_branch_binders
			                      (Program.enum_variant_name v_head) l =
			                    Some binders_head |- _ => exact H
			            end)
		            ltac:(match goal with
		              | H : lookup_expr_branch (Program.enum_variant_name v_head) l =
		                    Some e_head |- _ => exact H
		            end))
		            as [binders_head_r [rho_head [e_headr
		              [used_head_pre [used_head [used_head_out
		                [Hbinders_head_r [Hlookup_head_r
		                  [Hrename_head_binders [Hrename_head
		                    Hused_head_pre]]]]]]]]]].
			          pose proof (lookup_expr_branch_binders_expr_in_alpha _ _ _ _
			            ltac:(match goal with
			              | H : lookup_expr_branch_binders
			                      (Program.enum_variant_name v_head) l =
			                    Some binders_head |- _ => exact H
			            end)
		            ltac:(match goal with
		              | H : lookup_expr_branch (Program.enum_variant_name v_head) l =
		                    Some e_head |- _ => exact H
		            end)) as Hhead_in.
			          match goal with
			          | H : match_payload_params binders_head lts args v_head =
			                infer_ok ps_head |- _ =>
			              destruct (match_binder_params_alpha_rename_idents
			                rho (binders_head ++ free_vars_expr e_head ++ used_head_pre)
			                binders_head binders_head_r rho_head used_head
		                (instantiate_enum_variant_field_tys lts args v_head)
		                ps_head Hrename_head_binders H)
		              as [ps_head_r [Hparams_head_r [Hparams_head_alpha
		                Hrename_head_params]]]
		          end.
		          assert (Hparams_head_nodup_r :
		            params_names_nodup_b ps_head_r = true).
		          { apply params_names_nodup_b_complete_alpha.
		            rewrite (match_binder_params_names _ _ _ Hparams_head_r).
		            eapply alpha_rename_idents_outputs_nodup.
		            exact Hrename_head_binders. }
		          assert (Hctx_head_none_r :
		            ctx_lookup_params_none_b ps_head_r Σr1 = true).
		          { eapply ctx_lookup_params_none_b_fresh_used
		              with (used := used_head_pre).
		            - intros y Hy.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - rewrite (match_binder_params_names _ _ _ Hparams_head_r).
		              eapply Forall_fresh_weaken.
		              + intros y Hy.
		                apply in_or_app. right. apply in_or_app. right.
		                exact Hy.
		              + eapply alpha_rename_idents_fresh_used.
		                exact Hrename_head_binders. }
		          assert (Hctx_head_payload :
		            ctx_alpha rho_head
		              (sctx_add_params ps_head Σ1)
		              (sctx_add_params ps_head_r Σr1)).
		          { unfold sctx_add_params, ctx_add_params.
		            eapply alpha_rename_params_ctx_alpha_extend_tail.
		            - exact Hrename_head_params.
		            - exact Hctx1_r.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hrange_used1. exact Hy. }
		          assert (Hkeys_R1 : root_env_sctx_keys_named R1 Σ1).
		          { match goal with
		            | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                  Σ1 R1 roots_scrut |- _ =>
		                destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                  as [Hkeys_env _];
		                eapply Hkeys_env; eassumption
		            end. }
		          assert (Hroots_R1 : root_env_sctx_roots_named R1 Σ1).
		          { match goal with
		            | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                  Σ1 R1 roots_scrut |- _ =>
		                destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                  as [Hroots_env _];
		                destruct (Hroots_env R Σ e T_scrut Σ1 R1 roots_scrut)
		                  as [Hroots_env1 _]; eauto
		            end. }
		          assert (Hkeys_Rr1 : root_env_sctx_keys_named Rr1 Σr1).
		          { eapply root_env_sctx_keys_named_rename; eassumption. }
		          assert (Hroots_Rr1 : root_env_sctx_roots_named Rr1 Σr1).
		          { eapply root_env_sctx_roots_named_rename.
		            - exact Hctx1_r.
		            - exact HnsR1.
		            - exact HRr1.
		            - exact Hroots_R1. }
		          assert (Hroots_scrut_named :
		            root_set_sctx_roots_named roots_scrut Σ1).
		          { match goal with
		            | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                  Σ1 R1 roots_scrut |- _ =>
		                destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                  as [Hroots_env _];
		                destruct (Hroots_env R Σ e T_scrut Σ1 R1 roots_scrut)
		                  as [_ Hroots_expr]; eauto
		            end. }
		          assert (Hroot_head_none_r :
		            root_env_lookup_params_none_b ps_head_r Rr1 = true).
		          { eapply root_env_lookup_params_none_b_from_sctx_keys;
		            eassumption. }
		          assert (Hroots_scrut_excl :
		            roots_exclude_params ps_head roots_scrut).
		          { unfold roots_exclude_params.
		            apply Forall_forall. intros x Hin.
		            eapply root_set_sctx_roots_named_fresh_exclude.
		            - exact Hroots_scrut_named.
		            - eapply ctx_lookup_params_none_b_not_in_names.
		              match goal with
		              | H : ctx_lookup_params_none_b ps_head Σ1 = true |- _ =>
		                  exact H
		              end.
		              exact Hin. }
		          assert (Henv_excl_R1 :
		            root_env_excludes_params ps_head R1).
		          { unfold root_env_excludes_params.
		            apply Forall_forall. intros x Hin.
		            eapply root_env_sctx_roots_named_fresh_excludes.
		            - exact Hroots_R1.
		            - eapply ctx_lookup_params_none_b_not_in_names.
		              match goal with
		              | H : ctx_lookup_params_none_b ps_head Σ1 = true |- _ =>
		                  exact H
		              end.
		              exact Hin. }
		          set (R_payload :=
		            root_env_add_params_roots_same ps_head roots_scrut R1) in *.
		          pose (R_payload_head_r :=
		            root_env_add_params_roots_same ps_head_r roots_scrutr Rr1).
		          assert (Hroots_scrutr_branch :
		            root_set_equiv roots_scrutr
		              (root_set_rename rho_head roots_scrut)).
		          { eapply root_set_equiv_trans.
		            - exact Hroots_scrut.
		            - apply root_set_equiv_sym.
		              eapply alpha_rename_params_root_set_rename_excluded.
		              + exact Hrename_head_params.
		              + exact Hroots_scrut_excl. }
		          assert (HRpayload_head_r :
		            root_env_equiv R_payload_head_r
		              (root_env_rename rho_head R_payload)).
		          { unfold R_payload_head_r. subst R_payload.
		            eapply alpha_rename_params_root_env_add_params_roots_same_rename_equiv.
		            - exact Hrename_head_params.
		            - exact HnsR1.
			            - assumption.
			            - assumption.
		            - exact Hroots_scrut_excl.
		            - exact Henv_excl_R1.
		            - exact HRr1.
		            - exact Hroots_scrutr_branch. }
		          assert (Hkeys_payload_head :
		            root_env_sctx_keys_named R_payload
		              (sctx_add_params ps_head Σ1)).
		          { subst R_payload.
		            apply root_env_sctx_keys_named_add_params_roots_same.
		            exact Hkeys_R1. }
		          assert (Hroots_payload_head :
		            root_env_sctx_roots_named R_payload
		              (sctx_add_params ps_head Σ1)).
		          { subst R_payload.
		            apply root_env_sctx_roots_named_add_params_roots_same;
		              assumption. }
		          assert (Hns_payload_head : root_env_no_shadow R_payload).
		          { subst R_payload.
		            eapply root_env_add_params_roots_same_no_shadow; eauto. }
		          assert (Hns_payload_head_r :
		            root_env_no_shadow R_payload_head_r).
		          { unfold R_payload_head_r.
		            eapply root_env_add_params_roots_same_no_shadow; eauto. }
		          assert (Hnocoll_payload_head :
		            rename_no_collision_on rho_head
		              (root_env_names R_payload)).
		          { subst R_payload.
		            eapply alpha_rename_params_root_env_add_params_roots_same_no_collision_on.
		            - exact Hrename_head_params.
		            - exact Hctx1_r.
		            - exact Hkeys_R1.
			            - assumption.
			            - assumption.
			            - assumption.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hrange_used1. exact Hy.
		            - exact HnocollR1. }
		          assert (Hnocoll_head_output :
		            rename_no_collision_on rho_head
		              (root_env_names R_head_payload)).
		          { eapply alpha_rename_params_root_env_remove_match_params_no_collision_on.
		            - exact Hrename_head_params.
		            - exact Hctx1_r.
		            - eapply typed_env_roots_no_shadow.
		              + eapply typed_env_roots_shadow_safe_roots.
		                match goal with
		                | H : typed_env_roots_shadow_safe env Ω n R_payload
		                      (sctx_add_params ps_head Σ1) e_head T_head
		                      Σ_head_payload R_head_payload roots_head |- _ =>
		                    exact H
		                end.
		              + exact Hns_payload_head.
		            - match goal with
		              | H : typed_env_roots_shadow_safe env Ω n R_payload
		                    (sctx_add_params ps_head Σ1) e_head T_head
		                    Σ_head_payload R_head_payload roots_head |- _ =>
		                  destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                    as [Hkeys_env _];
		                  eapply root_env_sctx_keys_named_same_bindings;
		                  [ apply sctx_same_bindings_sym;
		                    eapply typed_env_structural_same_bindings;
		                    eapply typed_env_roots_structural;
		                    eapply typed_env_roots_shadow_safe_roots; exact H
		                  | eapply Hkeys_env; eassumption ]
		              end.
		            - match goal
		              with H : params_names_nodup_b ps_head = true |- _ =>
		                exact H
		              end.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hrange_used1. exact Hy.
		            - exact HnocollR'. }
		             destruct (IH env Ω n rho_head R_payload R_payload_head_r
		               (sctx_add_params ps_head Σ1)
		               (sctx_add_params ps_head_r Σr1) e_head e_headr
		               used_head used_head_out T_head Σ_head_payload
		               R_head_payload roots_head)
		               as [Σ_head_payload_r [R_head_payload_r [roots_headr
		                 [Hhead_r [Hctx_head_payload_r
		                   [HnsR_head_payload_r [HRhead_payload_r
		                     Hroots_head]]]]]]].
			             ++ pose proof (expr_size_match_branch_lt e l
			                  (Program.enum_variant_name v_head) binders_head e_head
			                  Hhead_in).
		                simpl in *. lia.
		             ++ match goal with
		                | H : typed_env_roots_shadow_safe env Ω n R_payload
		                      (sctx_add_params ps_head Σ1) e_head T_head
		                      Σ_head_payload R_head_payload roots_head |- _ =>
		                    exact H
		                end.
		             ++ exact Hctx_head_payload.
		             ++ exact Hns_payload_head.
		             ++ exact Hns_payload_head_r.
		             ++ exact HRpayload_head_r.
		             ++ exact Hkeys_payload_head.
		             ++ exact Hroots_payload_head.
		             ++ exact Hnocoll_payload_head.
		             ++ exact Hnocoll_head_output.
		             ++ intros y Hy.
		                unfold sctx_add_params, ctx_add_params in Hy.
		                rewrite ctx_names_app in Hy.
		                apply in_app_or in Hy as [Hy_params | Hy_tail].
		                ** eapply alpha_rename_params_names_in_used.
		                   --- exact Hrename_head_params.
		                   --- exact Hy_params.
		                ** eapply alpha_rename_params_used_extends.
		                   --- exact Hrename_head_params.
		                   --- apply in_or_app. right. apply in_or_app. right.
		                       apply Hused_head_pre. apply Hctx_used1.
		                       exact Hy_tail.
		             ++ intros y Hy.
		                destruct (alpha_rename_params_range_ctx_or_tail
		                  _ _ _ _ _ _ Hrename_head_params _ Hy)
		                  as [Hy_params | Hy_range].
		                ** eapply alpha_rename_params_names_in_used.
		                   --- exact Hrename_head_params.
		                   --- exact Hy_params.
		                ** eapply alpha_rename_params_used_extends.
		                   --- exact Hrename_head_params.
		                   --- apply in_or_app. right. apply in_or_app. right.
		                       apply Hused_head_pre. apply Hrange_used1.
		                       exact Hy_range.
		             ++ intros y Hfree Hrange.
		                destruct (alpha_rename_params_range_ctx_or_tail
		                  _ _ _ _ _ _ Hrename_head_params _ Hrange)
		                  as [Hy_params | Hy_range].
		                ** eapply alpha_rename_params_names_fresh_used.
		                   --- exact Hrename_head_params.
		                   --- exact Hy_params.
		                   --- apply in_or_app. right. apply in_or_app. left.
		                       exact Hfree.
		                ** eapply lookup_expr_branch_disjoint_alpha.
		                   --- match goal with
		                       | H : lookup_expr_branch
		                               (Program.enum_variant_name v_head) l =
		                             Some e_head |- _ => exact H
		                       end.
		                   --- exact Hdisj_branches.
		                   --- exact Hfree.
		                   --- exact Hy_range.
		             ++ exact Hrename_head.
		             ++ pose (R_head_r :=
		                  root_env_remove_match_params ps_head_r
		                    R_head_payload_r).
		                set (Σ_head :=
		                  sctx_remove_params ps_head Σ_head_payload) in *.
		                pose (Σ_head_r :=
		                  sctx_remove_params ps_head_r
		                    Σ_head_payload_r).
		                assert (Hparams_head_ok_r :
		                  params_ok_sctx_b env ps_head_r
		                    Σ_head_payload_r = true).
		                { eapply alpha_rename_params_params_ok_sctx_b_forward_gen.
		                  - exact Hrename_head_params.
		                  - rewrite <- params_ctx_names_param_names.
		                    eapply params_names_nodup_b_sound.
		                    match goal
		                    with H : params_names_nodup_b ps_head = true |- _ =>
		                      exact H
		                    end.
		                  - intros y Hy.
		                    rewrite <- params_ctx_names_param_names in Hy.
		                    match goal with
			                    | H : match_payload_params binders_head lts args
			                            v_head = infer_ok ps_head |- _ =>
			                        rewrite (match_binder_params_names _ _ _ H) in Hy
		                    end.
		                    apply in_or_app. left. exact Hy.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hrange_used1. exact Hy.
		                  - exact Hctx_head_payload_r.
			                  - match goal with
			                    | H : params_ok_sctx_b env ps_head
			                            Σ_head_payload = true |- _ => exact H
			                    end. }
			                assert (Hctx_head_r :
			                  ctx_alpha rho Σ_head Σ_head_r).
		                { subst Σ_head_r.
		                  unfold Σ_head.
		                  eapply alpha_rename_params_ctx_alpha_remove.
		                  - exact Hrename_head_params.
		                  - exact Hctx_head_payload_r. }
		                assert (Hroots_head_named :
		                  root_set_sctx_roots_named roots_head
		                    (sctx_add_params ps_head Σ1)).
		                { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                    as [Hroots_env _].
		                  match goal with
		                  | H : typed_env_roots_shadow_safe env Ω n R_payload
		                        (sctx_add_params ps_head Σ1) e_head T_head
		                        Σ_head_payload R_head_payload roots_head |- _ =>
		                      destruct (Hroots_env R_payload
		                        (sctx_add_params ps_head Σ1) e_head T_head
		                        Σ_head_payload R_head_payload roots_head H
		                        Hns_payload_head) as [_ Hroots_head0]
		                  end.
		                  - exact Hroots_payload_head.
		                  - eapply root_set_sctx_roots_named_same_bindings.
		                    + apply sctx_same_bindings_sym.
		                      eapply typed_env_structural_same_bindings.
		                      eapply typed_env_roots_structural.
		                      eapply typed_env_roots_shadow_safe_roots.
		                      match goal with
		                      | H : typed_env_roots_shadow_safe env Ω n R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head |- _ =>
		                          exact H
		                      end.
		                    + exact Hroots_head0. }
		                assert (Hroots_head_r_outer :
		                  root_set_equiv roots_headr
		                    (root_set_rename rho roots_head)).
		                { eapply root_set_equiv_trans.
		                  - exact Hroots_head.
		                  - eapply alpha_rename_params_root_set_rename_excluded.
		                    + exact Hrename_head_params.
		                    + match goal with
		                      | H : roots_exclude_params ps_head roots_head |- _ =>
		                          exact H
		                      end. }
		                assert (Hns_R_head_payload :
		                  root_env_no_shadow R_head_payload).
		                { eapply typed_env_roots_no_shadow.
		                  - eapply typed_env_roots_shadow_safe_roots.
		                    match goal with
		                    | H : typed_env_roots_shadow_safe env Ω n R_payload
		                          (sctx_add_params ps_head Σ1) e_head T_head
		                          Σ_head_payload R_head_payload roots_head |- _ =>
		                        exact H
		                    end.
		                  - exact Hns_payload_head. }
		                set (R_out :=
		                  root_env_remove_match_params ps_head
		                    R_head_payload) in *.
		                assert (Hkeys_R_head :
		                  root_env_sctx_keys_named R_out
		                    (sctx_add_params ps_head Σ1)).
		                { eapply root_env_sctx_keys_named_add_params_env.
		                  eapply root_env_sctx_keys_named_same_bindings.
		                  - apply sctx_same_bindings_sym.
		                    eapply sctx_same_bindings_remove_added_params.
		                    apply sctx_same_bindings_refl.
			                  - unfold R_out.
			                    eapply root_env_sctx_keys_named_remove_match_params.
		                    + exact Hns_R_head_payload.
		                    + match goal with
		                      | H : typed_env_roots_shadow_safe env Ω n R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head |- _ =>
		                          destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                            as [Hkeys_env _];
		                          eapply root_env_sctx_keys_named_same_bindings;
		                          [ apply sctx_same_bindings_sym;
		                            eapply typed_env_structural_same_bindings;
		                            eapply typed_env_roots_structural;
		                            eapply typed_env_roots_shadow_safe_roots; exact H
		                          | eapply Hkeys_env; eassumption ]
		                      end. }
		                assert (Hroots_R_head :
		                  root_env_sctx_roots_named R_out
		                    (sctx_add_params ps_head Σ1)).
		                { eapply root_env_sctx_roots_named_add_params_env.
		                  eapply root_env_sctx_roots_named_same_bindings.
		                  - apply sctx_same_bindings_sym.
		                    eapply sctx_same_bindings_remove_added_params.
		                    apply sctx_same_bindings_refl.
			                  - unfold R_out.
			                    eapply root_env_sctx_roots_named_remove_match_params.
		                    + exact Hns_R_head_payload.
		                    + match goal with
		                      | H : root_env_excludes_params ps_head R_out |- _ =>
		                          exact H
		                      end.
		                    + match goal with
		                      | H : typed_env_roots_shadow_safe env Ω n R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head |- _ =>
		                          destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                            as [Hroots_env _];
		                          destruct (Hroots_env R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head H
		                            Hns_payload_head) as [Hroots_env_head _];
		                          [ exact Hroots_payload_head
		                          | eapply root_env_sctx_roots_named_same_bindings;
		                            [ apply sctx_same_bindings_sym;
		                              eapply typed_env_structural_same_bindings;
		                              eapply typed_env_roots_structural;
		                              eapply typed_env_roots_shadow_safe_roots; exact H
		                            | exact Hroots_env_head ] ]
		                      end. }
		                assert (Hroot_none_R_head :
		                  root_env_lookup_params_none_b ps_head R_out = true).
		                { unfold R_out.
		                  apply root_env_lookup_params_none_b_remove_match_params.
		                  exact Hns_R_head_payload. }
		                assert (Hnocoll_params_R_head_payload :
		                  forall x, In x (ctx_names (params_ctx ps_head)) ->
		                    rename_no_collision_for rho_head x
		                      (root_env_names R_head_payload)).
		                { intros x Hin.
		                  eapply alpha_rename_params_rename_no_collision_for_params.
		                  - exact Hrename_head_params.
		                  - exact Hctx1_r.
		                  - exact Hns_R_head_payload.
		                  - match goal with
		                    | H : typed_env_roots_shadow_safe env Ω n R_payload
		                          (sctx_add_params ps_head Σ1) e_head T_head
		                          Σ_head_payload R_head_payload roots_head |- _ =>
		                        destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                          as [Hkeys_env _];
		                        eapply root_env_sctx_keys_named_same_bindings;
		                        [ apply sctx_same_bindings_sym;
		                          eapply typed_env_structural_same_bindings;
		                          eapply typed_env_roots_structural;
		                          eapply typed_env_roots_shadow_safe_roots; exact H
		                        | eapply Hkeys_env; eassumption ]
		                    end.
		                  - match goal
		                    with H : params_names_nodup_b ps_head = true |- _ =>
		                      exact H
		                    end.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hctx_used1. exact Hy.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hrange_used1. exact Hy.
		                  - exact Hnocoll_head_output.
		                  - exact Hin. }
		                assert (HRhead_r_branch :
		                  root_env_equiv R_head_r
		                    (root_env_rename rho_head R_out)).
		                { unfold R_head_r. unfold R_out.
		                  eapply alpha_rename_params_root_env_remove_match_params_full_rename_equiv.
		                  - exact Hrename_head_params.
		                  - match goal
		                    with H : params_names_nodup_b ps_head = true |- _ =>
		                      exact H
		                    end.
		                  - exact Hns_R_head_payload.
		                  - exact HnsR_head_payload_r.
		                  - exact HRhead_payload_r.
		                  - exact Hnocoll_head_output.
		                  - exact Hnocoll_params_R_head_payload.
		                  - intros x Hin. reflexivity. }
		                assert (Henv_head_excl_r :
		                  root_env_excludes_params ps_head_r R_head_r).
		                { eapply alpha_rename_params_root_env_excludes_params_rename.
		                  - exact Hrename_head_params.
		                  - exact Hctx1_r.
		                  - match goal with
		                    | H : root_env_no_shadow R_out |- _ => exact H
		                    end.
		                  - exact Hkeys_R_head.
		                  - exact Hroots_R_head.
		                  - exact Hroot_none_R_head.
		                  - match goal with
		                    | H : root_env_excludes_params ps_head R_out |- _ =>
		                        exact H
		                    end.
		                  - exact HRhead_r_branch.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hctx_used1. exact Hy.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hrange_used1. exact Hy. }
		                assert (HnsR_head_r :
		                  root_env_no_shadow R_head_r).
		                { unfold R_head_r.
		                  apply root_env_remove_match_params_no_shadow.
		                  exact HnsR_head_payload_r. }
		                assert (HRhead_r_outer :
		                  root_env_equiv R_head_r
		                    (root_env_rename rho R_out)).
		                { eapply root_env_equiv_trans.
		                  - exact HRhead_r_branch.
		                  - eapply alpha_rename_params_root_env_rename_excluded.
		                    + exact Hrename_head_params.
		                    + exact HnsRout.
		                    + exact Hroot_none_R_head.
		                    + match goal with
		                      | H : root_env_excludes_params ps_head R_out |- _ =>
		                          exact H
		                      end. }
		                destruct (alpha_rename_typed_match_tail_roots_shadow_safe_forward
		                  env Ω n rho lts args R1 roots_scrut roots_scrutr
		                  Rr1 Σ1 Σr1 l branchesr used_scrut
		                  used_branches v_tail (ty_core T_head) R_out
		                  R_head_r Σ_tail Ts_tail roots_tail)
		                  as [Σ_tailr [roots_tailr [Htail_r [Hctx_tail_r Hroots_tail]]]].
				                ** intros rho0 R0 R0r Σa Σb used0 variant binders e0 er0 used1 T0
			                     Σa' R0' roots0 Hin Htyped0 Halpha HnsR0 HnsR0r
			                     HR0r Hkeys0 Hroots0 Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
			                   eapply (IH env Ω n rho0 R0 R0r Σa Σb e0 er0 used0
			                     used1 T0 Σa' R0' roots0).
		                   --- pose proof (expr_size_match_branch_lt e l variant binders e0 Hin).
		                       simpl in *. lia.
		                   --- exact Htyped0.
		                   --- exact Halpha.
		                   --- exact HnsR0.
		                   --- exact HnsR0r.
		                   --- exact HR0r.
		                   --- exact Hkeys0.
		                   --- exact Hroots0.
		                   --- exact Hnocoll0.
		                   --- exact Hnocoll0'.
		                   --- exact Hcu.
		                   --- exact Hru.
		                   --- exact Hd.
		                   --- exact Hr.
			                ** match goal with
			                   | H : typed_match_tail_roots_shadow_safe env Ω n
			                         lts args R1 roots_scrut Σ1 l v_tail
			                         (ty_core T_head) R_out Σ_tail Ts_tail
			                         roots_tail |- _ => exact H
			                   end.
		                ** exact Hctx1_r.
		                ** exact HnsR1.
		                ** exact HnsRout.
		                ** exact HnsRr1.
		                ** exact HRr1.
		                ** match goal with
		                   | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                         Σ1 R1 roots_scrut |- _ =>
		                       destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                         as [Hkeys_env _];
		                       eapply Hkeys_env; eassumption
		                   end.
			                ** exact Hroots_R1.
			                ** exact Hroots_scrut_named.
		                ** exact HnocollR1.
		                ** exact HnocollR'.
			                ** exact Hctx_used1.
			                ** exact Hrange_used1.
			                ** exact Hroots_scrut.
			                ** exact Hdisj_branches.
		                ** exact Hbranches.
			                ** exact HRhead_r_outer.
			                ** destruct (ctx_alpha_merge_many_forward rho
			                     Σ_head Σ_head_r Σ_tail Σ_tailr Γ_out)
			                     as [Γ_outr [Hmerge_r Hctx_merge_r]].
		                   --- exact Hctx_head_r.
		                   --- exact Hctx_tail_r.
		                   --- match goal with
		                       | H : ctx_merge_many (ctx_of_sctx Σ_head)
		                             (map ctx_of_sctx Σ_tail) = Some Γ_out |- _ =>
		                           exact H
		                       end.
				                   --- exists (sctx_of_ctx Γ_outr), R_head_r,
			                         (root_sets_union (roots_headr :: roots_tailr)).
				                       split; [| split; [| split; [| split]]].
				                       { eapply TERS_Match.
				                         - exact Hscrut_r.
				                         - match goal with
				                           | H : ty_core T_scrut = TEnum enum_name lts args |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : Program.lookup_enum enum_name env = Some edef |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : Datatypes.length lts = Program.enum_lifetimes edef |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : Datatypes.length args = Program.enum_type_params edef |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : check_struct_bounds env (Program.enum_bounds edef) args =
				                                 None |- _ => exact H
				                           end.
				                         - eapply alpha_rename_match_branches_first_unknown_variant_branch; eauto.
					                         - match goal with
					                           | H : Program.enum_variants edef = v_head :: v_tail |- _ =>
					                               exact H
					                           end.
					                         - exact Hbinders_head_r.
						                         - unfold match_payload_params.
						                           exact Hparams_head_r.
					                         - exact Hparams_head_nodup_r.
					                         - exact Hctx_head_none_r.
					                         - exact Hroot_head_none_r.
					                         - exact Hlookup_head_r.
					                         - reflexivity.
					                         - exact Hhead_r.
					                         - exact Hparams_head_ok_r.
					                         - eapply alpha_rename_params_roots_exclude_params_rename.
					                           + exact Hrename_head_params.
					                           + exact Hctx1_r.
					                           + exact Hroots_head_named.
					                           + match goal with
					                             | H : roots_exclude_params ps_head roots_head |- _ =>
					                                 exact H
					                             end.
					                           + exact Hroots_head.
					                           + intros y Hy. apply in_or_app. right.
					                             apply in_or_app. right.
					                             apply Hused_head_pre. apply Hctx_used1.
					                             exact Hy.
					                           + intros y Hy. apply in_or_app. right.
					                             apply in_or_app. right.
					                             apply Hused_head_pre. apply Hrange_used1.
					                             exact Hy.
					                         - reflexivity.
					                         - exact Henv_head_excl_r.
					                         - reflexivity.
					                         - exact Htail_r.
					                         - exact Hmerge_r. }
				                       { unfold sctx_of_ctx. exact Hctx_merge_r. }
				                       { exact HnsR_head_r. }
				                       { exact HRhead_r_outer. }
				                       { eapply root_sets_union_rename_equiv.
				                         simpl. constructor; assumption. }
		      + eapply (alpha_rename_typed_env_roots_replace_shadow_safe_support_forward
		          env Ω n rho R Rr Σ Σr p e er used used' T Σ' R' roots).
	        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_assign_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr p e er used used' T Σ' R' roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply alpha_rename_typed_env_roots_borrow_shadow_safe_support_forward;
          eauto.
      + inversion Htyped; subst; simpl in Hrename; injection Hrename as <- <-.
        * match goal with
          | Hlookup : root_env_lookup ?x0 ?R0 = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_ren :
                root_env_lookup (lookup_rename x0 rho)
                  (root_env_rename rho R0) =
                Some (root_set_rename rho roots));
              [ apply root_env_lookup_rename;
                [ apply HnocollR;
                  eapply root_env_lookup_some_in_names; exact Hlookup
                | exact Hlookup ]
              | destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R0)
                  (lookup_rename x0 rho) (root_set_rename rho roots)
                  HR Hlookup_ren) as [rootsr [Hlookup_r Hroots_r]] ]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowShared.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ eapply place_path_rename_place_some. eassumption.
             ++ exact Hlookup_r.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
        * match goal with
          | Hpath : place_path p = None,
            Hlookup : place_root_lookup ?R0 p = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_root :
                root_env_lookup (root_provenance_place_name p) R0 = Some roots)
                by (rewrite <- (place_root_lookup_indirect R0 p Hpath); exact Hlookup);
              destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
                (root_provenance_place_name p) roots HR HnocollR Hlookup_root)
                as [rootsr [Hlookup_r Hroots_r]]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowShared_Indirect.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ match goal with Hpath : place_path p = None |- _ =>
                  apply place_path_rename_place_none; exact Hpath
                end.
             ++ rewrite (place_root_lookup_indirect Rr (rename_place rho p)).
                ** rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
                ** match goal with Hpath : place_path p = None |- _ =>
                     apply place_path_rename_place_none; exact Hpath
                   end.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
        * match goal with
          | Hlookup : root_env_lookup ?x0 ?R0 = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_ren :
                root_env_lookup (lookup_rename x0 rho)
                  (root_env_rename rho R0) =
                Some (root_set_rename rho roots));
              [ apply root_env_lookup_rename;
                [ apply HnocollR;
                  eapply root_env_lookup_some_in_names; exact Hlookup
                | exact Hlookup ]
              | destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R0)
                  (lookup_rename x0 rho) (root_set_rename rho roots)
                  HR Hlookup_ren) as [rootsr [Hlookup_r Hroots_r]] ]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowUnique.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ eapply place_path_rename_place_some. eassumption.
             ++ eapply ctx_alpha_lookup_mut_forward.
                ** exact Hctx.
                ** match goal with
                   | Hpath : place_path p = Some (?x0, ?path0) |- _ =>
                       rewrite <- (place_path_root p x0 path0 Hpath); exact Hsafe_root
                   end.
                ** eassumption.
             ++ exact Hlookup_r.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
        * match goal with
          | Hpath : place_path p = None,
            Hlookup : place_root_lookup ?R0 p = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_root :
                root_env_lookup (root_provenance_place_name p) R0 = Some roots)
                by (rewrite <- (place_root_lookup_indirect R0 p Hpath); exact Hlookup);
              destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
                (root_provenance_place_name p) roots HR HnocollR Hlookup_root)
                as [rootsr [Hlookup_r Hroots_r]]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowUnique_Indirect.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ match goal with Hpath : place_path p = None |- _ =>
                  apply place_path_rename_place_none; exact Hpath
                end.
             ++ eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
             ++ rewrite (place_root_lookup_indirect Rr (rename_place rho p)).
                ** rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
                ** match goal with Hpath : place_path p = None |- _ =>
                     apply place_path_rename_place_none; exact Hpath
                   end.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
      + eapply (alpha_rename_typed_env_roots_drop_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_if_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hlt0 Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
  }
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply (Hsize (S (expr_size e))); eauto.
Qed.

Lemma alpha_rename_fn_def_typed_structural_forward :
  forall env used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params f))) ->
    typed_fn_env_structural env f ->
    typed_fn_env_structural env fr.
Proof.
  intros env used f fr used' Hrename Hnodup Htyped.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  injection Hrename as <- <-.
  unfold typed_fn_env_structural in *. simpl in *.
  destruct Htyped as [T_body [Γ_out [Htyped_body [Hcompat Hparams]]]].
  unfold fn_body_ctx, fn_body_params in Htyped_body.
  simpl in Htyped_body.
  destruct (alpha_rename_typed_env_structural_forward
    (global_env_with_local_bounds env fn_bounds) outs lifetimes ρ
    (sctx_of_ctx (params_ctx (ps ++ captures)))
    (sctx_of_ctx (params_ctx (psr ++ captures)))
    body bodyr used1 used2 T_body (sctx_of_ctx Γ_out))
    as [Σr_out [Htyped_body_r Hctx_out_r]].
  - eapply alpha_rename_params_ctx_alpha_stable_tail. exact Hps.
  - intros x Hin.
    change (ctx_names (sctx_of_ctx (params_ctx (psr ++ captures))))
      with (ctx_names (params_ctx (psr ++ captures))) in Hin.
    rewrite params_ctx_app in Hin.
    rewrite ctx_names_app in Hin.
    rewrite !params_ctx_names_param_names in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_captures].
    + eapply alpha_rename_params_names_in_used.
      * exact Hps.
      * rewrite params_ctx_names_param_names. exact Hin_params.
    + eapply alpha_rename_params_used_extends.
      * exact Hps.
      * apply in_or_app. right.
        apply in_or_app. left. exact Hin_captures.
  - intros x Hin.
    eapply alpha_rename_params_range_in_used_nil.
    + exact Hps.
    + exact Hin.
  - intros x Hfree Hrange.
    eapply alpha_rename_params_range_fresh_used_nil.
    + exact Hps.
    + exact Hrange.
    + apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. left. exact Hfree.
  - exact Hbody.
  - exact Htyped_body.
  - exists T_body, Σr_out. repeat split.
    + exact Htyped_body_r.
    + exact Hcompat.
    + eapply alpha_rename_params_params_ok_env_b_forward.
      * exact Hps.
      * exact Hnodup.
      * intros x Hin.
        apply in_or_app. left. exact Hin.
      * exact Hctx_out_r.
      * exact Hparams.
Qed.
