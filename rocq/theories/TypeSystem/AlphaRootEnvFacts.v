From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping AlphaEnvStructural AlphaRoots.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.
Lemma place_resolved_write_writable_chain_rename :
  forall env rho R Rr Σ Σr p,
    root_env_equiv (root_env_rename rho R) Rr ->
    rename_no_collision_on rho (root_env_names R) ->
    ctx_alpha rho Σ Σr ->
    ~ In (place_root p) (rename_range rho) ->
    place_resolved_write_writable_chain env R Σ p ->
    place_resolved_write_writable_chain env Rr Σr (rename_place rho p).
Proof.
  intros env rho R Rr Σ Σr p HR Hnocoll Halpha Hsafe Hchain.
  induction Hchain.
  - apply PRWWC_Direct.
    apply place_resolved_write_direct_parent_rename. exact H.
  - simpl.
    eapply PRWWC_Deref.
    + exact (IHHchain Hsafe).
    + eapply alpha_rename_writable_place_env_structural_forward; eauto.
    + eapply place_resolved_write_target_equiv.
      * exact HR.
      * apply place_resolved_write_target_rename.
        -- exact Hnocoll.
        -- exact H0.
    + eapply ctx_alpha_lookup_mut_forward_any; eassumption.
Qed.

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

Lemma root_set_store_names_sctx_names :
  forall roots Σ x,
    root_set_sctx_roots_named roots Σ ->
    In x (root_set_store_names roots) ->
    In x (ctx_names Σ).
Proof.
  induction roots as [| atom rest IH]; intros Σ x Hnamed Hin; simpl in Hin.
  - contradiction.
  - destruct atom as [y | y]; simpl in Hin.
    + destruct Hin as [Hin | Hin].
      * subst x. apply Hnamed. simpl. left. reflexivity.
      * apply IH.
        -- unfold root_set_sctx_roots_named in *.
           intros z Hz. apply Hnamed. simpl. right. exact Hz.
        -- exact Hin.
    + apply IH.
      * unfold root_set_sctx_roots_named in *.
        intros z Hz. apply Hnamed. simpl. right. exact Hz.
      * exact Hin.
Qed.

Lemma root_env_all_store_names_sctx_names :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    In x (root_env_all_store_names R) ->
    In x (ctx_names Σ).
Proof.
  induction R as [| [y roots] rest IH]; intros Σ x Hns Hkeys Hroots Hin; simpl in Hin.
  - contradiction.
  - inversion Hns as [| ? ? Hnot_tail Hns_tail]; subst.
    destruct Hin as [Hin | Hin].
    + subst x. apply Hkeys. simpl. left. reflexivity.
    + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply root_set_store_names_sctx_names.
        -- eapply (root_env_lookup_sctx_roots_named ((y, roots) :: rest) Σ y roots).
           ++ simpl. rewrite ident_eqb_refl. reflexivity.
           ++ exact Hroots.
        -- exact Hin.
      * eapply IH.
        -- exact Hns_tail.
        -- unfold root_env_sctx_keys_named, root_env_keys_named in *.
           intros z Hz. apply Hkeys. simpl. right. exact Hz.
        -- unfold root_env_sctx_roots_named in *.
           intros z roots0 w Hlookup Hinw.
           apply (Hroots z roots0 w).
           ++ simpl. destruct (ident_eqb z y) eqn:Hzy.
              ** apply ident_eqb_eq in Hzy. subst z.
                 exfalso. apply Hnot_tail.
                 eapply root_env_lookup_some_in_names; exact Hlookup.
              ** exact Hlookup.
           ++ exact Hinw.
        -- exact Hin.
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

Lemma ctx_alpha_lookup_rename_not_fresh :
  forall rho Γ Γr x xr,
    ctx_alpha rho Γ Γr ->
    In x (ctx_names Γ) ->
    ~ In xr (ctx_names Γr) ->
    ~ In xr (rename_range rho) ->
    lookup_rename x rho <> xr.
Proof.
  intros rho Γ Γr x xr Halpha Hin Hfresh_ctx Hfresh_range Heq.
  destruct (lookup_rename_in_range_or_self rho x) as [Hin_range | Hself].
  - apply Hfresh_range. rewrite <- Heq. exact Hin_range.
  - apply Hfresh_ctx. rewrite <- Heq.
    eapply ctx_alpha_lookup_rename_in_names; eassumption.
Qed.

Lemma ctx_alpha_no_collision_on_any :
  forall rho Σ Σr,
    ctx_alpha rho Σ Σr ->
    rename_no_collision_on rho (ctx_names Σ).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho Σ Σr Halpha.
  induction Halpha as [Γ | rho Γ Γr x xr T b m Halpha IH Hfresh_ctx Hfresh_range];
    intros a Ha y Hy Hya Heq.
  - simpl in Heq. contradiction.
  - simpl in Ha, Hy.
    destruct Ha as [Ha | Ha].
    + subst a. destruct Hy as [Hy | Hy].
      * subst y. contradiction.

      * simpl in Heq. destruct (ident_eqb y x) eqn:Hyx.
        -- apply ident_eqb_eq in Hyx. subst y. contradiction.
        -- try rewrite Hyx in Heq. try rewrite ident_eqb_refl in Heq.
           eapply (ctx_alpha_lookup_rename_not_fresh rho Γ Γr y xr); eauto; exact Heq.
    + destruct Hy as [Hy | Hy].
      * subst y. simpl in Heq. destruct (ident_eqb a x) eqn:Hax.
        -- apply ident_eqb_eq in Hax. subst a. contradiction.
        -- try rewrite Hax in Heq. try rewrite ident_eqb_refl in Heq.
           symmetry in Heq.
           eapply (ctx_alpha_lookup_rename_not_fresh rho Γ Γr a xr); eauto; exact Heq.
      * simpl in Heq. destruct (ident_eqb a x) eqn:Hax.
        -- apply ident_eqb_eq in Hax. subst a.
           destruct (ident_eqb y x) eqn:Hyx.
           ++ apply ident_eqb_eq in Hyx. subst y. contradiction.
           ++ try rewrite Hyx in Heq. try rewrite ident_eqb_refl in Heq.
              eapply (ctx_alpha_lookup_rename_not_fresh rho Γ Γr y xr); eauto; exact Heq.
        -- destruct (ident_eqb y x) eqn:Hyx.
           ++ apply ident_eqb_eq in Hyx. subst y.
              try rewrite Hax in Heq. try rewrite ident_eqb_refl in Heq. symmetry in Heq.
              eapply (ctx_alpha_lookup_rename_not_fresh rho Γ Γr a xr); eauto; exact Heq.
           ++ try rewrite Hax in Heq; try rewrite Hyx in Heq.
              exact (IH a Ha y Hy Hya Heq).
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
      simpl in Heq. try rewrite ident_eqb_refl in Heq.
      destruct (ident_eqb y x) eqn:Hyeq.
      * apply ident_eqb_eq in Hyeq. contradiction.
      * apply Hxr_notin.
        rewrite <- Heq.
        eapply ctx_alpha_lookup_rename_in_names; eassumption.
    + subst y.
      assert (Hax : a <> x).
      { intros Heq_ax. subst a. contradiction. }
      simpl in Heq. try rewrite ident_eqb_refl in Heq.
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

Lemma ctx_alpha_sctx_names_no_collision :
  forall rho Σ Σr x y,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    In x (ctx_names Σ) ->
    In y (ctx_names Σ) ->
    y <> x ->
    lookup_rename y rho <> lookup_rename x rho.
Proof.
  intros rho Σ Σr x y Halpha Hnodup Hnodup_r Hx Hy Hyx.
  pose proof (ctx_alpha_no_collision_on rho Σ Σr
    Halpha Hnodup Hnodup_r) as Hnocoll.
  exact (Hnocoll x Hx y Hy Hyx).
Qed.

Lemma ctx_alpha_root_env_keys_no_collision_for :
  forall rho Σ Σr R x,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_env_sctx_keys_named R Σ ->
    In x (ctx_names Σ) ->
    rename_no_collision_for rho x (root_env_names R).
Proof.
  unfold rename_no_collision_for.
  intros rho Σ Σr R x Halpha Hnodup Hnodup_r Hkeys Hx y Hy Hyx.
  eapply ctx_alpha_sctx_names_no_collision.
  - exact Halpha.
  - exact Hnodup.
  - exact Hnodup_r.
  - exact Hx.
  - apply Hkeys. exact Hy.
  - exact Hyx.
Qed.

Lemma ctx_alpha_root_env_keys_no_collision_on :
  forall rho Σ Σr R,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_env_sctx_keys_named R Σ ->
    rename_no_collision_on rho (root_env_names R).
Proof.
  unfold rename_no_collision_on.
  intros rho Σ Σr R Halpha Hnodup Hnodup_r Hkeys x Hin.
  eapply ctx_alpha_root_env_keys_no_collision_for.
  - exact Halpha.
  - exact Hnodup.
  - exact Hnodup_r.
  - exact Hkeys.
  - apply Hkeys. exact Hin.
Qed.

Lemma singleton_store_root_some_in :
  forall roots x,
    singleton_store_root roots = Some x ->
    In (RStore x) roots.
Proof.
  intros roots x Hsingle.
  destruct (singleton_store_root_some_equiv roots x Hsingle
    (RStore x)) as [_ H].
  apply H. simpl. left. reflexivity.
Qed.

Lemma singleton_store_root_rename_some :
  forall rho roots x,
    singleton_store_root roots = Some x ->
    singleton_store_root (root_set_rename rho roots) =
      Some (lookup_rename x rho).
Proof.
  intros rho roots x Hsingle.
  apply singleton_store_root_of_singleton_equiv.
  eapply root_set_equiv_trans.
  - apply root_set_rename_equiv.
    apply singleton_store_root_some_equiv. exact Hsingle.
  - simpl. apply root_set_equiv_refl.
Qed.

Lemma same_store_root_rename_true_alpha :
  forall rho Σ Σr x roots,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_set_sctx_roots_named (RStore x :: roots) Σ ->
    same_store_root (lookup_rename x rho) (root_set_rename rho roots) =
      true ->
    same_store_root x roots = true.
Proof.
  intros rho Σ Σr x roots Halpha Hnodup Hnodup_r.
  induction roots as [| atom rest IH]; intros Hnamed Hsame; simpl in *.
  - reflexivity.
  - destruct atom as [y | y]; simpl in Hsame; try discriminate.
    apply andb_true_iff in Hsame as [Hy_ren Hsame].
    destruct (ident_eqb y x) eqn:Hyx.
    + simpl.
      apply IH.
      * unfold root_set_sctx_roots_named in *.
        intros z Hin. apply Hnamed. simpl in Hin.
        destruct Hin as [Hin | Hin].
        -- left. exact Hin.
        -- right. right. exact Hin.
      * exact Hsame.
    + apply ident_eqb_neq in Hyx.
      apply ident_eqb_eq in Hy_ren.
      exfalso.
      eapply ctx_alpha_sctx_names_no_collision.
      * exact Halpha.
      * exact Hnodup.
      * exact Hnodup_r.
      * apply Hnamed. simpl. left. reflexivity.
      * apply Hnamed. simpl. right. left. reflexivity.
      * exact Hyx.
      * exact Hy_ren.
Qed.

Lemma singleton_store_root_rename_none_alpha :
  forall rho Σ Σr roots,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_set_sctx_roots_named roots Σ ->
    singleton_store_root roots = None ->
    singleton_store_root (root_set_rename rho roots) = None.
Proof.
  intros rho Σ Σr roots Halpha Hnodup Hnodup_r Hnamed Hsingle.
  destruct roots as [| atom rest]; simpl in *; try reflexivity.
  destruct atom as [x | x]; try reflexivity.
  destruct (same_store_root x rest) eqn:Hsame; try discriminate.
  simpl. destruct (same_store_root (lookup_rename x rho)
    (root_set_rename rho rest)) eqn:Hsame_ren; try reflexivity.
  exfalso.
  pose proof (same_store_root_rename_true_alpha rho Σ Σr x rest
    Halpha Hnodup Hnodup_r Hnamed Hsame_ren) as Hsame_true.
  rewrite Hsame in Hsame_true. discriminate.
Qed.

Lemma place_borrow_roots_sctx_roots_named :
  forall R Σ p roots,
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named (root_of_place p) Σ ->
    place_borrow_roots R p = Some roots ->
    root_set_sctx_roots_named roots Σ.
Proof.
  intros R Σ p roots Henv Hplace Hborrow.
  unfold place_borrow_roots in Hborrow.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - inversion Hborrow; subst roots. exact Hplace.
  - assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hborrow. }
    eapply root_env_lookup_sctx_roots_named; eassumption.
Qed.

Lemma resolve_root_set_fuel_sctx_roots_named :
  forall fuel R Σ roots out,
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    resolve_root_set_fuel fuel R roots = Some out ->
    root_set_sctx_roots_named out Σ.
Proof.
  induction fuel as [| fuel IH]; intros R Σ roots out Henv Hroots Hres;
    simpl in Hres; try discriminate.
  destruct (singleton_store_root roots) as [x |] eqn:Hsingle.
  - destruct (root_env_lookup x R) as [env_roots |] eqn:Hlookup.
    + assert (Henv_roots : root_set_sctx_roots_named env_roots Σ).
      { eapply root_env_lookup_sctx_roots_named; eassumption. }
      destruct (singleton_store_root env_roots) as [y |] eqn:Henv_single.
      * destruct (ident_eqb x y) eqn:Hxy.
        -- inversion Hres; subst out. exact Hroots.
        -- eapply IH; eassumption.
      * eapply IH; eassumption.
    + inversion Hres; subst out. exact Hroots.
  - inversion Hres; subst out. exact Hroots.
Qed.

Lemma place_resolved_roots_sctx_roots_named :
  forall R Σ p roots,
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named (root_of_place p) Σ ->
    place_resolved_roots R p = Some roots ->
    root_set_sctx_roots_named roots Σ.
Proof.
  intros R Σ p roots Henv Hplace Hresolved.
  unfold place_resolved_roots in Hresolved.
  destruct (place_borrow_roots R p) as [borrow_roots |] eqn:Hborrow;
    try discriminate.
  assert (Hborrow_named : root_set_sctx_roots_named borrow_roots Σ).
  { eapply place_borrow_roots_sctx_roots_named; eassumption. }
  unfold resolve_root_set in Hresolved.
  eapply resolve_root_set_fuel_sctx_roots_named; eassumption.
Qed.

Lemma place_borrow_roots_rename_alpha :
  forall rho Σ Σr R p roots,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_env_sctx_keys_named R Σ ->
    place_borrow_roots R p = Some roots ->
    exists rootsr,
      place_borrow_roots (root_env_rename rho R) (rename_place rho p) =
        Some rootsr /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros rho Σ Σr R p roots Halpha Hnodup Hnodup_r Hkeys Hborrow.
  unfold place_borrow_roots in *.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - rewrite (place_path_rename_place_some rho p x path Hpath).
    inversion Hborrow; subst roots.
    exists (root_of_place (rename_place rho p)).
    split.
    + reflexivity.
    + rewrite root_of_place_rename_place. apply root_set_equiv_refl.
  - assert (Hpath_ren := place_path_rename_place_none rho p Hpath).
    rewrite Hpath_ren.
    assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hborrow. }
    assert (Hroot_in :
      In (root_provenance_place_name p) (ctx_names Σ)).
    { apply Hkeys. eapply root_env_lookup_some_in_names. exact Hlookup. }
    assert (Hnocoll :
      rename_no_collision_for rho (root_provenance_place_name p)
        (root_env_names R)).
    { eapply ctx_alpha_root_env_keys_no_collision_for; eassumption. }
    exists (root_set_rename rho roots).
    split.
    + rewrite (place_root_lookup_indirect (root_env_rename rho R)
        (rename_place rho p) Hpath_ren).
      rewrite root_provenance_place_name_rename_place.
      rewrite (root_env_lookup_rename rho R
        (root_provenance_place_name p) roots Hnocoll Hlookup).
      reflexivity.
    + apply root_set_equiv_refl.
Qed.

Lemma resolve_root_set_fuel_rename_alpha :
  forall fuel rho Σ Σr R roots out,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots Σ ->
    resolve_root_set_fuel fuel R roots = Some out ->
    exists outr,
      resolve_root_set_fuel fuel (root_env_rename rho R)
        (root_set_rename rho roots) = Some outr /\
      root_set_equiv outr (root_set_rename rho out).
Proof.
  induction fuel as [| fuel IH]; intros rho Σ Σr R roots out Halpha
    Hnodup Hnodup_r Hkeys Henv Hroots Hres; simpl in Hres; try discriminate.
  simpl.
  destruct (singleton_store_root roots) as [x |] eqn:Hsingle.
  - rewrite (singleton_store_root_rename_some rho roots x Hsingle).
    assert (Hx_in : In x (ctx_names Σ)).
    { apply Hroots. apply singleton_store_root_some_in. exact Hsingle. }
    assert (Hnocoll_x : rename_no_collision_for rho x (root_env_names R)).
    { eapply ctx_alpha_root_env_keys_no_collision_for; eassumption. }
    destruct (root_env_lookup x R) as [env_roots |] eqn:Hlookup.
    + rewrite (root_env_lookup_rename rho R x env_roots
        Hnocoll_x Hlookup).
      assert (Henv_roots_named :
        root_set_sctx_roots_named env_roots Σ).
      { eapply root_env_lookup_sctx_roots_named; eassumption. }
      destruct (singleton_store_root env_roots) as [y |] eqn:Henv_single.
      * rewrite (singleton_store_root_rename_some rho env_roots y
          Henv_single).
        destruct (ident_eqb x y) eqn:Hxy.
        -- apply ident_eqb_eq in Hxy. subst y.
           rewrite ident_eqb_refl.
           inversion Hres; subst out.
           exists (root_set_rename rho roots).
           split; [reflexivity | apply root_set_equiv_refl].
        -- assert (Hy_in : In y (ctx_names Σ)).
           { apply Henv_roots_named.
             apply singleton_store_root_some_in. exact Henv_single. }
           assert (Hxy_neq : x <> y).
           { apply ident_eqb_neq. exact Hxy. }
           destruct (ident_eqb (lookup_rename x rho) (lookup_rename y rho))
             eqn:Hxy_ren.
           ++ apply ident_eqb_eq in Hxy_ren.
              exfalso.
              eapply (ctx_alpha_sctx_names_no_collision rho Σ Σr y x).
              ** exact Halpha.
              ** exact Hnodup.
              ** exact Hnodup_r.
              ** exact Hy_in.
              ** exact Hx_in.
              ** exact Hxy_neq.
              ** exact Hxy_ren.
           ++ eapply IH; eassumption.
      * rewrite (singleton_store_root_rename_none_alpha rho Σ Σr env_roots
          Halpha Hnodup Hnodup_r Henv_roots_named Henv_single).
        eapply IH; eassumption.
    + rewrite (root_env_lookup_rename_none rho R x Hnocoll_x Hlookup).
      inversion Hres; subst out.
      exists (root_set_rename rho roots).
      split; [reflexivity | apply root_set_equiv_refl].
  - rewrite (singleton_store_root_rename_none_alpha rho Σ Σr roots
      Halpha Hnodup Hnodup_r Hroots Hsingle).
    inversion Hres; subst out.
    exists (root_set_rename rho roots).
    split; [reflexivity | apply root_set_equiv_refl].
Qed.

Lemma place_resolved_roots_rename_alpha_equiv :
  forall rho Σ Σr R Rr p roots,
    ctx_alpha rho Σ Σr ->
    NoDup (ctx_names Σ) ->
    NoDup (ctx_names Σr) ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named (root_of_place p) Σ ->
    place_resolved_roots R p = Some roots ->
    exists rootsr,
      place_resolved_roots Rr (rename_place rho p) = Some rootsr /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros rho Σ Σr R Rr p roots Halpha Hnodup Hnodup_r HnsR HnsRr
    HRr Hkeys Henv Hplace Hresolved.
  unfold place_resolved_roots in Hresolved.
  destruct (place_borrow_roots R p) as [borrow_roots |] eqn:Hborrow;
    try discriminate.
  assert (Hborrow_named : root_set_sctx_roots_named borrow_roots Σ).
  { eapply place_borrow_roots_sctx_roots_named; eassumption. }
  destruct (place_borrow_roots_rename_alpha rho Σ Σr R p borrow_roots
    Halpha Hnodup Hnodup_r Hkeys Hborrow) as
    [borrow_rootsr [Hborrow_r Hborrow_eq]].
  destruct (resolve_root_set_fuel_rename_alpha
      (S (List.length R)) rho Σ Σr R borrow_roots roots
      Halpha Hnodup Hnodup_r Hkeys Henv Hborrow_named Hresolved)
    as [roots_ren [Hresolved_ren Hroots_ren]].
  destruct (resolve_root_set_fuel_equiv
      (S (List.length R)) (root_env_rename rho R)
      (root_env_rename rho R) (root_set_rename rho borrow_roots)
      borrow_rootsr roots_ren
      (root_env_equiv_refl (root_env_rename rho R))
      (root_set_equiv_sym _ _ Hborrow_eq) Hresolved_ren) as
    [roots_ren' [Hresolved_ren' Hroots_ren']].
  destruct (place_resolved_roots_equiv_same_length
      (root_env_rename rho R) Rr (rename_place rho p) roots_ren')
    as [rootsr [Hresolved_r Hroots_r]].
  - assert (HnocollR : rename_no_collision_on rho (root_env_names R)).
    { eapply ctx_alpha_root_env_keys_no_collision_on; eassumption. }
    assert (HnsR_ren : root_env_no_shadow (root_env_rename rho R)).
    { apply root_env_rename_no_shadow; assumption. }
    eapply root_env_equiv_length.
    + exact HnsR_ren.
    + exact HnsRr.
    + apply root_env_equiv_sym. exact HRr.
  - apply root_env_equiv_sym. exact HRr.
  - unfold place_resolved_roots. rewrite Hborrow_r.
    unfold resolve_root_set. rewrite root_env_rename_length.
    exact Hresolved_ren'.
  - exists rootsr. split.
    + exact Hresolved_r.
    + eapply root_set_equiv_trans.
      * apply root_set_equiv_sym. exact Hroots_r.
      * eapply root_set_equiv_trans.
        -- apply root_set_equiv_sym. exact Hroots_ren'.
        -- exact Hroots_ren.
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
        try rewrite ident_eqb_refl in Heq. exact Heq.
  - destruct Hy as [Hy | Hy].
    + subst y.
      simpl.
      destruct (ident_eqb x0 x) eqn:Hx0x.
      * apply ident_eqb_eq in Hx0x. subst x0. contradiction.
      * intros Heq. apply (Hfresh x0 Hx0).
        try rewrite ident_eqb_refl in Heq. symmetry. exact Heq.
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

Lemma place_resolved_write_target_writable_chain_sctx_roots_named :
  forall env R Σ p x,
    root_env_sctx_roots_named R Σ ->
    place_resolved_write_writable_chain env R Σ p ->
    place_resolved_write_target R p = Some x ->
    root_set_sctx_roots_named [RStore x] Σ.
Proof.
  intros env R Σ p x Henv Hchain Htarget_out.
  revert x Htarget_out.
  induction Hchain as [p Hdirect | p target Hchain IH Hwritable Htarget Hmut];
    intros x Htarget_out.
  - destruct Hdirect as [q [root [path [Hp Hpath]]]]. subst p.
    simpl in Htarget_out.
    rewrite (place_resolved_write_target_path_root R q root path Hpath)
      in Htarget_out.
    destruct (root_env_lookup root R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct (singleton_store_root roots) as [target |] eqn:Hsingle;
      try discriminate.
    inversion Htarget_out. subst target.
    apply root_set_sctx_roots_named_single.
    eapply root_set_store_names_sctx_names.
    + eapply root_env_lookup_sctx_roots_named; eassumption.
    + eapply singleton_store_root_store_name_in. exact Hsingle.
  - simpl in Htarget_out. rewrite Htarget in Htarget_out.
    destruct (root_env_lookup target R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct (singleton_store_root roots) as [target_out |] eqn:Hsingle;
      try discriminate.
    inversion Htarget_out. subst target_out.
    apply root_set_sctx_roots_named_single.
    eapply root_set_store_names_sctx_names.
    + eapply root_env_lookup_sctx_roots_named; eassumption.
    + eapply singleton_store_root_store_name_in. exact Hsingle.
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

Lemma root_env_add_params_roots_same_all_store_names_subset :
  forall ps roots R x,
    In x (root_env_all_store_names
      (root_env_add_params_roots_same ps roots R)) ->
    In x (ctx_names (params_ctx ps) ++
      root_set_store_names roots ++ root_env_all_store_names R).
Proof.
  induction ps as [| [m y T] ps IH]; intros roots R x Hin; simpl in *.
  - apply in_or_app. right. exact Hin.
  - destruct Hin as [Hin | Hin].
    + left. exact Hin.
    + apply in_app_or in Hin as [Hin | Hin].
      * right. apply in_or_app. right. apply in_or_app. left. exact Hin.
      * specialize (IH roots R x Hin).
        apply in_app_or in IH as [Hin_params | Hin_tail].
        -- right. apply in_or_app. left. exact Hin_params.
        -- apply in_app_or in Hin_tail as [Hin_roots | Hin_env].
           ++ right. apply in_or_app. right. apply in_or_app. left. exact Hin_roots.
           ++ right. apply in_or_app. right. apply in_or_app. right. exact Hin_env.
Qed.

Lemma rename_no_collision_on_all_store_names_add_params_roots_same :
  forall rho ps roots R,
    rename_no_collision_on rho
      (ctx_names (params_ctx ps) ++
       root_set_store_names roots ++ root_env_all_store_names R) ->
    rename_no_collision_on rho
      (root_env_all_store_names
        (root_env_add_params_roots_same ps roots R)).
Proof.
  intros rho ps roots R Hnocoll.
  eapply rename_no_collision_on_all_store_names_weaken.
  - exact Hnocoll.
  - intros x Hin.
    eapply root_env_add_params_roots_same_all_store_names_subset; eassumption.
Qed.

Lemma root_env_remove_match_params_all_store_names_subset :
  forall ps R x,
    In x (root_env_all_store_names (root_env_remove_match_params ps R)) ->
    In x (root_env_all_store_names R).
Proof.
  induction ps as [| [m y T] ps IH]; intros R x Hin; simpl in *.
  - exact Hin.
  - apply root_env_all_store_names_remove_subset with (x := y).
    apply IH. exact Hin.
Qed.

Lemma rename_no_collision_on_all_store_names_remove_match_params :
  forall rho ps R,
    rename_no_collision_on rho (root_env_all_store_names R) ->
    rename_no_collision_on rho
      (root_env_all_store_names (root_env_remove_match_params ps R)).
Proof.
  intros rho ps R Hnocoll.
  eapply rename_no_collision_on_all_store_names_weaken.
  - exact Hnocoll.
  - intros x Hin.
    eapply root_env_remove_match_params_all_store_names_subset; eassumption.
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
