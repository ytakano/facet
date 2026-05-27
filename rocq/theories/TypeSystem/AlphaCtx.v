From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Import AlphaCore.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Context alpha-renaming facts                                        *)
(* ------------------------------------------------------------------ *)

Inductive ctx_alpha : rename_env -> ctx -> ctx -> Prop :=
  | CtxAlpha_Base : forall Γ,
      ctx_alpha [] Γ Γ
  | CtxAlpha_Bind : forall ρ Γ Γr x xr T b m,
      ctx_alpha ρ Γ Γr ->
      ~ In xr (ctx_names Γr) ->
      ~ In xr (rename_range ρ) ->
      ctx_alpha ((x, xr) :: ρ) ((x, T, b, m) :: Γ) ((xr, T, b, m) :: Γr).

Lemma ctx_alpha_nil_eq : forall Γ Γr,
  ctx_alpha [] Γ Γr ->
  Γ = Γr.
Proof.
  intros Γ Γr H.
  inversion H. reflexivity.
Qed.

Lemma ctx_consume_preserves_names : forall x Γ Γ',
  ctx_consume x Γ = Some Γ' ->
  ctx_names Γ' = ctx_names Γ.
Proof.
  intros x Γ. revert x.
  induction Γ as [| [[[n T] b] m] Γ IH]; intros x Γ' Hconsume.
  - simpl in Hconsume. discriminate.
  - simpl in Hconsume.
    destruct (ident_eqb x n).
    + injection Hconsume as <-. reflexivity.
    + destruct (ctx_consume x Γ) as [Γt |] eqn:Htail.
      2: discriminate.
      injection Hconsume as <-.
      simpl. rewrite (IH x Γt Htail). reflexivity.
Qed.


Lemma ctx_alpha_lookup_backward : forall ρ Γ Γr x T b,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_lookup (lookup_rename x ρ) Γr = Some (T, b) ->
  ctx_lookup x Γ = Some (T, b).
Proof.
  intros ρ Γ Γr x T b Halpha.
  revert x T b.
  induction Halpha; intros y T0 b0 Hsafe Hlookup.
  - simpl in Hlookup. exact Hlookup.
  - simpl in Hsafe, Hlookup.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl in Hlookup.
      rewrite ident_eqb_refl in Hlookup.
      simpl. rewrite ident_eqb_refl. exact Hlookup.
    + simpl in Hlookup.
      assert (Hneq_lookup :
        ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - intro Heq. apply Hsafe. left. symmetry. exact Heq.
      }
      rewrite Hneq_lookup in Hlookup.
      simpl.
      rewrite Hyx.
      apply IHHalpha.
      * exact Hsafe_tail.
      * exact Hlookup.
Qed.

Lemma ctx_alpha_lookup_forward : forall ρ Γ Γr x T b,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_lookup x Γ = Some (T, b) ->
  ctx_lookup (lookup_rename x ρ) Γr = Some (T, b).
Proof.
  intros ρ Γ Γr x T b Halpha.
  revert x T b.
  induction Halpha; intros y T0 b0 Hsafe Hlookup.
  - simpl in Hlookup. exact Hlookup.
  - simpl in Hsafe, Hlookup.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl.
      exact Hlookup.
    + simpl. rewrite Hyx.
      assert (Hneq_lookup :
        ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - exact Hneq_y_xr.
      }
      rewrite Hneq_lookup.
      apply IHHalpha.
      * exact Hsafe_tail.
      * exact Hlookup.
Qed.

Lemma ctx_alpha_lookup_state_backward : forall ρ Γ Γr x T st,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_lookup_state (lookup_rename x ρ) Γr = Some (T, st) ->
  ctx_lookup_state x Γ = Some (T, st).
Proof.
  intros ρ Γ Γr x T st Halpha.
  revert x T st.
  induction Halpha; intros y T0 st0 Hsafe Hlookup.
  - simpl in Hlookup. exact Hlookup.
  - simpl in Hsafe, Hlookup.
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl in Hlookup.
      rewrite ident_eqb_refl in Hlookup.
      simpl. rewrite ident_eqb_refl. exact Hlookup.
    + simpl in Hlookup.
      assert (Hneq_lookup :
        ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - intro Heq. apply Hsafe. left. symmetry. exact Heq.
      }
      rewrite Hneq_lookup in Hlookup.
      simpl. rewrite Hyx.
      apply IHHalpha; assumption.
Qed.

Lemma ctx_alpha_lookup_state_forward : forall ρ Γ Γr x T st,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_lookup_state x Γ = Some (T, st) ->
  ctx_lookup_state (lookup_rename x ρ) Γr = Some (T, st).
Proof.
  intros ρ Γ Γr x T st Halpha.
  revert x T st.
  induction Halpha; intros y T0 st0 Hsafe Hlookup.
  - simpl in Hlookup. exact Hlookup.
  - simpl in Hsafe, Hlookup.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl.
      exact Hlookup.
    + simpl. rewrite Hyx.
      assert (Hneq_lookup :
        ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - exact Hneq_y_xr.
      }
      rewrite Hneq_lookup.
      apply IHHalpha; assumption.
Qed.

Lemma ctx_alpha_consume_backward : forall ρ Γ Γr x Γr',
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_consume (lookup_rename x ρ) Γr = Some Γr' ->
  exists Γ',
    ctx_consume x Γ = Some Γ' /\
    ctx_alpha ρ Γ' Γr'.
Proof.
  intros ρ Γ Γr x Γr' Halpha.
  revert x Γr'.
  induction Halpha; intros y Γr' Hsafe Hconsume.
  - simpl in Hconsume. exists Γr'. split; [exact Hconsume | constructor].
  - simpl in Hsafe, Hconsume.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl in Hconsume.
      rewrite ident_eqb_refl in Hconsume.
      injection Hconsume as <-.
      exists ((x, T, state_consume_path [] b, m) :: Γ).
      split.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * constructor; assumption.
    + simpl in Hconsume.
      assert (Hneq_lookup :
        ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - intro Heq. apply Hsafe. left. symmetry. exact Heq.
      }
      rewrite Hneq_lookup in Hconsume.
      destruct (ctx_consume (lookup_rename y ρ) Γr) as [Γrt |] eqn:Hconsume_tail.
      2: discriminate.
      injection Hconsume as <-.
      destruct (IHHalpha y Γrt Hsafe_tail Hconsume_tail)
        as [Γ' [Hconsume0 Halpha0]].
      exists ((x, T, b, m) :: Γ').
      split.
      * simpl. rewrite Hyx. rewrite Hconsume0. reflexivity.
      * constructor.
        -- exact Halpha0.
        -- rewrite (ctx_consume_preserves_names
             (lookup_rename y ρ) Γr Γrt Hconsume_tail). exact H.
        -- exact H0.
Qed.

Lemma ctx_alpha_consume_forward : forall ρ Γ Γr x Γ',
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_consume x Γ = Some Γ' ->
  exists Γr',
    ctx_consume (lookup_rename x ρ) Γr = Some Γr' /\
    ctx_alpha ρ Γ' Γr'.
Proof.
  intros ρ Γ Γr x Γ' Halpha.
  revert x Γ'.
  induction Halpha; intros y Γ' Hsafe Hconsume.
  - simpl in Hconsume. exists Γ'. split; [exact Hconsume | constructor].
  - simpl in Hsafe, Hconsume.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      injection Hconsume as <-.
      exists ((xr, T, state_consume_path [] b, m) :: Γr).
      split.
      * simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl. reflexivity.
      * constructor; assumption.
    + destruct (ctx_consume y Γ) as [Γt |] eqn:Hconsume_tail.
      2: discriminate.
      injection Hconsume as <-.
      destruct (IHHalpha y Γt Hsafe_tail Hconsume_tail)
        as [Γrt [Hconsume_r_tail Halpha0]].
      exists ((xr, T, b, m) :: Γrt).
      split.
      * simpl. rewrite Hyx.
        assert (Hneq_lookup :
          ident_eqb (lookup_rename y ρ) xr = false).
        { apply ident_eqb_neq.
          apply lookup_rename_not_in_range_neq.
          - exact H0.
          - exact Hneq_y_xr.
        }
        rewrite Hneq_lookup. rewrite Hconsume_r_tail. reflexivity.
      * constructor.
        -- exact Halpha0.
        -- rewrite (ctx_consume_preserves_names
             (lookup_rename y ρ) Γr Γrt Hconsume_r_tail). exact H.
        -- exact H0.
Qed.

Lemma ctx_alpha_update_state_forward : forall ρ Γ Γr x f Γ',
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  sctx_update_state x f Γ = Some Γ' ->
  exists Γr',
    sctx_update_state (lookup_rename x ρ) f Γr = Some Γr' /\
    ctx_alpha ρ Γ' Γr'.
Proof.
  intros ρ Γ Γr x f Γ' Halpha.
  revert x Γ'.
  induction Halpha; intros y Γ' Hsafe Hupdate.
  - simpl in Hupdate. exists Γ'. split; [exact Hupdate | constructor].
  - simpl in Hsafe, Hupdate.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      injection Hupdate as <-.
      exists ((xr, T, f b, m) :: Γr).
      split.
      * simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl. reflexivity.
      * constructor; assumption.
    + destruct (sctx_update_state y f Γ) as [Γt |] eqn:Hupdate_tail.
      2: discriminate.
      injection Hupdate as <-.
      destruct (IHHalpha y Γt Hsafe_tail Hupdate_tail)
        as [Γrt [Hupdate_r_tail Halpha0]].
      exists ((xr, T, b, m) :: Γrt).
      split.
      * simpl. rewrite Hyx.
        assert (Hneq_lookup :
          ident_eqb (lookup_rename y ρ) xr = false).
        { apply ident_eqb_neq.
          apply lookup_rename_not_in_range_neq.
          - exact H0.
          - exact Hneq_y_xr.
        }
        rewrite Hneq_lookup. rewrite Hupdate_r_tail. reflexivity.
      * constructor.
        -- exact Halpha0.
        -- rewrite (sctx_update_state_names
             (lookup_rename y ρ) f Γr Γrt Hupdate_r_tail). exact H.
        -- exact H0.
Qed.

Lemma ctx_alpha_path_available_forward : forall ρ Γ Γr x path,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  sctx_path_available Γ x path = infer_ok tt ->
  sctx_path_available Γr (lookup_rename x ρ) path = infer_ok tt.
Proof.
  intros ρ Γ Γr x path Halpha Hsafe Havailable.
  unfold sctx_path_available, sctx_lookup in *.
  destruct (ctx_lookup_state x Γ) as [[T st] |] eqn:Hlookup;
    try discriminate.
  pose proof (ctx_alpha_lookup_state_forward
    ρ Γ Γr x T st Halpha Hsafe Hlookup) as Hlookup_r.
  rewrite Hlookup_r.
  destruct (binding_available_b st path); inversion Havailable.
  reflexivity.
Qed.

Lemma ctx_alpha_consume_path_forward : forall ρ Γ Γr x path Γ',
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  sctx_consume_path Γ x path = infer_ok Γ' ->
  exists Γr',
    sctx_consume_path Γr (lookup_rename x ρ) path = infer_ok Γr' /\
    ctx_alpha ρ Γ' Γr'.
Proof.
  intros ρ Γ Γr x path Γ' Halpha Hsafe Hconsume.
  unfold sctx_consume_path in Hconsume.
  destruct (sctx_path_available Γ x path) as [[] | err] eqn:Havailable;
    try discriminate.
  destruct (sctx_update_state x (state_consume_path path) Γ)
    as [Γ0 |] eqn:Hupdate; try discriminate.
  injection Hconsume as <-.
  destruct (ctx_alpha_update_state_forward
    ρ Γ Γr x (state_consume_path path) Γ0 Halpha Hsafe Hupdate)
    as [Γr' [Hupdate_r Halpha_r]].
  exists Γr'. split.
  - unfold sctx_consume_path.
    rewrite (ctx_alpha_path_available_forward
      ρ Γ Γr x path Halpha Hsafe Havailable).
    rewrite Hupdate_r. reflexivity.
  - exact Halpha_r.
Qed.

Lemma ctx_alpha_restore_path_forward : forall ρ Γ Γr x path Γ',
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  sctx_restore_path Γ x path = infer_ok Γ' ->
  exists Γr',
    sctx_restore_path Γr (lookup_rename x ρ) path = infer_ok Γr' /\
    ctx_alpha ρ Γ' Γr'.
Proof.
  intros ρ Γ Γr x path Γ' Halpha Hsafe Hrestore.
  unfold sctx_restore_path in Hrestore.
  destruct (sctx_update_state x (state_restore_path path) Γ)
    as [Γ0 |] eqn:Hupdate; try discriminate.
  injection Hrestore as <-.
  destruct (ctx_alpha_update_state_forward
    ρ Γ Γr x (state_restore_path path) Γ0 Halpha Hsafe Hupdate)
    as [Γr' [Hupdate_r Halpha_r]].
  exists Γr'. split.
  - unfold sctx_restore_path. rewrite Hupdate_r. reflexivity.
  - exact Halpha_r.
Qed.

Lemma ctx_alpha_check_ok_forward : forall env ρ Γ Γr x T,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  sctx_check_ok env x T Γ = true ->
  sctx_check_ok env (lookup_rename x ρ) T Γr = true.
Proof.
  intros env ρ Γ Γr x T Halpha Hsafe Hok.
  unfold sctx_check_ok, sctx_lookup in *.
  destruct (ty_usage T); try exact Hok.
  destruct (ctx_lookup_state x Γ) as [[Tx st] |] eqn:Hlookup; try discriminate.
  rewrite (ctx_alpha_lookup_state_forward ρ Γ Γr x Tx st Halpha Hsafe Hlookup).
  exact Hok.
Qed.

Lemma ctx_alpha_add_fresh_forward : forall ρ Γ Γr x xr T m,
  ctx_alpha ρ Γ Γr ->
  ~ In xr (ctx_names Γr) ->
  ~ In xr (rename_range ρ) ->
  ctx_alpha ((x, xr) :: ρ)
    (sctx_add x T m Γ) (sctx_add xr T m Γr).
Proof.
  intros ρ Γ Γr x xr T m Halpha Hfresh_ctx Hfresh_range.
  unfold sctx_add, ctx_add. constructor; assumption.
Qed.

Lemma ctx_alpha_add_fresh_inv : forall ρ Γ Γr x xr T m,
  ctx_alpha ((x, xr) :: ρ)
    (sctx_add x T m Γ) (sctx_add xr T m Γr) ->
  ctx_alpha ρ Γ Γr /\
  ~ In xr (ctx_names Γr) /\
  ~ In xr (rename_range ρ).
Proof.
  intros ρ Γ Γr x xr T m Halpha.
  unfold sctx_add, ctx_add in Halpha.
  inversion Halpha; subst.
  repeat split; assumption.
Qed.

Lemma ctx_alpha_remove_head : forall ρ Γ Γr x xr T b m,
  ctx_alpha ρ Γ Γr ->
  ctx_alpha ρ
    (ctx_remove x ((x, T, b, m) :: Γ))
    (ctx_remove xr ((xr, T, b, m) :: Γr)).
Proof.
  intros ρ Γ Γr x xr T b m Halpha.
  simpl.
  rewrite ident_eqb_refl.
  rewrite ident_eqb_refl.
  exact Halpha.
Qed.

Lemma ctx_alpha_remove_bound : forall ρ Γ Γr x xr,
  ctx_alpha ((x, xr) :: ρ) Γ Γr ->
  ctx_alpha ρ (ctx_remove x Γ) (ctx_remove xr Γr).
Proof.
  intros ρ Γ Γr x xr Halpha.
  inversion Halpha; subst.
  simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl.
  assumption.
Qed.

Lemma ctx_alpha_lookup_mut_backward : forall ρ Γ Γr x m,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_lookup_mut (lookup_rename x ρ) Γr = Some m ->
  ctx_lookup_mut x Γ = Some m.
Proof.
  intros ρ Γ Γr x m Halpha.
  revert x m.
  induction Halpha; intros y m0 Hsafe Hlookup.
  - simpl in Hlookup. exact Hlookup.
  - simpl in Hsafe, Hlookup.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl in Hlookup. rewrite ident_eqb_refl in Hlookup.
      simpl. rewrite ident_eqb_refl. exact Hlookup.
    + simpl in Hlookup.
      assert (Hneq_lookup : ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - exact Hneq_y_xr. }
      rewrite Hneq_lookup in Hlookup.
      simpl. rewrite Hyx.
      apply IHHalpha.
      * exact Hsafe_tail.
      * exact Hlookup.
Qed.

Lemma ctx_alpha_lookup_mut_forward : forall ρ Γ Γr x m,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_lookup_mut x Γ = Some m ->
  ctx_lookup_mut (lookup_rename x ρ) Γr = Some m.
Proof.
  intros ρ Γ Γr x m Halpha.
  revert x m.
  induction Halpha; intros y m0 Hsafe Hlookup.
  - simpl in Hlookup. exact Hlookup.
  - simpl in Hsafe, Hlookup.
    assert (Hneq_y_xr : y <> xr).
    { intro Heq. apply Hsafe. left. symmetry. exact Heq. }
    assert (Hsafe_tail : ~ In y (rename_range ρ)).
    { intro Hin. apply Hsafe. right. exact Hin. }
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl.
      exact Hlookup.
    + simpl. rewrite Hyx.
      assert (Hneq_lookup : ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - exact Hneq_y_xr. }
      rewrite Hneq_lookup.
      apply IHHalpha.
      * exact Hsafe_tail.
      * exact Hlookup.
Qed.

Lemma check_make_closure_captures_sctx_alpha_forward :
  forall env ρ Σ Σr Ω captures params captured_tys,
    ctx_alpha ρ Σ Σr ->
    disjoint_names captures (rename_range ρ) ->
    check_make_closure_captures_sctx env Ω Σ captures params =
      infer_ok captured_tys ->
    check_make_closure_captures_sctx env Ω Σr
      (map (fun x => lookup_rename x ρ) captures) params =
      infer_ok captured_tys.
Proof.
  intros env ρ Σ Σr Ω captures.
  induction captures as [| x captures IH]; intros params captured_tys Halpha Hdisj Hcheck;
    destruct params as [| cap params]; simpl in *; try discriminate.
  - exact Hcheck.
  - destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    change (sctx_lookup (lookup_rename x ρ) Σr) with
      (ctx_lookup_state (lookup_rename x ρ) Σr).
    rewrite (ctx_alpha_lookup_state_forward ρ Σ Σr x T st Halpha
      ltac:(apply Hdisj; simpl; left; reflexivity) Hlookup).
    destruct (negb (binding_available_b st [])); try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    change (sctx_lookup_mut (lookup_rename x ρ) Σr) with
      (ctx_lookup_mut (lookup_rename x ρ) Σr).
    rewrite (ctx_alpha_lookup_mut_forward ρ Σ Σr x m Halpha
      ltac:(apply Hdisj; simpl; left; reflexivity) Hmut).
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted); try discriminate.
    destruct (capture_ref_free_ty_b env T); try discriminate.
    destruct (ty_compatible_b Ω T (param_ty cap)); try discriminate.
    destruct (check_make_closure_captures_sctx env Ω Σ captures params)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    rewrite (IH params captured_rest Halpha
      ltac:(intros y Hy; apply Hdisj; simpl; right; exact Hy) Hrest).
    reflexivity.
Qed.

Lemma check_make_closure_captures_sctx_base_alpha_forward :
  forall env ρ Σ Σr Ω captures params captured_tys,
    ctx_alpha ρ Σ Σr ->
    disjoint_names captures (rename_range ρ) ->
    check_make_closure_captures_sctx_base env Ω Σ captures params =
      infer_ok captured_tys ->
    check_make_closure_captures_sctx_base env Ω Σr
      (map (fun x => lookup_rename x ρ) captures) params =
      infer_ok captured_tys.
Proof.
  intros env ρ Σ Σr Ω captures.
  induction captures as [| x captures IH]; intros params captured_tys Halpha Hdisj Hcheck;
    destruct params as [| cap params]; simpl in *; try discriminate.
  - exact Hcheck.
  - destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    change (sctx_lookup (lookup_rename x ρ) Σr) with
      (ctx_lookup_state (lookup_rename x ρ) Σr).
    rewrite (ctx_alpha_lookup_state_forward ρ Σ Σr x T st Halpha
      ltac:(apply Hdisj; simpl; left; reflexivity) Hlookup).
    destruct (negb (binding_available_b st [])); try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    change (sctx_lookup_mut (lookup_rename x ρ) Σr) with
      (ctx_lookup_mut (lookup_rename x ρ) Σr).
    rewrite (ctx_alpha_lookup_mut_forward ρ Σ Σr x m Halpha
      ltac:(apply Hdisj; simpl; left; reflexivity) Hmut).
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted); try discriminate.
    destruct (ty_compatible_b Ω T (param_ty cap)); try discriminate.
    destruct (check_make_closure_captures_sctx_base env Ω Σ captures params)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    rewrite (IH params captured_rest Halpha
      ltac:(intros y Hy; apply Hdisj; simpl; right; exact Hy) Hrest).
    reflexivity.
Qed.

Lemma check_make_closure_captures_sctx_with_env_alpha_forward :
  forall env ρ Σ Σr Ω captures params env_lt captured_tys,
    ctx_alpha ρ Σ Σr ->
    disjoint_names captures (rename_range ρ) ->
    check_make_closure_captures_sctx_with_env env Ω Σ captures params =
      infer_ok (env_lt, captured_tys) ->
    check_make_closure_captures_sctx_with_env env Ω Σr
      (map (fun x => lookup_rename x ρ) captures) params =
      infer_ok (env_lt, captured_tys).
Proof.
  intros env ρ Σ Σr Ω captures params env_lt captured_tys Halpha Hdisj Hcheck.
  unfold check_make_closure_captures_sctx_with_env in *.
  destruct (check_make_closure_captures_sctx_base env Ω Σ captures params)
    as [captured_tys0 | err] eqn:Hbase; try discriminate.
  rewrite (check_make_closure_captures_sctx_base_alpha_forward
    env ρ Σ Σr Ω captures params captured_tys0 Halpha Hdisj Hbase).
  exact Hcheck.
Qed.

Lemma check_make_closure_captures_exact_sctx_alpha_forward :
  forall env ρ Σ Σr Ω captures params captured_tys,
    ctx_alpha ρ Σ Σr ->
    disjoint_names captures (rename_range ρ) ->
    check_make_closure_captures_exact_sctx env Ω Σ captures params =
      infer_ok captured_tys ->
    check_make_closure_captures_sctx env Ω Σr
      (map (fun x => lookup_rename x ρ) captures) params =
      infer_ok captured_tys.
Proof.
  intros env ρ Σ Σr Ω captures params captured_tys Halpha Hdisj Hcheck.
  eapply check_make_closure_captures_sctx_alpha_forward; eauto.
  eapply check_make_closure_captures_exact_sctx_implies_sctx.
  exact Hcheck.
Qed.

