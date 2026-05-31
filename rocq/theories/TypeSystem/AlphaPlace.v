From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Import AlphaCore AlphaCtx.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Place alpha-renaming facts                                          *)
(* ------------------------------------------------------------------ *)

(* Alpha-renaming relation for places: rename_place ρ maps PVar x to
   PVar (lookup_rename x ρ) and PDeref recursively. *)
Inductive place_alpha (ρ : rename_env) : place -> place -> Prop :=
  | PA_Var : forall x,
      ~ In x (rename_range ρ) ->
      place_alpha ρ (PVar x) (PVar (lookup_rename x ρ))
  | PA_Deref : forall p pr,
      place_alpha ρ p pr ->
      place_alpha ρ (PDeref p) (PDeref pr)
  | PA_Field : forall p pr f,
      place_alpha ρ p pr ->
      place_alpha ρ (PField p f) (PField pr f).

(* place_name gives the root variable; disjointness of root ↔ place_alpha holds. *)
Lemma rename_place_alpha_sound : forall ρ p,
  ~ In (place_name p) (rename_range ρ) ->
  place_alpha ρ p (rename_place ρ p).
Proof.
  intros ρ p Hdisj. induction p; simpl in *.
  - apply PA_Var. exact Hdisj.
  - apply PA_Deref. apply IHp. exact Hdisj.
  - apply PA_Field. apply IHp. exact Hdisj.
Qed.

Lemma place_name_root : forall p,
  place_name p = place_root p.
Proof.
  induction p; simpl; auto.
Qed.

Lemma place_root_rename_place : forall ρ p,
  place_root (rename_place ρ p) = lookup_rename (place_root p) ρ.
Proof.
  induction p; simpl; auto.
Qed.


Lemma alpha_rename_typed_place_backward : forall fenv0 fenvr n ρ Γ0 Γr p T,
  ctx_alpha ρ Γ0 Γr ->
  ~ In (place_root p) (rename_range ρ) ->
  typed_place fenvr n Γr (rename_place ρ p) T ->
  typed_place fenv0 n Γ0 p T.
Proof.
  intros fenv0 fenvr n ρ Γ0 Γr p.
  induction p as [x | p IH | p IH f]; intros T Hctx Hsafe Htyped_place.
  - simpl in Htyped_place. inversion Htyped_place; subst.
    apply TP_Var.
    eapply ctx_alpha_lookup_backward; eauto.
  - simpl in Htyped_place. inversion Htyped_place; subst.
    eapply TP_Deref.
    apply IH.
    + exact Hctx.
    + exact Hsafe.
    + exact H0.
  - simpl in Htyped_place. inversion Htyped_place; subst.
    eapply TP_Field; eauto.
Qed.

Lemma alpha_rename_typed_place_forward : forall fenv0 fenvr n ρ Γ0 Γr p T,
  ctx_alpha ρ Γ0 Γr ->
  ~ In (place_root p) (rename_range ρ) ->
  typed_place fenv0 n Γ0 p T ->
  typed_place fenvr n Γr (rename_place ρ p) T.
Proof.
  intros fenv0 fenvr n ρ Γ0 Γr p.
  induction p as [x | p IH | p IH f]; intros T Hctx Hsafe Htyped_place.
  - simpl. inversion Htyped_place; subst.
    apply TP_Var.
    eapply ctx_alpha_lookup_forward; eauto.
  - simpl. inversion Htyped_place; subst.
    eapply TP_Deref.
    apply IH.
    + exact Hctx.
    + exact Hsafe.
    + exact H0.
  - simpl. inversion Htyped_place; subst.
    eapply TP_Field; eauto.
Qed.

Lemma place_path_rename_place_some : forall ρ p x path,
  place_path p = Some (x, path) ->
  place_path (rename_place ρ p) = Some (lookup_rename x ρ, path).
Proof.
  intros ρ p.
  induction p as [y | p IH | p IH f]; intros x path Hpath.
  - simpl in Hpath. injection Hpath as <- <-. reflexivity.
  - simpl in Hpath. discriminate.
  - simpl.
    simpl in Hpath.
    remember (place_path p) as parent eqn:Hparent_eq.
    symmetry in Hparent_eq.
    destruct parent as [[y path0] |]; try discriminate.
    specialize (IH y path0 eq_refl).
    injection Hpath as <- <-.
    rewrite IH.
    reflexivity.
Qed.

Lemma place_resolved_write_direct_parent_rename : forall ρ p,
  place_resolved_write_direct_parent p ->
  place_resolved_write_direct_parent (rename_place ρ p).
Proof.
  intros ρ p [q [x [path [Hp Hpath]]]].
  subst p.
  exists (rename_place ρ q), (lookup_rename x ρ), path.
  split; [reflexivity |].
  apply place_path_rename_place_some. exact Hpath.
Qed.

Lemma place_resolved_write_shape_rename : forall ρ p,
  place_resolved_write_shape p ->
  place_resolved_write_shape (rename_place ρ p).
Proof.
  intros ρ p Hshape.
  induction Hshape.
  - apply PRWS_Direct.
    apply place_resolved_write_direct_parent_rename. exact H.
  - simpl. apply PRWS_Deref. exact IHHshape.
  - simpl. apply PRWS_Field. exact IHHshape.
Qed.

Lemma place_path_rename_place_none : forall ρ p,
  place_path p = None ->
  place_path (rename_place ρ p) = None.
Proof.
  intros ρ p.
  induction p as [x | p IH | p IH f]; intros Hpath.
  - simpl in Hpath. discriminate.
  - reflexivity.
  - simpl.
    simpl in Hpath.
    remember (place_path p) as parent eqn:Hparent_eq.
    symmetry in Hparent_eq.
    destruct parent as [[x path] |]; try discriminate.
    specialize (IH eq_refl).
    rewrite IH.
    reflexivity.
Qed.

Lemma place_path_root : forall p x path,
  place_path p = Some (x, path) ->
  place_root p = x.
Proof.
  fix IH 1.
  intros p x path Hpath.
  destruct p as [y | p | p f]; simpl in Hpath.
  - injection Hpath as <- _. reflexivity.
  - discriminate.
  - destruct (place_path p) as [[y path0] |] eqn:Hparent;
      try discriminate.
    injection Hpath as <- _.
    simpl. eapply IH. exact Hparent.
Qed.

Lemma alpha_rename_typed_place_type_env_structural_forward :
  forall env ρ Σ Σr p T,
    ctx_alpha ρ Σ Σr ->
    ~ In (place_root p) (rename_range ρ) ->
    typed_place_type_env_structural env Σ p T ->
    typed_place_type_env_structural env Σr (rename_place ρ p) T.
Proof.
  intros env ρ Σ Σr p T Hctx Hsafe Hplace.
  induction Hplace.
  - simpl. eapply TPTES_Var.
    eapply ctx_alpha_lookup_state_forward; eauto.
  - simpl. eapply TPTES_Deref.
    apply IHHplace. exact Hsafe.
  - simpl. eapply TPTES_Field; eauto.
Qed.

Lemma alpha_rename_typed_place_env_structural_forward :
  forall env ρ Σ Σr p T,
    ctx_alpha ρ Σ Σr ->
    ~ In (place_root p) (rename_range ρ) ->
    typed_place_env_structural env Σ p T ->
    typed_place_env_structural env Σr (rename_place ρ p) T.
Proof.
  intros env ρ Σ Σr p T Hctx Hsafe Hplace.
  induction Hplace.
  - simpl. eapply TPES_Var.
    + eapply ctx_alpha_lookup_state_forward; eauto.
    + exact H0.
  - simpl. eapply TPES_Deref.
    apply IHHplace. exact Hsafe.
  - simpl. eapply TPES_Field.
    + eapply alpha_rename_typed_place_type_env_structural_forward; eauto.
    + exact H0.
    + exact H1.
    + exact H2.
    + pose proof (place_path_rename_place_some ρ
        (PField p (Program.field_name fdef)) x path H3) as Hpathr.
      simpl in Hpathr. exact Hpathr.
    + eapply ctx_alpha_lookup_state_forward.
      * exact Hctx.
      * rewrite <- (place_path_root
          (PField p (Program.field_name fdef)) x path H3).
        exact Hsafe.
      * exact H4.
    + exact H5.
  - simpl. eapply TPES_Field_Indirect.
    + eapply alpha_rename_typed_place_type_env_structural_forward; eauto.
    + exact H0.
    + exact H1.
    + exact H2.
    + pose proof (place_path_rename_place_none ρ
        (PField p (Program.field_name fdef)) H3) as Hpathr.
      simpl in Hpathr. exact Hpathr.
Qed.

Lemma alpha_rename_writable_place_env_structural_forward :
  forall env ρ Σ Σr p,
    ctx_alpha ρ Σ Σr ->
    ~ In (place_root p) (rename_range ρ) ->
    writable_place_env_structural env Σ p ->
    writable_place_env_structural env Σr (rename_place ρ p).
Proof.
  intros env ρ Σ Σr p Hctx Hsafe Hwrite.
  induction Hwrite.
  - simpl. apply WPES_Var.
    eapply ctx_alpha_lookup_mut_forward; eauto.
  - simpl. eapply WPES_Deref.
    eapply alpha_rename_typed_place_env_structural_forward; eauto.
  - simpl. eapply WPES_Field.
    + apply IHHwrite. exact Hsafe.
    + eapply alpha_rename_typed_place_type_env_structural_forward; eauto.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
Qed.

Lemma alpha_rename_place_under_unique_ref_structural_forward :
  forall env ρ Σ Σr p,
    ctx_alpha ρ Σ Σr ->
    ~ In (place_root p) (rename_range ρ) ->
    place_under_unique_ref_structural env Σ p ->
    place_under_unique_ref_structural env Σr (rename_place ρ p).
Proof.
  intros env ρ Σ Σr p Hctx Hsafe Hunique.
  induction Hunique.
  - simpl. eapply PUURS_Deref.
    eapply alpha_rename_typed_place_env_structural_forward; eauto.
  - simpl. apply PUURS_Field.
    apply IHHunique. exact Hsafe.
Qed.

