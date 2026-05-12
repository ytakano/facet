From Facet.TypeSystem Require Import Types Syntax TypingRules TypeChecker.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

Scheme typed_ind' := Induction for typed Sort Prop
with typed_args_ind' := Induction for typed_args Sort Prop.
Combined Scheme typed_typed_args_ind from typed_ind', typed_args_ind'.

(* ------------------------------------------------------------------ *)

Fixpoint rename_range (ρ : rename_env) : list ident :=
  match ρ with
  | [] => []
  | (_, xr) :: ρ' => xr :: rename_range ρ'
  end.

Definition disjoint_names (xs ys : list ident) : Prop :=
  forall x, In x xs -> ~ In x ys.

Lemma disjoint_names_nil_l : forall xs,
  disjoint_names [] xs.
Proof.
  intros xs x Hin. contradiction.
Qed.

Lemma disjoint_names_nil_r : forall xs,
  disjoint_names xs [].
Proof.
  intros xs x Hin Hnil. contradiction.
Qed.

Lemma disjoint_names_cons_l : forall x xs ys,
  disjoint_names (x :: xs) ys ->
  ~ In x ys /\ disjoint_names xs ys.
Proof.
  intros x xs ys H.
  split.
  - apply H. simpl. left. reflexivity.
  - intros y Hy. apply H. simpl. right. exact Hy.
Qed.

Lemma disjoint_names_app_l : forall xs ys zs,
  disjoint_names (xs ++ ys) zs ->
  disjoint_names xs zs /\ disjoint_names ys zs.
Proof.
  intros xs ys zs H.
  split; intros x Hin; apply H; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma ident_in_false_not_in : forall x xs,
  ident_in x xs = false ->
  ~ In x xs.
Proof.
  intros x xs. induction xs as [| y ys IH]; intros H Hin.
  - contradiction.
  - simpl in H, Hin.
    destruct (ident_eqb x y) eqn:Heq.
    + discriminate.
    + destruct Hin as [Heqxy | Hin].
      * subst. rewrite ident_eqb_refl in Heq.
        discriminate.
      * eapply IH; eauto.
Qed.

Lemma max_ident_index_ge : forall base n used,
  In (base, n) used ->
  n <= max_ident_index base used.
Proof.
  intros base n used. induction used as [| [base0 n0] used IH]; intros Hin.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst. simpl.
      rewrite String.eqb_refl. lia.
    + simpl.
      pose proof (IH Hin) as Hle.
      destruct (String.eqb base base0); lia.
Qed.

Lemma fresh_ident_not_in : forall x used,
  ~ In (fresh_ident x used) used.
Proof.
  intros [base n] used Hin.
  unfold fresh_ident in Hin. simpl in Hin.
  pose proof (max_ident_index_ge base (S (max_ident_index base used))
    used Hin).
  lia.
Qed.


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

(* Alpha-renaming relation for places: rename_place ρ maps PVar x to
   PVar (lookup_rename x ρ) and PDeref recursively. *)
Inductive place_alpha (ρ : rename_env) : place -> place -> Prop :=
  | PA_Var : forall x,
      ~ In x (rename_range ρ) ->
      place_alpha ρ (PVar x) (PVar (lookup_rename x ρ))
  | PA_Deref : forall p pr,
      place_alpha ρ p pr ->
      place_alpha ρ (PDeref p) (PDeref pr).

(* place_name gives the root variable; disjointness of root ↔ place_alpha holds. *)
Lemma rename_place_alpha_sound : forall ρ p,
  ~ In (place_name p) (rename_range ρ) ->
  place_alpha ρ p (rename_place ρ p).
Proof.
  intros ρ p Hdisj. induction p; simpl in *.
  - apply PA_Var. exact Hdisj.
  - apply PA_Deref. apply IHp. exact Hdisj.
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

Inductive expr_alpha : rename_env -> expr -> expr -> Prop :=
  | EA_Unit : forall ρ,
      expr_alpha ρ EUnit EUnit
  | EA_Lit : forall ρ l,
      expr_alpha ρ (ELit l) (ELit l)
  | EA_Var : forall ρ x,
      ~ In x (rename_range ρ) ->
      expr_alpha ρ (EVar x) (EVar (lookup_rename x ρ))
  | EA_Let : forall ρ m x xr T e1 e1r e2 e2r,
      expr_alpha ρ e1 e1r ->
      expr_alpha ((x, xr) :: ρ) e2 e2r ->
      expr_alpha ρ (ELet m x T e1 e2) (ELet m xr T e1r e2r)
  | EA_LetInfer : forall ρ m x xr e1 e1r e2 e2r,
      expr_alpha ρ e1 e1r ->
      expr_alpha ((x, xr) :: ρ) e2 e2r ->
      expr_alpha ρ (ELetInfer m x e1 e2) (ELetInfer m xr e1r e2r)
  | EA_Call : forall ρ fname args argsr,
      exprs_alpha ρ args argsr ->
      expr_alpha ρ (ECall fname args) (ECall fname argsr)
  | EA_Replace : forall ρ p pr e er,
      place_alpha ρ p pr ->
      expr_alpha ρ e er ->
      expr_alpha ρ (EReplace p e) (EReplace pr er)
  | EA_Assign : forall ρ p pr e er,
      place_alpha ρ p pr ->
      expr_alpha ρ e er ->
      expr_alpha ρ (EAssign p e) (EAssign pr er)
  | EA_Borrow : forall ρ rk p pr,
      place_alpha ρ p pr ->
      expr_alpha ρ (EBorrow rk p) (EBorrow rk pr)
  | EA_Deref : forall ρ e er,
      expr_alpha ρ e er ->
      expr_alpha ρ (EDeref e) (EDeref er)
  | EA_Drop : forall ρ e er,
      expr_alpha ρ e er ->
      expr_alpha ρ (EDrop e) (EDrop er)
  | EA_If : forall ρ e1 e1r e2 e2r e3 e3r,
      expr_alpha ρ e1 e1r ->
      expr_alpha ρ e2 e2r ->
      expr_alpha ρ e3 e3r ->
      expr_alpha ρ (EIf e1 e2 e3) (EIf e1r e2r e3r)
with exprs_alpha : rename_env -> list expr -> list expr -> Prop :=
  | EAs_Nil : forall ρ,
      exprs_alpha ρ [] []
  | EAs_Cons : forall ρ e er es esr,
      expr_alpha ρ e er ->
      exprs_alpha ρ es esr ->
      exprs_alpha ρ (e :: es) (er :: esr).

Definition same_param_shape (p pr : param) : Prop :=
  param_mutability p = param_mutability pr /\
  param_ty p = param_ty pr.

Inductive params_alpha : list param -> list param -> Prop :=
  | ParamsAlpha_Nil :
      params_alpha [] []
  | ParamsAlpha_Cons : forall p pr ps psr,
      same_param_shape p pr ->
      params_alpha ps psr ->
      params_alpha (p :: ps) (pr :: psr).

Definition same_fn_shape (f fr : fn_def) : Prop :=
  fn_name f = fn_name fr /\
  fn_ret f = fn_ret fr /\
  params_alpha (fn_params f) (fn_params fr).

Inductive fenv_alpha : list fn_def -> list fn_def -> Prop :=
  | FenvAlpha_Nil :
      fenv_alpha [] []
  | FenvAlpha_Cons : forall f fr fs fsr,
      same_fn_shape f fr ->
      fenv_alpha fs fsr ->
      fenv_alpha (f :: fs) (fr :: fsr).

Lemma fenv_alpha_in_backward : forall fenv fenvr fr,
  fenv_alpha fenv fenvr ->
  In fr fenvr ->
  exists f,
    In f fenv /\
    same_fn_shape f fr.
Proof.
  intros fenv fenvr fr Halpha Hin.
  induction Halpha.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst fr. exists f. split; [left; reflexivity | assumption].
    + destruct (IHHalpha Hin) as [f0 [Hin0 Hshape]].
      exists f0. split; [right; exact Hin0 | exact Hshape].
Qed.

Lemma lookup_rename_in_range_or_self : forall ρ x,
  In (lookup_rename x ρ) (rename_range ρ) \/ lookup_rename x ρ = x.
Proof.
  intros ρ x.
  induction ρ as [| [old fresh] ρ IH].
  - simpl. right. reflexivity.
  - simpl.
    destruct (ident_eqb x old) eqn:Heq.
    + left. left. reflexivity.
    + destruct IH as [Hin | Heq_lookup].
      * left. right. exact Hin.
      * right. exact Heq_lookup.
Qed.

Lemma lookup_rename_not_in_range_neq : forall ρ x y,
  ~ In y (rename_range ρ) ->
  x <> y ->
  lookup_rename x ρ <> y.
Proof.
  intros ρ x y Hnot Hyx Heq.
  destruct (lookup_rename_in_range_or_self ρ x) as [Hin | Hself].
  - rewrite Heq in Hin. contradiction.
  - rewrite Hself in Heq. contradiction.
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
        - apply ident_eqb_neq in Hyx. intro Heq. subst y. contradiction.
      }
      rewrite Hneq_lookup in Hlookup.
      simpl.
      rewrite Hyx.
      apply IHHalpha.
      * exact Hsafe_tail.
      * exact Hlookup.
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
      exists ((x, T, true, m) :: Γ).
      split.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * constructor; assumption.
    + simpl in Hconsume.
      assert (Hneq_lookup :
        ident_eqb (lookup_rename y ρ) xr = false).
      { apply ident_eqb_neq.
        apply lookup_rename_not_in_range_neq.
        - exact H0.
        - apply ident_eqb_neq in Hyx. intro Heq. subst y. contradiction.
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

Lemma alpha_rename_typed_place_backward : forall fenv0 fenvr n ρ Γ0 Γr p T,
  ctx_alpha ρ Γ0 Γr ->
  ~ In (place_root p) (rename_range ρ) ->
  typed_place fenvr n Γr (rename_place ρ p) T ->
  typed_place fenv0 n Γ0 p T.
Proof.
  intros fenv0 fenvr n ρ Γ0 Γr p.
  induction p as [x | p IH]; intros T Hctx Hsafe Htyped_place.
  - simpl in Htyped_place. inversion Htyped_place; subst.
    apply TP_Var.
    eapply ctx_alpha_lookup_backward; eauto.
  - simpl in Htyped_place. inversion Htyped_place; subst.
    eapply TP_Deref.
    apply IH.
    + exact Hctx.
    + exact Hsafe.
    + exact H0.
Qed.

Lemma ctx_alpha_is_ok_backward : forall ρ Γ Γr x T,
  ctx_alpha ρ Γ Γr ->
  ~ In x (rename_range ρ) ->
  ctx_is_ok (lookup_rename x ρ) T Γr ->
  ctx_is_ok x T Γ.
Proof.
  intros ρ Γ Γr x T Halpha Hsafe Hok.
  unfold ctx_is_ok in *.
  destruct (ty_usage T); try exact I.
  destruct (ctx_lookup (lookup_rename x ρ) Γr) as [[Tx b] |] eqn:Hlookup;
    try contradiction.
  destruct b; try contradiction.
  rewrite (ctx_alpha_lookup_backward ρ Γ Γr x Tx true Halpha Hsafe Hlookup).
  exact I.
Qed.

Inductive ctx_same_bindings : ctx -> ctx -> Prop :=
  | CtxSame_Nil :
      ctx_same_bindings [] []
  | CtxSame_Cons : forall x T b b' m Γ Γ',
      ctx_same_bindings Γ Γ' ->
      ctx_same_bindings ((x, T, b, m) :: Γ) ((x, T, b', m) :: Γ').

Lemma ctx_same_bindings_refl : forall Γ,
  ctx_same_bindings Γ Γ.
Proof.
  induction Γ as [| [[[x T] b] m] Γ IH].
  - constructor.
  - constructor. exact IH.
Qed.

Lemma ctx_same_bindings_names : forall Γ Γ',
  ctx_same_bindings Γ Γ' ->
  ctx_names Γ' = ctx_names Γ.
Proof.
  intros Γ Γ' Hsame.
  induction Hsame; simpl; [reflexivity |].
  rewrite IHHsame. reflexivity.
Qed.

Lemma ctx_same_bindings_trans : forall Γ1 Γ2 Γ3,
  ctx_same_bindings Γ1 Γ2 ->
  ctx_same_bindings Γ2 Γ3 ->
  ctx_same_bindings Γ1 Γ3.
Proof.
  intros Γ1 Γ2 Γ3 H12 H23.
  revert Γ3 H23.
  induction H12 as [| x T b b' m Γ Γ' H12 IH]; intros Γ3 H23.
  - inversion H23; subst. constructor.
  - inversion H23; subst. constructor.
    match goal with
    | Htail : ctx_same_bindings Γ' _ |- _ => eapply IH; exact Htail
    end.
Qed.

Lemma ctx_consume_same_bindings : forall x Γ Γ',
  ctx_consume x Γ = Some Γ' ->
  ctx_same_bindings Γ Γ'.
Proof.
  intros x Γ. revert x.
  induction Γ as [| [[[n T] b] m] Γ IH]; intros x Γ' Hconsume.
  - discriminate.
  - simpl in Hconsume.
    destruct (ident_eqb x n).
    + injection Hconsume as <-. constructor. apply ctx_same_bindings_refl.
    + destruct (ctx_consume x Γ) as [Γt |] eqn:Htail.
      2: discriminate.
      injection Hconsume as <-.
      constructor. eapply IH. exact Htail.
Qed.

Lemma ctx_remove_same_bindings_head : forall x T b b' m Γ Γ',
  ctx_same_bindings Γ Γ' ->
  ctx_remove x ((x, T, b, m) :: Γ) = Γ ->
  ctx_remove x ((x, T, b', m) :: Γ') = Γ'.
Proof.
  intros x T b b' m Γ Γ' _ _.
  simpl. rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma ctx_same_bindings_remove_head : forall x T b m Γ Γ',
  ctx_same_bindings ((x, T, b, m) :: Γ) Γ' ->
  ctx_same_bindings Γ (ctx_remove x Γ').
Proof.
  intros x T b m Γ Γ' Hsame.
  inversion Hsame; subst.
  simpl. rewrite ident_eqb_refl. assumption.
Qed.

Lemma ctx_merge_same_bindings : forall Γ2 Γ3 Γ4,
  ctx_merge Γ2 Γ3 = Some Γ4 ->
  ctx_same_bindings Γ2 Γ4.
Proof.
  intros Γ2. induction Γ2 as [| [[[n T] b2] m] t2 IH]; intros Γ3 Γ4 Hmerge.
  - destruct Γ3; simpl in Hmerge; [injection Hmerge as <-; constructor | discriminate].
  - destruct Γ3 as [| [[[n' T'] b3] m3] t3]; [discriminate |].
    simpl in Hmerge.
    destruct (ident_eqb n n') eqn:Hnn'; [|discriminate].
    simpl in Hmerge.
    destruct (ctx_merge t2 t3) as [rest |] eqn:Hrest; [|discriminate].
    destruct (ty_usage T) eqn:Hu.
    + destruct (Bool.eqb b2 b3) eqn:Heqb; [|discriminate].
      injection Hmerge as <-. constructor. eapply IH. exact Hrest.
    + injection Hmerge as <-. constructor. eapply IH. exact Hrest.
    + injection Hmerge as <-. constructor. eapply IH. exact Hrest.
Qed.

Lemma typed_same_bindings :
  (forall fenv n Γ e T Γ',
      typed fenv n Γ e T Γ' ->
      ctx_same_bindings Γ Γ') /\
  (forall fenv n Γ es ps Γ',
      typed_args fenv n Γ es ps Γ' ->
      ctx_same_bindings Γ Γ').
Proof.
  assert (H : forall fenv n,
    (forall Γ e T Γ',
        typed fenv n Γ e T Γ' -> ctx_same_bindings Γ Γ') /\
    (forall Γ es ps Γ',
        typed_args fenv n Γ es ps Γ' -> ctx_same_bindings Γ Γ')).
  {
    intros fenv n.
    apply typed_typed_args_ind; intros; simpl;
      try solve [apply ctx_same_bindings_refl];
      try solve [eassumption];
      try solve [
        match goal with
        | Hconsume : ctx_consume _ _ = Some _ |- _ =>
            eapply ctx_consume_same_bindings; exact Hconsume
        end
      ];
      try solve [
        match goal with
        | Hhead : ctx_same_bindings ?Γ ?Γ1,
          Hbody : ctx_same_bindings (ctx_add ?x ?T ?m ?Γ1) ?Γ2
          |- ctx_same_bindings ?Γ (ctx_remove ?x ?Γ2) =>
            eapply ctx_same_bindings_trans;
            [ exact Hhead
            | eapply ctx_same_bindings_remove_head; exact Hbody ]
        end
      ];
      try solve [eapply ctx_same_bindings_trans; eassumption];
      try solve [
        match goal with
        | H1 : ctx_same_bindings ?Γ ?Γ1,
          H2 : ctx_same_bindings ?Γ1 ?Γ2,
          Hm : ctx_merge ?Γ2 _ = Some ?Γ4
          |- ctx_same_bindings ?Γ ?Γ4 =>
            eapply ctx_same_bindings_trans;
            [ eapply ctx_same_bindings_trans; [exact H1 | exact H2]
            | eapply ctx_merge_same_bindings; exact Hm ]
        end
      ].
  }
  split; intros fenv n; destruct (H fenv n) as [Ht Hargs]; [apply Ht | apply Hargs].
Qed.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EUnit => 1
  | ELit _ => 1
  | EVar _ => 1
  | ELet _ _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ELetInfer _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ECall _ args =>
      S ((fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | EReplace _ e => S (expr_size e)
  | EAssign _ e => S (expr_size e)
  | EBorrow _ _ => 1
  | EDeref e => S (expr_size e)
  | EDrop e => S (expr_size e)
  | EIf e1 e2 e3 => S (expr_size e1 + expr_size e2 + expr_size e3)
  end.

Lemma expr_size_call_arg_lt : forall fname args arg,
  In arg args ->
  expr_size arg < expr_size (ECall fname args).
Proof.
  intros fname args.
  induction args as [| a rest IH]; intros arg Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH arg Hin). simpl in IH. lia.
Qed.

Lemma alpha_rename_call_args_used_extends : forall ρ used args argsr used',
  (forall used0 e er used1,
      In e args ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      forall x, In x used0 -> In x used1) ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr ρ used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  forall x, In x used -> In x used'.
Proof.
  intros ρ used args.
  revert used.
  induction args as [| arg rest IH]; intros used argsr used' Hexpr Hrename x Hin;
    simpl in Hrename.
  - injection Hrename as _ <-. exact Hin.
  - destruct (alpha_rename_expr ρ used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr ρ used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as _ <-.
    eapply IH.
    + intros used0 e er0 used_tail Hin_rest Hrename0.
      eapply Hexpr.
      * right. exact Hin_rest.
      * exact Hrename0.
    + exact Hrest.
    + eapply Hexpr.
      * left. reflexivity.
      * exact Harg.
      * exact Hin.
Qed.

Lemma alpha_rename_expr_used_extends : forall ρ used e er used',
  alpha_rename_expr ρ used e = (er, used') ->
  forall x, In x used -> In x used'.
Proof.
  assert (Hsize : forall n ρ used e er used',
    expr_size e < n ->
    alpha_rename_expr ρ used e = (er, used') ->
    forall x, In x used -> In x used').
  {
  induction n as [| n IH]; intros ρ used e er used' Hlt Hrename x0 Hin.
  - lia.
  - destruct e; simpl in Hrename.
  + injection Hrename as _ <-. exact Hin.
  + injection Hrename as _ <-. exact Hin.
  + injection Hrename as _ <-. exact Hin.
  + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
    * exact He2.
    * right. right. apply in_or_app. right.
      eapply IH.
      -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
      -- exact He1.
      -- exact Hin.
  + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
    * exact He2.
    * right. right. apply in_or_app. right.
      eapply IH.
      -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
      -- exact He1.
      -- exact Hin.
  + remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used l) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as _ <-.
    eapply alpha_rename_call_args_used_extends.
    * intros used0 e er0 used1 Hin_arg Hrename0.
      eapply IH.
      -- pose proof (expr_size_call_arg_lt i l e Hin_arg) as Harg_lt.
        assert (expr_size e < n) as Hlt_arg by lia.
        exact Hlt_arg.
      -- exact Hrename0.
    * symmetry. exact Hargs.
    * exact Hin.
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
    * exact He.
    * exact Hin.
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
    * exact He.
    * exact Hin.
  + (* EBorrow: returns used unchanged *)
    injection Hrename as _ <-. exact Hin.
  + (* EDeref: like EDrop *)
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
    * exact He.
    * exact Hin.
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
    * exact He.
    * exact Hin.
  + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
    injection Hrename as _ <-.
    eapply IH.
    * simpl in Hlt. assert (expr_size e3 < n) as Hlt_e3 by lia. exact Hlt_e3.
    * exact He3.
    * eapply IH.
      -- simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
      -- exact He2.
      -- eapply IH.
         ++ simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
         ++ exact He1.
         ++ exact Hin.
  }
  intros ρ used e er used' Hrename x Hin.
  eapply (Hsize (S (expr_size e))).
  - apply Nat.lt_succ_diag_r.
  - exact Hrename.
  - exact Hin.
Qed.

Lemma alpha_rename_params_used_extends : forall ρ used ps psr ρ' used',
  alpha_rename_params ρ used ps = (psr, ρ', used') ->
  forall x, In x used -> In x used'.
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Hrename x Hin.
  - simpl in Hrename. injection Hrename as _ _ <-. exact Hin.
  - simpl in Hrename.
    destruct (alpha_rename_params
      ((param_name p, fresh_ident (param_name p) used) :: ρ)
      (fresh_ident (param_name p) used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    injection Hrename as _ _ <-.
    eapply IH.
    + exact Hps.
    + right. exact Hin.
Qed.

Lemma alpha_rename_fn_def_used_extends : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  forall x, In x used -> In x used'.
Proof.
  intros used f fr used' Hrename x Hin.
  destruct f as [fname lifetimes ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  injection Hrename as _ <-.
  eapply alpha_rename_expr_used_extends.
  - exact Hbody.
  - eapply alpha_rename_params_used_extends.
    + exact Hps.
    + apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma alpha_rename_syntax_go_used_extends : forall used fenv fenvr used',
  alpha_rename_syntax_go used fenv = (fenvr, used') ->
  forall x, In x used -> In x used'.
Proof.
  intros used fenv.
  revert used.
  induction fenv as [| f fs IH]; intros used fenvr used' Hrename x Hin.
  - simpl in Hrename. injection Hrename as _ <-. exact Hin.
  - simpl in Hrename.
    destruct (alpha_rename_fn_def used f) as [fr used1] eqn:Hf.
    destruct (alpha_rename_syntax_go used1 fs) as [fsr used2] eqn:Hfs.
    injection Hrename as _ <-.
    eapply IH.
    + exact Hfs.
    + eapply alpha_rename_fn_def_used_extends; [exact Hf | exact Hin].
Qed.

Lemma alpha_rename_call_args_sound : forall ρ used args argsr used',
  (forall used0 e er used1,
      In e args ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      expr_alpha ρ e er) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range ρ) ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr ρ used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exprs_alpha ρ args argsr.
Proof.
  intros ρ used args.
  revert used.
  induction args as [| arg rest IH]; intros used argsr used' Hexpr Hdisj Hrename;
    simpl in Hrename.
  - injection Hrename as <- _. constructor.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range ρ) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr ρ used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr ρ used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- _.
    constructor.
    + eapply Hexpr.
      * left. reflexivity.
      * exact Hdisj_arg.
      * exact Harg.
    + eapply IH.
      * intros used0 e er0 used_tail Hin Hdisj0 Hrename0.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Hdisj0.
        -- exact Hrename0.
      * exact Hdisj_rest.
      * exact Hrest.
Qed.

Lemma alpha_rename_expr_sound : forall ρ used e er used',
  disjoint_names (free_vars_expr e) (rename_range ρ) ->
  alpha_rename_expr ρ used e = (er, used') ->
  expr_alpha ρ e er.
Proof.
  assert (Hsize : forall n ρ used e er used',
    expr_size e < n ->
    disjoint_names (free_vars_expr e) (rename_range ρ) ->
    alpha_rename_expr ρ used e = (er, used') ->
    expr_alpha ρ e er).
  {
  induction n as [| n IH]; intros ρ used e er used' Hlt Hdisj Hrename.
  - lia.
  - destruct e; simpl in Hrename.
  + injection Hrename as <- _. constructor.
  + injection Hrename as <- _. constructor.
  + injection Hrename as <- _. constructor.
    apply (Hdisj i). simpl. left. reflexivity.
  + destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
      (rename_range ρ)) as [Hdisj1 Hdisj2].
    { intros x Hin. apply Hdisj. simpl. right. exact Hin. }
    destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as <- _.
    constructor.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact Hdisj1.
      -- exact He1.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- intros x Hin.
        simpl. intros [Heq | Hin_range].
        ++ subst x.
           apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
           right. apply in_or_app. left. exact Hin.
        ++ exact (Hdisj2 x Hin Hin_range).
      -- exact He2.
  + destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
      (rename_range ρ)) as [Hdisj1 Hdisj2].
    { intros x Hin. apply Hdisj. simpl. right. exact Hin. }
    destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as <- _.
    constructor.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact Hdisj1.
      -- exact He1.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- intros x Hin.
        simpl. intros [Heq | Hin_range].
        ++ subst x.
           apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
           right. apply in_or_app. left. exact Hin.
        ++ exact (Hdisj2 x Hin Hin_range).
      -- exact He2.
  + remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used l) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as <- _.
    constructor.
    eapply alpha_rename_call_args_sound.
    * intros used0 e er0 used1 Hin Hdisj0 Hrename0.
      eapply IH.
      -- pose proof (expr_size_call_arg_lt i l e Hin) as Harg_lt.
         assert (expr_size e < n) as Hlt_arg by lia.
         exact Hlt_arg.
      -- exact Hdisj0.
      -- exact Hrename0.
    * exact Hdisj.
    * symmetry. exact Hargs.
  + (* EReplace p e *)
    destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e)
      (rename_range ρ) Hdisj) as [Hpx Hdisj_e].
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    constructor.
    * apply rename_place_alpha_sound. exact Hpx.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact Hdisj_e.
      -- exact He.
  + (* EAssign p e *)
    destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e)
      (rename_range ρ) Hdisj) as [Hpx Hdisj_e].
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    constructor.
    * apply rename_place_alpha_sound. exact Hpx.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact Hdisj_e.
      -- exact He.
  + (* EBorrow: no sub-expression, just rename place *)
    injection Hrename as <- _.
    constructor.
    apply rename_place_alpha_sound.
    exact (Hdisj (place_name p) (in_eq (place_name p) [])). 
  + (* EDeref: like EDrop *)
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    constructor.
    eapply IH.
    * simpl in Hlt. lia.
    * exact Hdisj.
    * exact He.
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    constructor.
    eapply IH.
    * simpl in Hlt. lia.
    * exact Hdisj.
    * exact He.
  + destruct (disjoint_names_app_l (free_vars_expr e1)
      (free_vars_expr e2 ++ free_vars_expr e3) (rename_range ρ)) as [Hdisj1 Hdisj23].
    { intros x Hin. apply Hdisj. simpl. exact Hin. }
    destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
      (rename_range ρ)) as [Hdisj2 Hdisj3].
    { exact Hdisj23. }
    destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
    injection Hrename as <- _.
    constructor.
    * eapply IH; [simpl in Hlt; lia | exact Hdisj1 | exact He1].
    * eapply IH; [simpl in Hlt; lia | exact Hdisj2 | exact He2].
    * eapply IH; [simpl in Hlt; lia | exact Hdisj3 | exact He3].
  }
  intros ρ used e er used' Hdisj Hrename.
  eapply (Hsize (S (expr_size e))).
  - lia.
  - exact Hdisj.
  - exact Hrename.
Qed.

Lemma alpha_rename_params_shape : forall ρ used ps psr ρ' used',
  alpha_rename_params ρ used ps = (psr, ρ', used') ->
  params_alpha ps psr.
Proof.
  intros ρ used ps. revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' H.
  - simpl in H. inversion H. constructor.
  - destruct p as [m x T].
    simpl in H.
    destruct (alpha_rename_params
      ((x, fresh_ident x used) :: ρ) (fresh_ident x used :: used) ps)
      as [[ps'' ρ''] used''] eqn:Hps.
    inversion H; subst.
    constructor.
    + unfold same_param_shape. simpl. split; reflexivity.
    + eapply IH. exact Hps.
Qed.

Lemma alpha_rename_fn_def_shape : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  same_fn_shape f fr.
Proof.
  intros used f fr used' H.
  destruct f as [fname lifetimes ps ret body].
  unfold alpha_rename_fn_def in H.
  simpl in H.
  destruct (alpha_rename_params []
    (param_names ps ++ free_vars_expr body ++ used) ps)
    as [[ps' ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [body' used2] eqn:Hbody.
  inversion H; subst.
  unfold same_fn_shape. simpl.
  split; [reflexivity |].
  split; [reflexivity |].
  eapply alpha_rename_params_shape. exact Hps.
Qed.

Lemma alpha_rename_syntax_go_shape : forall used fenv fenvr used',
  alpha_rename_syntax_go used fenv = (fenvr, used') ->
  fenv_alpha fenv fenvr.
Proof.
  intros used fenv. revert used.
  induction fenv as [| f fs IH]; intros used fenvr used' H.
  - simpl in H. inversion H. constructor.
  - simpl in H.
    destruct (alpha_rename_fn_def used f) as [f' used1] eqn:Hf.
    destruct (alpha_rename_syntax_go used1 fs) as [fs' used2] eqn:Hfs.
    inversion H; subst.
    constructor.
    + eapply alpha_rename_fn_def_shape. exact Hf.
    + eapply IH. exact Hfs.
Qed.

Lemma alpha_rename_for_infer_sound : forall fenv Γ e fenvr er,
  alpha_rename_for_infer Γ fenv e = (fenvr, er) ->
  fenv_alpha fenv fenvr /\ expr_alpha [] e er.
Proof.
  intros fenv Γ e fenvr er Hrename.
  unfold alpha_rename_for_infer in Hrename.
  destruct (alpha_rename_syntax_go (free_vars_expr e ++ ctx_names Γ) fenv)
    as [fenv1 used] eqn:Hfenv.
  destruct (alpha_rename_expr [] used e) as [er1 used'] eqn:He.
  injection Hrename as <- <-.
  split.
  - eapply alpha_rename_syntax_go_shape. exact Hfenv.
  - eapply alpha_rename_expr_sound.
    + apply disjoint_names_nil_r.
    + exact He.
Qed.

Lemma params_alpha_cons_inv : forall ps0 pr psr,
  params_alpha ps0 (pr :: psr) ->
  exists p ps,
    ps0 = p :: ps /\
    same_param_shape p pr /\
    params_alpha ps psr.
Proof.
  intros ps0 pr psr Halpha.
  inversion Halpha; subst.
  exists p, ps.
  split; [reflexivity |].
  split; assumption.
Qed.

Lemma typed_args_cons_inv : forall fenv n Γ er ers pr psr Γ',
  typed_args fenv n Γ (er :: ers) (pr :: psr) Γ' ->
  exists T Γ1,
    typed fenv n Γ er T Γ1 /\
    ty_compatible T (param_ty pr) /\
    typed_args fenv n Γ1 ers psr Γ'.
Proof.
  intros fenv n Γ er ers pr psr Γ' Htyped.
  inversion Htyped; subst.
  exists T_e, Γ1. repeat split; assumption.
Qed.

Lemma typed_call_inv : forall fenv n Γ fname args T Γ',
  typed fenv n Γ (ECall fname args) T Γ' ->
  exists fdef σ,
    In fdef fenv /\
    fn_name fdef = fname /\
    apply_lt_ty σ (fn_ret fdef) = T /\
    typed_args fenv n Γ args (apply_lt_params σ (fn_params fdef)) Γ'.
Proof.
  intros fenv n Γ fname args T Γ' Htyped.
  inversion Htyped; subst.
  exists fdef, σ. repeat split; assumption.
Qed.

Lemma params_alpha_apply_lt_compat : forall σ ps psr,
  params_alpha ps psr ->
  params_alpha (apply_lt_params σ ps) (apply_lt_params σ psr).
Proof.
  intros σ ps psr H.
  induction H as [| p pr ps' psr' Hshape Htail IH].
  - constructor.
  - simpl. constructor.
    + unfold same_param_shape in *. destruct Hshape as [Hmut Hty].
      split.
      * exact Hmut.
      * simpl. now rewrite Hty.
    + exact IH.
Qed.

Lemma alpha_rename_call_args_typed_backward : forall fenv0 fenvr n ρ Γ0 Γr args argsr used used' ps0 psr Γr',
  (forall Γa Γb used0 e er used1 T Γb',
      In e args ->
      ctx_alpha ρ Γa Γb ->
      (forall x, In x (ctx_names Γb) -> In x used0) ->
      (forall x, In x (rename_range ρ) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      typed fenvr n Γb er T Γb' ->
      exists Γa',
        typed fenv0 n Γa e T Γa' /\
        ctx_alpha ρ Γa' Γb') ->
  fenv_alpha fenv0 fenvr ->
  ctx_alpha ρ Γ0 Γr ->
  (forall x, In x (ctx_names Γr) -> In x used) ->
  (forall x, In x (rename_range ρ) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range ρ) ->
  params_alpha ps0 psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr ρ used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  typed_args fenvr n Γr argsr psr Γr' ->
  exists Γ0',
    typed_args fenv0 n Γ0 args ps0 Γ0' /\
    ctx_alpha ρ Γ0' Γr'.
Proof.
  intros fenv0 fenvr n ρ Γ0 Γr args.
  revert Γ0 Γr.
  induction args as [| arg rest IH]; intros Γ0 Γr argsr used used' ps0 psr Γr'
    Hexpr Hfenv Hctx Hctx_used Hrange_used Hdisj Hparams Hrename Htyped_args;
    simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Γ0. split; [constructor | exact Hctx].
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range ρ) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr ρ used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr ρ used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct psr as [| pr psr_tail].
    { inversion Htyped_args. }
    destruct (params_alpha_cons_inv ps0 pr psr_tail Hparams)
      as [p [ps [Hps0 [Hshape Hparams_tail]]]].
    subst ps0.
    destruct (typed_args_cons_inv fenvr n Γr ar restr pr psr_tail Γr' Htyped_args)
      as [Targ [Γr1 [Htyped_arg_r [Hcompat Htyped_tail_r]]]].
    destruct (Hexpr Γ0 Γr used arg ar used1 Targ Γr1)
      as [Γ01 [Htyped_arg Hctx_arg]].
    + left. reflexivity.
    + exact Hctx.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + exact Htyped_arg_r.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Γr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (ctx_same_bindings_names Γr Γr1).
          + exact Hin.
          + destruct typed_same_bindings as [Hsame _].
            eapply Hsame. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range ρ) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH Γ01 Γr1 restr used1 used2 ps psr_tail Γr')
        as [Γ02 [Htyped_tail Hctx_tail]].
      * intros Γa Γb used0 e er used_tail T Γb' Hin Halpha Hcu Hru Hd Hr Ht.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Halpha.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
        -- exact Ht.
      * exact Hfenv.
      * exact Hctx_arg.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exact Htyped_tail_r.
      * exists Γ02. split.
        -- eapply TArgs_Cons.
           ++ exact Htyped_arg.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite HT. exact Hcompat.
           ++ exact Htyped_tail.
        -- exact Hctx_tail.
Qed.

Lemma ctx_alpha_merge_backward : forall ρ Γ02 Γ2r Γ03 Γ3r Γ4r,
  ctx_alpha ρ Γ02 Γ2r ->
  ctx_alpha ρ Γ03 Γ3r ->
  ctx_merge Γ2r Γ3r = Some Γ4r ->
  exists Γ04, ctx_merge Γ02 Γ03 = Some Γ04 /\ ctx_alpha ρ Γ04 Γ4r.
Proof.
  intros ρ Γ02 Γ2r Γ03 Γ3r Γ4r Halpha2 Halpha3 Hmerge.
  revert Γ03 Γ3r Γ4r Halpha3 Hmerge.
  induction Halpha2 as [Γ02 | ρ' Γ02' Γ2r' x xr T b2 m2 Halpha2' IH2 Hxr_ctx Hxr_range];
    intros Γ03 Γ3r Γ4r Halpha3 Hmerge.
  - (* CtxAlpha_Base: Γ02 = Γ2r *)
    inversion Halpha3; subst.
    exists Γ4r. split; [exact Hmerge | constructor].
  - (* CtxAlpha_Bind: Γ02 = (x,T,b2)::Γ02', Γ2r = (xr,T,b2)::Γ2r' *)
    (* After inversion+subst on Halpha3: Γ03/Γ3r are substituted away,
       fresh tail vars (auto-named) appear *)
    inversion Halpha3; subst.
    simpl in Hmerge. rewrite ident_eqb_refl in Hmerge. simpl in Hmerge.
    lazymatch goal with
    | H_alpha3' : ctx_alpha ρ' ?Γ03t ?Γ3rt |- _ =>
        destruct (ctx_merge Γ2r' Γ3rt) as [rest4r |] eqn:Hmerge_rest;
        [| discriminate];
        destruct (IH2 Γ03t Γ3rt rest4r H_alpha3' Hmerge_rest) as [rest04 [Hmerge04 Hctx04]];
        assert (Hrest_names : ~ In xr (ctx_names rest4r)) by
          (rewrite (ctx_same_bindings_names _ _
             (ctx_merge_same_bindings _ Γ3rt _ Hmerge_rest));
           exact Hxr_ctx)
    end.
    simpl. rewrite ident_eqb_refl. simpl. rewrite Hmerge04.
    destruct (ty_usage T) eqn:Hu.
    + (* ULinear: Hmerge has the form (if Bool.eqb b2 ?b then ... else ...) = Some _ *)
      lazymatch goal with
      | Hm : (if Bool.eqb b2 ?bX then _ else _) = Some _ |- _ =>
          destruct (Bool.eqb b2 bX) eqn:Heqb;
          [injection Hm as <-;
           eexists; split;
           [reflexivity |
            constructor; [exact Hctx04 | exact Hrest_names | exact Hxr_range]]
          | discriminate]
      end.
    + (* UAffine *)
      injection Hmerge as <-.
      eexists. split. reflexivity.
      constructor; [exact Hctx04 | exact Hrest_names | exact Hxr_range].
    + (* UUnrestricted *)
      injection Hmerge as <-.
      eexists. split. reflexivity.
      constructor; [exact Hctx04 | exact Hrest_names | exact Hxr_range].
Qed.

Lemma alpha_rename_typed_backward : forall fenv0 fenvr n ρ Γ0 Γr e er used used' T Γr',
  fenv_alpha fenv0 fenvr ->
  ctx_alpha ρ Γ0 Γr ->
  (forall x, In x (ctx_names Γr) -> In x used) ->
  (forall x, In x (rename_range ρ) -> In x used) ->
  disjoint_names (free_vars_expr e) (rename_range ρ) ->
  alpha_rename_expr ρ used e = (er, used') ->
  typed fenvr n Γr er T Γr' ->
  exists Γ0',
    typed fenv0 n Γ0 e T Γ0' /\
    ctx_alpha ρ Γ0' Γr'.
Proof.
  assert (Hsize : forall sz fenv0 fenvr n ρ Γ0 Γr e er used used' T Γr',
    expr_size e < sz ->
    fenv_alpha fenv0 fenvr ->
    ctx_alpha ρ Γ0 Γr ->
    (forall x, In x (ctx_names Γr) -> In x used) ->
    (forall x, In x (rename_range ρ) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range ρ) ->
    alpha_rename_expr ρ used e = (er, used') ->
    typed fenvr n Γr er T Γr' ->
    exists Γ0',
      typed fenv0 n Γ0 e T Γ0' /\
      ctx_alpha ρ Γ0' Γr').
  {
  induction sz as [| sz IH]; intros fenv0 fenvr n ρ Γ0 Γr e er used used' T Γr'
    Hlt Hfenv Hctx Hctx_used Hrange_used Hdisj Hrename Htyped.
  - lia.
  - destruct e; simpl in Hrename.
  + injection Hrename as <- _.
    inversion Htyped; subst.
    eexists. split; [constructor | exact Hctx].
  + injection Hrename as <- _.
    inversion Htyped; subst.
    * exists Γ0. split; [constructor | exact Hctx].
    * exists Γ0. split; [constructor | exact Hctx].
    * exists Γ0. split; [constructor | exact Hctx].
  + injection Hrename as <- _.
    inversion Htyped; subst.
    * assert (Hsafe : ~ In i (rename_range ρ)).
      { intros Hin. apply (Hdisj i); simpl; [left; reflexivity | exact Hin]. }
      lazymatch goal with
      | Hlookup : ctx_lookup (lookup_rename i ρ) Γr = Some (T, false),
        Hconsume_r : ctx_consume (lookup_rename i ρ) Γr = Some ?Γr1 |- _ =>
      destruct (ctx_alpha_consume_backward ρ Γ0 Γr i Γr1 Hctx Hsafe Hconsume_r)
        as [Γ0' [Hconsume Hctx']]
      end.
	      exists Γ0'. split.
	      { eapply T_Var_Consume.
	        - lazymatch goal with
	          | Hlookup : ctx_lookup (lookup_rename i ρ) Γr = Some (T, false) |- _ =>
	              exact (ctx_alpha_lookup_backward ρ Γ0 Γr i T false Hctx Hsafe Hlookup)
	          end.
	        - assumption.
	        - exact Hconsume. }
	      { exact Hctx'. }
    * assert (Hsafe : ~ In i (rename_range ρ)).
      { intros Hin. apply (Hdisj i); simpl; [left; reflexivity | exact Hin]. }
	      exists Γ0. split.
	      { eapply T_Var_Copy.
	        - lazymatch goal with
	          | Hlookup : ctx_lookup (lookup_rename i ρ) ?Γrx = Some (T, b),
	            Halpha : ctx_alpha ρ Γ0 ?Γrx |- _ =>
	              exact (ctx_alpha_lookup_backward ρ Γ0 Γrx i T b Halpha Hsafe Hlookup)
	          end.
	        - assumption. }
	      { exact Hctx. }
  + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as <- _.
    inversion Htyped; subst.
    destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
      (rename_range ρ)) as [Hdisj1 Hdisj2].
    { intros x Hin. apply Hdisj. simpl. right. exact Hin. }
    lazymatch goal with
    | Hte1 : typed fenvr n Γr e1r ?T1r ?Γ1r |- _ =>
      destruct (IH fenv0 fenvr n ρ Γ0 Γr e1 e1r used used1 T1r Γ1r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx Hctx_used Hrange_used Hdisj1 He1 Hte1)
        as [Γ01 [Htyped1 Hctx1]]
    end.
    set (xr := fresh_ident i (i :: free_vars_expr e2 ++ used1)).
    assert (Hctx1_names : forall x, In x (ctx_names Γ1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (ctx_same_bindings_names Γr Γ1).
        + exact Hin.
        + destruct typed_same_bindings as [Hsame _].
          lazymatch goal with
          | Hte1 : typed fenvr n Γr e1r _ _ |- _ => eapply Hsame; exact Hte1
          end. }
    assert (Hxr_ctx : ~ In xr (ctx_names Γ1)).
    { unfold xr. intros Hin.
      apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx1_names. exact Hin. }
    assert (Hxr_range : ~ In xr (rename_range ρ)).
    { unfold xr. intros Hin.
      apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hrange_used. exact Hin. }
    assert (Hctx_ext :
      ctx_alpha ((i, xr) :: ρ)
        (ctx_add i t m Γ01) (ctx_add xr t m Γ1)).
    { constructor; exact Hctx1 || exact Hxr_ctx || exact Hxr_range. }
    assert (Hctx_ext_used :
      forall x, In x (ctx_names (ctx_add xr t m Γ1)) ->
        In x (xr :: i :: free_vars_expr e2 ++ used1)).
    { intros x [Hx | Hin]; [left; exact Hx |].
      right. right. apply in_or_app. right. apply Hctx1_names. exact Hin. }
    assert (Hrange_ext_used :
      forall x, In x (rename_range ((i, xr) :: ρ)) ->
        In x (xr :: i :: free_vars_expr e2 ++ used1)).
    { intros x [Hx | Hin]; [left; exact Hx |].
      right. right. apply in_or_app. right.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hrange_used. exact Hin. }
    assert (Hdisj2_ext :
      disjoint_names (free_vars_expr e2) (rename_range ((i, xr) :: ρ))).
    { intros x Hin [Hx | Hinr].
      - subst x. unfold xr in *.
        apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
        right. apply in_or_app. left. exact Hin.
      - exact (Hdisj2 x Hin Hinr). }
    lazymatch goal with
    | Hte2 : typed fenvr n (ctx_add ?xrr t m Γ1) e2r ?T2r ?Γ2r |- _ =>
      destruct (IH fenv0 fenvr n ((i, xr) :: ρ)
        (ctx_add i t m Γ01) (ctx_add xrr t m Γ1)
        e2 e2r (xr :: i :: free_vars_expr e2 ++ used1) used2 T2r Γ2r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx_ext Hctx_ext_used Hrange_ext_used Hdisj2_ext He2 Hte2)
        as [Γ02 [Htyped2 Hctx2]]
    end.
	    exists (ctx_remove i Γ02). split.
	    { eapply T_Let.
	      - exact Htyped1.
	      - assumption.
	      - exact Htyped2.
	      - eapply ctx_alpha_is_ok_backward.
	        + exact Hctx2.
	        + simpl. intros [Heq | Hinr].
	          * apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
	            fold xr. rewrite Heq. left. reflexivity.
	          * apply (Hdisj i); simpl; [left; reflexivity | exact Hinr].
	        + simpl. rewrite ident_eqb_refl.
	          lazymatch goal with
	          | Hok : ctx_is_ok _ _ _ |- _ => exact Hok
	          end. }
	    { eapply ctx_alpha_remove_bound. exact Hctx2. }
  + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as <- _.
    inversion Htyped; subst.
    destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
      (rename_range ρ)) as [Hdisj1 Hdisj2].
    { intros x Hin. apply Hdisj. simpl. right. exact Hin. }
    lazymatch goal with
    | Hte1 : typed fenvr n Γr e1r ?T1r ?Γ1r |- _ =>
      destruct (IH fenv0 fenvr n ρ Γ0 Γr e1 e1r used used1 T1r Γ1r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx Hctx_used Hrange_used Hdisj1 He1 Hte1)
        as [Γ01 [Htyped1 Hctx1]]
    end.
    set (xr := fresh_ident i (i :: free_vars_expr e2 ++ used1)).
    assert (Hctx1_names : forall x, In x (ctx_names Γ1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (ctx_same_bindings_names Γr Γ1).
        + exact Hin.
        + destruct typed_same_bindings as [Hsame _].
          lazymatch goal with
          | Hte1 : typed fenvr n Γr e1r _ _ |- _ => eapply Hsame; exact Hte1
          end. }
    assert (Hxr_ctx : ~ In xr (ctx_names Γ1)).
    { unfold xr. intros Hin.
      apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx1_names. exact Hin. }
    assert (Hxr_range : ~ In xr (rename_range ρ)).
    { unfold xr. intros Hin.
      apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hrange_used. exact Hin. }
    assert (Hctx_ext :
      ctx_alpha ((i, xr) :: ρ)
        (ctx_add i T1 m Γ01) (ctx_add xr T1 m Γ1)).
    { constructor; exact Hctx1 || exact Hxr_ctx || exact Hxr_range. }
    assert (Hctx_ext_used :
      forall x, In x (ctx_names (ctx_add xr T1 m Γ1)) ->
        In x (xr :: i :: free_vars_expr e2 ++ used1)).
    { intros x [Hx | Hin]; [left; exact Hx |].
      right. right. apply in_or_app. right. apply Hctx1_names. exact Hin. }
    assert (Hrange_ext_used :
      forall x, In x (rename_range ((i, xr) :: ρ)) ->
        In x (xr :: i :: free_vars_expr e2 ++ used1)).
    { intros x [Hx | Hin]; [left; exact Hx |].
      right. right. apply in_or_app. right.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hrange_used. exact Hin. }
    assert (Hdisj2_ext :
      disjoint_names (free_vars_expr e2) (rename_range ((i, xr) :: ρ))).
    { intros x Hin [Hx | Hinr].
      - subst x. unfold xr in *.
        apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
        right. apply in_or_app. left. exact Hin.
      - exact (Hdisj2 x Hin Hinr). }
    lazymatch goal with
    | Hte2 : typed fenvr n (ctx_add _ T1 m Γ1) e2r ?T2r ?Γ2r |- _ =>
      destruct (IH fenv0 fenvr n ((i, xr) :: ρ)
        (ctx_add i T1 m Γ01) (ctx_add xr T1 m Γ1)
        e2 e2r (xr :: i :: free_vars_expr e2 ++ used1) used2 T2r Γ2r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx_ext Hctx_ext_used Hrange_ext_used Hdisj2_ext He2 Hte2)
        as [Γ02 [Htyped2 Hctx2]]
    end.
    exists (ctx_remove i Γ02). split.
    { eapply T_LetInfer.
      - exact Htyped1.
      - exact Htyped2.
      - eapply ctx_alpha_is_ok_backward.
        + exact Hctx2.
        + simpl. intros [Heq | Hinr].
          * apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
            fold xr. rewrite Heq. left. reflexivity.
          * apply (Hdisj i); simpl; [left; reflexivity | exact Hinr].
        + simpl. rewrite ident_eqb_refl.
          lazymatch goal with
          | Hok : ctx_is_ok _ _ _ |- _ => exact Hok
          end. }
    { eapply ctx_alpha_remove_bound. exact Hctx2. }
  + remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used l) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as <- _.
    lazymatch goal with
    | Htyped_call : typed fenvr n Γr (ECall ?fname argsr) T Γr' |- _ =>
      destruct (typed_call_inv fenvr n Γr fname argsr T Γr' Htyped_call)
        as [fdef [σ [Hinr [Hname_r [Hret_r Hargs_typed]]]]];
      destruct (fenv_alpha_in_backward fenv0 fenvr fdef Hfenv Hinr)
        as [fdef0 [Hin0 Hshape]];
      destruct Hshape as [Hname [Hret Hparams]]
    end.
    assert (Hparams_lt :
      params_alpha (apply_lt_params σ (fn_params fdef0))
                   (apply_lt_params σ (fn_params fdef))).
    { apply params_alpha_apply_lt_compat. exact Hparams. }
    assert (Hargs_back :
      exists Γ0',
        typed_args fenv0 n Γ0 l (apply_lt_params σ (fn_params fdef0)) Γ0' /\
        ctx_alpha ρ Γ0' Γr').
    { eapply alpha_rename_call_args_typed_backward with (n := n).
      - intros Γa Γb used0 e er used1 T0 Γb' Hin Halpha Hcu Hru Hd Hr Ht.
        eapply IH.
        + pose proof (expr_size_call_arg_lt i l e Hin) as Harg_lt.
          eapply Nat.lt_le_trans.
          * exact Harg_lt.
          * simpl. simpl in Hlt. lia.
        + exact Hfenv.
        + exact Halpha.
        + exact Hcu.
        + exact Hru.
        + exact Hd.
        + exact Hr.
        + exact Ht.
      - exact Hfenv.
      - exact Hctx.
      - exact Hctx_used.
      - exact Hrange_used.
      - exact Hdisj.
      - exact Hparams_lt.
      - symmetry. exact Hargs.
      - lazymatch goal with
        | Hargs_typed : typed_args fenvr n Γr argsr _ Γr' |- _ => exact Hargs_typed
        end. }
    destruct Hargs_back as [Γ0' [Htyped_args0 Hctx0]].
    exists Γ0'. split.
    * rewrite <- Hret_r. rewrite <- Hret.
      eapply T_Call_Lt with (σ := σ).
      -- exact Hin0.
      -- rewrite Hname. exact Hname_r.
      -- exact Htyped_args0.
    * exact Hctx0.
  + (* EReplace p e *)
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    destruct p as [px | q].
    * (* PVar px → T_Replace *)
      inversion Htyped; subst.
      assert (Hsafe : ~ In px (rename_range ρ)).
      { intros Hin. apply (Hdisj px); simpl; [left; reflexivity | exact Hin]. }
      assert (Hdisj_e : disjoint_names (free_vars_expr e) (rename_range ρ)).
      { intros x Hin Hinr. exact (Hdisj x (or_intror Hin) Hinr). }
      lazymatch goal with
      | Hte : typed fenvr n Γr er0 ?Tnew ?Γr1 |- _ =>
        destruct (IH fenv0 fenvr n ρ Γ0 Γr e er0 used used0 Tnew Γr1
          ltac:(simpl in Hlt; lia)
          Hfenv Hctx Hctx_used Hrange_used
          Hdisj_e He Hte) as [Γ0' [Htyped0 Hctx0]]
      end.
      exists Γ0'. split.
      { eapply T_Replace.
        - lazymatch goal with
          | Hlookup : ctx_lookup (lookup_rename px ρ) Γr = Some (?Tx, false) |- _ =>
            exact (ctx_alpha_lookup_backward ρ Γ0 Γr px Tx false Hctx Hsafe Hlookup)
          end.
        - lazymatch goal with
          | Hmut : ctx_lookup_mut (lookup_rename px ρ) Γr = Some ?m |- _ =>
            exact (ctx_alpha_lookup_mut_backward ρ Γ0 Γr px m Hctx Hsafe Hmut)
          end.
        - exact Htyped0.
        - assumption. }
      { exact Hctx0. }
    * (* PDeref q → T_Replace_Deref *)
      inversion Htyped; subst.
      assert (Hsafe : ~ In (place_root q) (rename_range ρ)).
      { rewrite <- place_name_root. intros Hin.
        apply (Hdisj (place_name q)); simpl; [left; reflexivity | exact Hin]. }
      assert (Hdisj_e : disjoint_names (free_vars_expr e) (rename_range ρ)).
      { intros x Hin Hinr. exact (Hdisj x (or_intror Hin) Hinr). }
      lazymatch goal with
      | Hte : typed fenvr n Γr er0 ?Tnew ?Γr1 |- _ =>
        destruct (IH fenv0 fenvr n ρ Γ0 Γr e er0 used used0 Tnew Γr1
          ltac:(simpl in Hlt; lia)
          Hfenv Hctx Hctx_used Hrange_used
          Hdisj_e He Hte) as [Γ0' [Htyped0 Hctx0]]
      end.
      exists Γ0'. split.
      { eapply T_Replace_Deref.
        - lazymatch goal with
          | Hplace : typed_place fenvr n Γr (rename_place ρ q) _ |- _ =>
            exact (alpha_rename_typed_place_backward fenv0 fenvr n ρ Γ0 Γr q _ Hctx Hsafe Hplace)
          end.
        - lazymatch goal with
          | Hmut : ctx_lookup_mut (place_root (rename_place ρ q)) Γr = Some ?m |- _ =>
            rewrite place_root_rename_place in Hmut;
            exact (ctx_alpha_lookup_mut_backward ρ Γ0 Γr (place_root q) m Hctx Hsafe Hmut)
          end.
        - exact Htyped0.
        - assumption. }
      { exact Hctx0. }
  + (* EAssign p e *)
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    destruct p as [px | q].
    * (* PVar px → T_Assign *)
      inversion Htyped; subst.
      assert (Hsafe : ~ In px (rename_range ρ)).
      { intros Hin. apply (Hdisj px); simpl; [left; reflexivity | exact Hin]. }
      assert (Hdisj_e : disjoint_names (free_vars_expr e) (rename_range ρ)).
      { intros x Hin Hinr. exact (Hdisj x (or_intror Hin) Hinr). }
      lazymatch goal with
      | Hte : typed fenvr n Γr er0 ?Tnew ?Γr1 |- _ =>
        destruct (IH fenv0 fenvr n ρ Γ0 Γr e er0 used used0 Tnew Γr1
          ltac:(simpl in Hlt; lia)
          Hfenv Hctx Hctx_used Hrange_used Hdisj_e He Hte) as [Γ0' [Htyped0 Hctx0]]
      end.
      exists Γ0'. split.
      { eapply T_Assign.
        - lazymatch goal with
          | Hlookup : ctx_lookup (lookup_rename px ρ) Γr = Some (?Tx, false) |- _ =>
            exact (ctx_alpha_lookup_backward ρ Γ0 Γr px Tx false Hctx Hsafe Hlookup)
          end.
        - lazymatch goal with
          | Hmut : ctx_lookup_mut (lookup_rename px ρ) Γr = Some ?m |- _ =>
            exact (ctx_alpha_lookup_mut_backward ρ Γ0 Γr px m Hctx Hsafe Hmut)
          end.
        - assumption.
        - exact Htyped0.
        - assumption. }
      { exact Hctx0. }
    * (* PDeref q *)
      inversion Htyped; subst.
      assert (Hsafe : ~ In (place_root q) (rename_range ρ)).
      { rewrite <- place_name_root. intros Hin.
        apply (Hdisj (place_name q)); simpl; [left; reflexivity | exact Hin]. }
      assert (Hdisj_e : disjoint_names (free_vars_expr e) (rename_range ρ)).
      { intros x Hin Hinr. exact (Hdisj x (or_intror Hin) Hinr). }
      lazymatch goal with
      | Hte : typed fenvr n Γr er0 ?Tnew ?Γr1 |- _ =>
        destruct (IH fenv0 fenvr n ρ Γ0 Γr e er0 used used0 Tnew Γr1
          ltac:(simpl in Hlt; lia)
          Hfenv Hctx Hctx_used Hrange_used Hdisj_e He Hte) as [Γ0' [Htyped0 Hctx0]]
      end.
      exists Γ0'. split.
      { eapply T_Assign_Deref.
        - lazymatch goal with
          | Hplace : typed_place fenvr n Γr (rename_place ρ q) _ |- _ =>
            exact (alpha_rename_typed_place_backward fenv0 fenvr n ρ Γ0 Γr q _ Hctx Hsafe Hplace)
          end.
        - lazymatch goal with
          | Hmut : ctx_lookup_mut (place_root (rename_place ρ q)) Γr = Some ?m |- _ =>
            rewrite place_root_rename_place in Hmut;
            exact (ctx_alpha_lookup_mut_backward ρ Γ0 Γr (place_root q) m Hctx Hsafe Hmut)
          end.
        - assumption.
        - exact Htyped0.
        - assumption. }
      { exact Hctx0. }
  + (* EBorrow rk p *)
    injection Hrename as <- _.
    destruct p as [px | q].
    * (* PVar px → T_BorrowShared or T_BorrowMut *)
      inversion Htyped; subst.
      -- (* T_BorrowShared *)
         assert (Hsafe : ~ In px (rename_range ρ)).
         { intros Hin. apply (Hdisj px); simpl; [left; reflexivity | exact Hin]. }
         exists Γ0. split.
         { eapply T_BorrowShared.
           - lazymatch goal with
             | Hlookup : ctx_lookup (lookup_rename px ρ) ?Γrx = Some (?Tx, false) |- _ =>
               exact (ctx_alpha_lookup_backward ρ Γ0 Γrx px Tx false Hctx Hsafe Hlookup)
             end.
           - assumption. }
         { exact Hctx. }
      -- (* T_BorrowMut *)
         assert (Hsafe : ~ In px (rename_range ρ)).
         { intros Hin. apply (Hdisj px); simpl; [left; reflexivity | exact Hin]. }
         exists Γ0. split.
         { eapply T_BorrowMut.
           - lazymatch goal with
             | Hlookup : ctx_lookup (lookup_rename px ρ) ?Γrx = Some (?Tx, false) |- _ =>
               exact (ctx_alpha_lookup_backward ρ Γ0 Γrx px Tx false Hctx Hsafe Hlookup)
             end.
           - assumption.
           - lazymatch goal with
             | Hmut : ctx_lookup_mut (lookup_rename px ρ) ?Γrx = Some ?m |- _ =>
               exact (ctx_alpha_lookup_mut_backward ρ Γ0 Γrx px m Hctx Hsafe Hmut)
             end. }
         { exact Hctx. }
    * (* PDeref q → T_ReBorrowShared or T_ReBorrowMut *)
      inversion Htyped; subst.
      -- (* T_ReBorrowShared *)
         assert (Hsafe : ~ In (place_root q) (rename_range ρ)).
         { rewrite <- place_name_root. intros Hin.
           apply (Hdisj (place_name q)); simpl; [left; reflexivity | exact Hin]. }
         exists Γ0. split.
         { eapply T_ReBorrowShared.
           - lazymatch goal with
             | Hplace : typed_place fenvr n ?Γrx (rename_place ρ q) _ |- _ =>
               exact (alpha_rename_typed_place_backward fenv0 fenvr n ρ Γ0 Γrx q _ Hctx Hsafe Hplace)
             end.
           - assumption. }
         { exact Hctx. }
      -- (* T_ReBorrowMut *)
         assert (Hsafe : ~ In (place_root q) (rename_range ρ)).
         { rewrite <- place_name_root. intros Hin.
           apply (Hdisj (place_name q)); simpl; [left; reflexivity | exact Hin]. }
         exists Γ0. split.
         { eapply T_ReBorrowMut.
           - lazymatch goal with
             | Hplace : typed_place fenvr n ?Γrx (rename_place ρ q) _ |- _ =>
               exact (alpha_rename_typed_place_backward fenv0 fenvr n ρ Γ0 Γrx q _ Hctx Hsafe Hplace)
             end.
           - assumption.
           - lazymatch goal with
             | Hmut : ctx_lookup_mut (place_root (rename_place ρ q)) ?Γrx = Some ?m |- _ =>
               rewrite place_root_rename_place in Hmut;
               exact (ctx_alpha_lookup_mut_backward ρ Γ0 Γrx (place_root q) m Hctx Hsafe Hmut)
             end. }
         { exact Hctx. }
  + (* EDeref: like EDrop but uses T_Deref *)
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    inversion Htyped; subst.
    lazymatch goal with
    | Hte : typed fenvr n Γr er0 (MkTy ?u_r (TRef ?la ?rk T)) ?Γr1 |- _ =>
      destruct (IH fenv0 fenvr n ρ Γ0 Γr e er0 used used0 (MkTy u_r (TRef la rk T)) Γr1
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx Hctx_used Hrange_used Hdisj He Hte) as [Γ0' [Htyped0 Hctx0]]
    end.
    exists Γ0'. split.
    { eapply T_Deref; [assumption | exact Htyped0]. }
    { exact Hctx0. }
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    inversion Htyped; subst.
    destruct (IH fenv0 fenvr n ρ Γ0 Γr e er0 used used0 T0 Γr'
      ltac:(simpl in Hlt; lia)
      Hfenv Hctx Hctx_used Hrange_used Hdisj He H1)
      as [Γ0' [Htyped0 Hctx0]].
    exists Γ0'. split; [eapply T_Drop; exact Htyped0 | exact Hctx0].
  + (* EIf e1 e2 e3 *)
    destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
    injection Hrename as <- _.
    inversion Htyped; subst.
    (* Decompose disjointness from free_vars(EIf e1 e2 e3) = fv(e1) ++ fv(e2) ++ fv(e3) *)
    destruct (disjoint_names_app_l (free_vars_expr e1)
      (free_vars_expr e2 ++ free_vars_expr e3) (rename_range ρ)) as [Hdisj1 Hdisj23].
    { intros x Hin. apply Hdisj. simpl. exact Hin. }
    destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
      (rename_range ρ)) as [Hdisj2 Hdisj3].
    { exact Hdisj23. }
    (* Apply IH to e1 *)
    lazymatch goal with
    | Hte1 : typed fenvr n Γr e1r ?Tcr ?Γ1r |- _ =>
      destruct (IH fenv0 fenvr n ρ Γ0 Γr e1 e1r used used1 Tcr Γ1r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx Hctx_used Hrange_used Hdisj1 He1 Hte1)
        as [Γ01 [Htyped1 Hctx1]]
    end.
    (* Build Hctx_used1: ctx_names(Γ1) ⊆ used1 *)
    assert (Hctx_used1 : forall x, In x (ctx_names Γ1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends. exact He1.
      apply Hctx_used.
      rewrite <- (ctx_same_bindings_names Γr Γ1).
      - exact Hin.
      - destruct typed_same_bindings as [Hsame _].
        lazymatch goal with
        | Hte1 : typed fenvr n Γr e1r _ _ |- _ => eapply Hsame; exact Hte1
        end. }
    assert (Hrange_used1 : forall x, In x (rename_range ρ) -> In x used1).
    { intros x Hinr. eapply alpha_rename_expr_used_extends; [exact He1 | exact (Hrange_used x Hinr)]. }
    (* Apply IH to e2 (starting from Γ01/Γ1) *)
    lazymatch goal with
    | Hte2 : typed fenvr n Γ1 e2r ?T2r ?Γ2r |- _ =>
      destruct (IH fenv0 fenvr n ρ Γ01 Γ1 e2 e2r used1 used2 T2r Γ2r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx1 Hctx_used1 Hrange_used1 Hdisj2 He2 Hte2)
        as [Γ02 [Htyped2 Hctx2]]
    end.
    (* Build Hctx_used2: ctx_names(Γ1) ⊆ used2 *)
    assert (Hctx_used2 : forall x, In x (ctx_names Γ1) -> In x used2).
    { intros x Hin. eapply alpha_rename_expr_used_extends; [exact He2 | exact (Hctx_used1 x Hin)]. }
    assert (Hrange_used2 : forall x, In x (rename_range ρ) -> In x used2).
    { intros x Hinr. eapply alpha_rename_expr_used_extends; [exact He2 | exact (Hrange_used1 x Hinr)]. }
    (* Apply IH to e3 (starting from Γ01/Γ1) *)
    lazymatch goal with
    | Hte3 : typed fenvr n Γ1 e3r ?T3r ?Γ3r |- _ =>
      destruct (IH fenv0 fenvr n ρ Γ01 Γ1 e3 e3r used2 used3 T3r Γ3r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx1 Hctx_used2 Hrange_used2 Hdisj3 He3 Hte3)
        as [Γ03 [Htyped3 Hctx3]]
    end.
    (* Merge backward: ctx_alpha ρ Γ02 Γ2 ∧ ctx_alpha ρ Γ03 Γ3 → merge Γ02 Γ03 works *)
    lazymatch goal with
    | Hmerge : ctx_merge ?Γ2r ?Γ3r = Some ?Γ4r |- _ =>
      destruct (ctx_alpha_merge_backward ρ Γ02 Γ2r Γ03 Γ3r Γ4r Hctx2 Hctx3 Hmerge)
        as [Γ04 [Hmerge04 Hctx4]]
    end.
    exists Γ04. split.
    { lazymatch goal with
      | Hbool : ty_core _ = TBooleans,
        Hcore : ty_core ?T2_ = ty_core ?T3_ |- _ =>
        eapply T_If;
        [exact Htyped1 | exact Hbool | exact Htyped2 | exact Htyped3
        | exact Hcore | exact Hmerge04]
      end. }
    { exact Hctx4. }
  }
  intros fenv0 fenvr n ρ Γ0 Γr e er used used' T Γr'
    Hfenv Hctx Hctx_used Hrange_used Hdisj Hrename Htyped.
  eapply (Hsize (S (expr_size e))).
  - apply Nat.lt_succ_diag_r.
  - exact Hfenv.
  - exact Hctx.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename.
  - exact Htyped.
Qed.

Theorem alpha_rename_for_infer_typed_backward : forall fenv n Γ e fenv' e' T Γ',
  alpha_rename_for_infer Γ fenv e = (fenv', e') ->
  typed fenv' n Γ e' T Γ' ->
  typed fenv n Γ e T Γ'.
Proof.
  intros fenv n Γ e fenv' e' T Γ' Hrename Htyped.
  unfold alpha_rename_for_infer in Hrename.
  destruct (alpha_rename_syntax_go (free_vars_expr e ++ ctx_names Γ) fenv)
    as [fenv0 used] eqn:Hfenv.
  destruct (alpha_rename_expr [] used e) as [er used'] eqn:He.
  injection Hrename as <- <-.
  pose proof (alpha_rename_syntax_go_shape
    (free_vars_expr e ++ ctx_names Γ) fenv fenv0 used Hfenv) as Hfenv_alpha.
  assert (Hctx_used : forall x, In x (ctx_names Γ) -> In x used).
  { intros x Hin.
    eapply alpha_rename_syntax_go_used_extends.
    - exact Hfenv.
    - apply in_or_app. right. exact Hin. }
  assert (Hrange_used : forall x, In x (rename_range []) -> In x used).
  { intros x Hin. contradiction. }
  assert (Hdisj : disjoint_names (free_vars_expr e) (rename_range [])).
  { apply disjoint_names_nil_r. }
  pose proof (alpha_rename_typed_backward
    fenv fenv0 n [] Γ Γ e er used used' T Γ'
    Hfenv_alpha (CtxAlpha_Base Γ)
    Hctx_used Hrange_used Hdisj He Htyped)
    as [Γ0 [Htyped0 Hctx_alpha]].
  pose proof (ctx_alpha_nil_eq Γ0 Γ' Hctx_alpha) as Heq.
  subst Γ0.
  exact Htyped0.
Qed.
