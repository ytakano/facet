From Facet.TypeSystem Require Import Types Syntax PathState Renaming TypingRules TypeChecker EnvStructuralRules.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

Scheme typed_ind' := Induction for typed Sort Prop
with typed_args_ind' := Induction for typed_args Sort Prop.
Combined Scheme typed_typed_args_ind from typed_ind', typed_args_ind'.

Scheme typed_env_structural_ind' := Induction for typed_env_structural Sort Prop
with typed_args_env_structural_ind' := Induction for typed_args_env_structural Sort Prop
with typed_fields_env_structural_ind' := Induction for typed_fields_env_structural Sort Prop.
Combined Scheme typed_env_structural_mutind from
  typed_env_structural_ind',
  typed_args_env_structural_ind',
  typed_fields_env_structural_ind'.

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

Inductive expr_alpha : rename_env -> expr -> expr -> Prop :=
  | EA_Unit : forall ρ,
      expr_alpha ρ EUnit EUnit
  | EA_Lit : forall ρ l,
      expr_alpha ρ (ELit l) (ELit l)
  | EA_Var : forall ρ x,
      ~ In x (rename_range ρ) ->
      expr_alpha ρ (EVar x) (EVar (lookup_rename x ρ))
  | EA_Fn : forall ρ fname,
      expr_alpha ρ (EFn fname) (EFn fname)
  | EA_Place : forall ρ p pr,
      place_alpha ρ p pr ->
      expr_alpha ρ (EPlace p) (EPlace pr)
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
  | EA_CallExpr : forall ρ callee calleer args argsr,
      expr_alpha ρ callee calleer ->
      exprs_alpha ρ args argsr ->
      expr_alpha ρ (ECallExpr callee args) (ECallExpr calleer argsr)
  | EA_Struct : forall ρ name lts args fields fieldsr,
      expr_alpha ρ (EStruct name lts args fields) (EStruct name lts args fieldsr)
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

Lemma expr_as_place_alpha_rename_some_backward : forall ρ used e er used' pr,
  alpha_rename_expr ρ used e = (er, used') ->
  expr_as_place er = Some pr ->
  exists p, expr_as_place e = Some p /\ pr = rename_place ρ p.
Proof.
  intros ρ used e. revert used.
  induction e; intros used er used' pr Hrename Hplace; simpl in Hrename;
    try (injection Hrename as <- _; simpl in Hplace; discriminate).
  - injection Hrename as <- _. simpl in Hplace.
    injection Hplace as <-.
    exists (PVar i). split; reflexivity.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - injection Hrename as <- _. simpl in Hplace.
    injection Hplace as <-.
    exists p. split; reflexivity.
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used0 l).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
                : list (string * expr) * list ident :=
                 match fields0 with
                 | [] => ([], used0)
                 | (fname, e0) :: rest =>
                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
                     let (rest', used2) := go used1 rest in
                     ((fname, e0') :: rest', used2)
                 end) used l1).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- <-. simpl in Hplace.
    destruct (expr_as_place er0) as [pr0 |] eqn:Hpr0; [|discriminate].
    injection Hplace as <-.
    destruct (IHe used er0 used0 pr0 He Hpr0) as [p [Hp Hrename_p]].
    exists (PDeref p). split.
    + simpl. rewrite Hp. reflexivity.
    + simpl. rewrite Hrename_p. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2].
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3].
    injection Hrename as <- _. simpl in Hplace. discriminate.
Qed.

Lemma expr_as_place_alpha_rename_none_backward : forall ρ used e er used',
  alpha_rename_expr ρ used e = (er, used') ->
  expr_as_place er = None ->
  expr_as_place e = None.
Proof.
  intros ρ used e. revert used.
  induction e; intros used er used' Hrename Hnone; simpl in Hrename;
    try (injection Hrename as <- _; reflexivity).
  - injection Hrename as <- _. simpl in Hnone. discriminate.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. reflexivity.
  - injection Hrename as <- _. simpl in Hnone. discriminate.
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l).
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used0 l).
    injection Hrename as <- _. reflexivity.
  - destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
                : list (string * expr) * list ident :=
                 match fields0 with
                 | [] => ([], used0)
                 | (fname, e0) :: rest =>
                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
                     let (rest', used2) := go used1 rest in
                     ((fname, e0') :: rest', used2)
                 end) used l1).
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- <-. simpl in Hnone.
    destruct (expr_as_place er0) as [pr |] eqn:Hpr; [discriminate |].
    simpl. rewrite (IHe used er0 used0 He Hpr). reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2].
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3].
    injection Hrename as <- _. reflexivity.
Qed.

Lemma expr_as_place_place_name_in_free_vars : forall e p,
  expr_as_place e = Some p ->
  In (place_name p) (free_vars_expr e).
Proof.
  induction e; intros p0 Hplace; simpl in Hplace; try discriminate.
  - injection Hplace as <-. simpl. left. reflexivity.
  - injection Hplace as <-. simpl. left. reflexivity.
  - destruct (expr_as_place e) as [p1 |] eqn:Hp1; [|discriminate].
    injection Hplace as <-. simpl.
    exact (IHe p1 eq_refl).
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
  destruct (ctx_lookup_state (lookup_rename x ρ) Γr) as [[Tx st] |] eqn:Hlookup;
    try contradiction.
  rewrite (ctx_alpha_lookup_state_backward ρ Γ Γr x Tx st Halpha Hsafe Hlookup).
  exact Hok.
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
    + destruct (Bool.eqb (st_consumed b2) (st_consumed b3)) eqn:Heqb; [|discriminate].
      injection Hmerge as <-. constructor. eapply IH. exact Hrest.
    + injection Hmerge as <-. constructor. eapply IH. exact Hrest.
    + injection Hmerge as <-. constructor. eapply IH. exact Hrest.
Qed.

Lemma typed_same_bindings :
  (forall fenv Ω n Γ e T Γ',
      typed fenv Ω n Γ e T Γ' ->
      ctx_same_bindings Γ Γ') /\
  (forall fenv Ω n Γ es ps Γ',
      typed_args fenv Ω n Γ es ps Γ' ->
      ctx_same_bindings Γ Γ').
Proof.
  assert (H : forall fenv Ω n,
    (forall Γ e T Γ',
        typed fenv Ω n Γ e T Γ' -> ctx_same_bindings Γ Γ') /\
    (forall Γ es ps Γ',
        typed_args fenv Ω n Γ es ps Γ' -> ctx_same_bindings Γ Γ')).
  {
    intros fenv Ω n.
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
  split; intros fenv Ω n; destruct (H fenv Ω n) as [Ht Hargs]; [apply Ht | apply Hargs].
Qed.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EUnit => 1
  | ELit _ => 1
  | EVar _ => 1
  | EFn _ => 1
  | EPlace _ => 1
  | ELet _ _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ELetInfer _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ECall _ args =>
      S ((fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | ECallExpr callee args =>
      S (expr_size callee +
         (fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | EStruct _ _ _ fields =>
      S ((fix go (fields0 : list (string * expr)) : nat :=
            match fields0 with
            | [] => 0
            | (_, e) :: rest => expr_size e + go rest
            end) fields)
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

Lemma expr_size_callexpr_callee_lt : forall callee args,
  expr_size callee < expr_size (ECallExpr callee args).
Proof.
  intros. simpl. lia.
Qed.

Lemma expr_size_callexpr_arg_lt : forall callee args arg,
  In arg args ->
  expr_size arg < expr_size (ECallExpr callee args).
Proof.
  intros callee args.
  induction args as [| a rest IH]; intros arg Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH arg Hin). simpl in IH. lia.
Qed.

Lemma expr_size_struct_field_lt : forall name lts args fields fname field_expr,
  In (fname, field_expr) fields ->
  expr_size field_expr < expr_size (EStruct name lts args fields).
Proof.
  intros name lts args fields.
  induction fields as [| [fname0 e0] rest IH]; intros fname field_expr Hin.
  - contradiction.
  - simpl in *. destruct Hin as [Heq | Hin].
    + injection Heq as _ <-. lia.
    + specialize (IH fname field_expr Hin). simpl in IH. lia.
Qed.

Lemma expr_size_struct_field_snd_lt : forall name lts args fields field_expr,
  In field_expr (map snd fields) ->
  expr_size field_expr < expr_size (EStruct name lts args fields).
Proof.
  intros name lts args fields.
  induction fields as [| [fname e] rest IH]; intros field_expr Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst field_expr. simpl. lia.
    + specialize (IH field_expr Hin).
      eapply Nat.lt_le_trans.
      * exact IH.
      * simpl. lia.
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

Lemma alpha_rename_struct_fields_used_extends : forall ρ used fields fieldsr used',
  (forall used0 fname e er used1,
      In (fname, e) fields ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      forall x, In x used0 -> In x used1) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr ρ used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  forall x, In x used -> In x used'.
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname e] rest IH]; intros used fieldsr used' Hexpr Hrename x Hin;
    simpl in Hrename.
  - injection Hrename as _ <-. exact Hin.
  - destruct (alpha_rename_expr ρ used e) as [er used1] eqn:He.
    destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
          : list (string * expr) * list ident :=
          match fields0 with
          | [] => ([], used0)
          | (fname0, e0) :: rest0 =>
              let (e0', used2) := alpha_rename_expr ρ used0 e0 in
              let (rest', used3) := go used2 rest0 in
              ((fname0, e0') :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as _ <-.
    eapply IH.
    + intros used0 fname0 e0 er0 used_tail Hin_rest Hrename0.
      eapply Hexpr.
      * right. exact Hin_rest.
      * exact Hrename0.
    + exact Hrest.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
      * exact Hin.
Qed.

Lemma alpha_rename_struct_fields_lookup_forward : forall ρ used fields fieldsr used' fname e er,
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname0, e0) :: rest =>
          let (e0', used1) := alpha_rename_expr ρ used0 e0 in
          let (rest', used2) := go used1 rest in
          ((fname0, e0') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  lookup_field_b fname fields = Some e ->
  (forall used0 e0 er0 used1,
      In e0 (map snd fields) ->
      alpha_rename_expr ρ used0 e0 = (er0, used1) ->
      e0 = e ->
      er0 = er) ->
  lookup_field_b fname fieldsr = Some er.
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname0 e0] rest IH]; intros used fieldsr used' fname e er Hrename Hlookup Hexpr;
    simpl in Hrename, Hlookup.
  - discriminate.
  - destruct (alpha_rename_expr ρ used e0) as [e0r used1] eqn:He0.
    destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
          : list (string * expr) * list ident :=
          match fields0 with
          | [] => ([], used0)
          | (fname1, e1) :: rest1 =>
              let (e1', used2) := alpha_rename_expr ρ used0 e1 in
              let (rest', used3) := go used2 rest1 in
              ((fname1, e1') :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    simpl.
    destruct (String.eqb fname fname0) eqn:Hname.
    + injection Hlookup as <-.
      pose proof (Hexpr used e0 e0r used1) as Heq_er.
      assert (e0r = er) as ->.
      { apply Heq_er.
        - simpl. left. reflexivity.
        - exact He0.
        - reflexivity. }
      reflexivity.
    + eapply IH.
      * exact Hrest.
      * exact Hlookup.
      * intros used0 e1 er1 used_tail Hin Hren Heq.
        eapply Hexpr.
        -- simpl. right. exact Hin.
        -- exact Hren.
        -- exact Heq.
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
	  + injection Hrename as _ <-. exact Hin.
	  + injection Hrename as _ <-. exact Hin.
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
  + destruct (alpha_rename_expr ρ used e) as [callee_r used0] eqn:Hcallee.
    remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used0 l) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as _ <-.
    eapply alpha_rename_call_args_used_extends.
    * intros used_arg earg er0 used_tail Hin_arg Hrename0.
      eapply IH.
      -- pose proof (expr_size_callexpr_arg_lt e l earg Hin_arg) as Harg_lt.
        assert (expr_size earg < n) as Hlt_arg by lia.
        exact Hlt_arg.
      -- exact Hrename0.
    * symmetry. exact Hargs.
    * eapply IH.
      -- pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
        assert (expr_size e < n) as Hlt_callee by lia.
        exact Hlt_callee.
      -- exact Hcallee.
      -- exact Hin.
  + remember
      ((fix go (used0 : list ident) (fields0 : list (string * expr))
          : list (string * expr) * list ident :=
          match fields0 with
          | [] => ([], used0)
          | (fname, e0) :: rest =>
              let (e0', used1) := alpha_rename_expr ρ used0 e0 in
              let (rest', used2) := go used1 rest in
              ((fname, e0') :: rest', used2)
          end) used l1) as r eqn:Hfields.
    destruct r as [fieldsr used_fields].
    injection Hrename as _ <-.
    eapply alpha_rename_struct_fields_used_extends.
    * intros used0 fname efield er0 used1 Hin_field Hrename0.
      eapply IH.
      -- pose proof (expr_size_struct_field_lt s l l0 l1 fname efield Hin_field) as Hfield_lt.
         assert (expr_size efield < n) as Hlt_field by lia.
         exact Hlt_field.
      -- exact Hrename0.
    * symmetry. exact Hfields.
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
  - simpl in Hrename. inversion Hrename; subst. exact Hin.
  - simpl in Hrename.
    destruct (alpha_rename_params
      ρ
      (fresh_ident (param_name p) used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst.
    eapply IH.
    + exact Hps.
    + right. exact Hin.
Qed.

Lemma alpha_rename_params_names_fresh_used : forall ρ used ps psr ρ' used',
  alpha_rename_params ρ used ps = (psr, ρ', used') ->
  forall x, In x (ctx_names (params_ctx psr)) -> ~ In x used.
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Hrename x Hin Hused.
  - simpl in Hrename. inversion Hrename; subst.
    simpl in Hin. contradiction.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params
      ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst.
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst x. eapply fresh_ident_not_in. exact Hused.
    + eapply IH.
      * exact Hps.
      * exact Hin.
      * right. exact Hused.
Qed.

Lemma alpha_rename_params_names_nodup : forall ρ used ps psr ρ' used',
  alpha_rename_params ρ used ps = (psr, ρ', used') ->
  NoDup (ctx_names (params_ctx psr)).
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Hrename.
  - simpl in Hrename. inversion Hrename; subst.
    constructor.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params
      ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst.
    simpl.
    constructor.
    + intro Hin.
      eapply alpha_rename_params_names_fresh_used.
      * exact Hps.
      * exact Hin.
      * left. reflexivity.
    + eapply IH. exact Hps.
Qed.

Lemma alpha_rename_params_names_in_used : forall ρ used ps psr ρ' used',
  alpha_rename_params ρ used ps = (psr, ρ', used') ->
  forall x, In x (ctx_names (params_ctx psr)) -> In x used'.
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Hrename x Hin.
  - simpl in Hrename. inversion Hrename; subst.
    simpl in Hin. contradiction.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params
      ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst.
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst x.
      eapply alpha_rename_params_used_extends.
      * exact Hps.
      * simpl. left. reflexivity.
    + eapply IH.
      * exact Hps.
      * exact Hin.
Qed.

Lemma alpha_rename_params_range_ctx_or_tail : forall ρ used ps psr ρ' used',
  alpha_rename_params ρ used ps = (psr, ρ', used') ->
  forall x, In x (rename_range ρ') ->
    In x (ctx_names (params_ctx psr)) \/ In x (rename_range ρ).
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Hrename x Hin.
  - simpl in Hrename. inversion Hrename; subst.
    right. exact Hin.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params
      ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst.
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst x. left. simpl. left. reflexivity.
    + destruct (IH _ _ _ _ _ Hps _ Hin) as [Hctx | Hrange].
      * left. simpl. right. exact Hctx.
      * right. exact Hrange.
Qed.

Lemma alpha_rename_params_ctx_alpha_nil : forall used ps psr ρ' used',
  alpha_rename_params [] used ps = (psr, ρ', used') ->
  ctx_alpha ρ' (params_ctx ps) (params_ctx psr).
Proof.
  intros used ps.
  revert used.
  induction ps as [| p ps IH]; intros used psr ρ' used' Hrename.
  - simpl in Hrename. inversion Hrename; subst.
    constructor.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params
      [] (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst.
    simpl.
    constructor.
    + eapply IH. exact Hps.
    + intro Hin.
      eapply alpha_rename_params_names_fresh_used.
      * exact Hps.
      * exact Hin.
      * left. reflexivity.
    + intro Hin.
      destruct (alpha_rename_params_range_ctx_or_tail
        _ _ _ _ _ _ Hps _ Hin) as [Hctx | Htail].
      * eapply alpha_rename_params_names_fresh_used.
        -- exact Hps.
        -- exact Hctx.
        -- left. reflexivity.
      * simpl in Htail. contradiction.
Qed.

Lemma alpha_rename_params_range_in_used_nil : forall used ps psr ρ' used',
  alpha_rename_params [] used ps = (psr, ρ', used') ->
  forall x, In x (rename_range ρ') -> In x used'.
Proof.
  intros used ps psr ρ' used' Hrename x Hin.
  destruct (alpha_rename_params_range_ctx_or_tail
    _ _ _ _ _ _ Hrename _ Hin) as [Hctx | Htail].
  - eapply alpha_rename_params_names_in_used; eauto.
  - simpl in Htail. contradiction.
Qed.

Lemma alpha_rename_params_range_fresh_used_nil : forall used ps psr ρ' used',
  alpha_rename_params [] used ps = (psr, ρ', used') ->
  forall x, In x (rename_range ρ') -> ~ In x used.
Proof.
  intros used ps psr ρ' used' Hrename x Hin Hused.
  destruct (alpha_rename_params_range_ctx_or_tail
    _ _ _ _ _ _ Hrename _ Hin) as [Hctx | Htail].
  - eapply alpha_rename_params_names_fresh_used; eauto.
  - simpl in Htail. contradiction.
Qed.

Lemma params_ctx_names_param_names : forall ps,
  ctx_names (params_ctx ps) = param_names ps.
Proof.
  induction ps as [| p ps IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma sctx_check_ok_cons_ne : forall env x y T Ty st m Σ,
  x <> y ->
  sctx_check_ok env x T ((y, Ty, st, m) :: Σ) =
  sctx_check_ok env x T Σ.
Proof.
  intros env x y T Ty st m Σ Hneq.
  unfold sctx_check_ok, sctx_lookup.
  destruct (ty_usage T); try reflexivity.
  simpl.
  destruct (ident_eqb x y) eqn:Hxy.
  - apply ident_eqb_eq in Hxy. contradiction.
  - reflexivity.
Qed.

Lemma params_ok_sctx_b_cons_notin : forall env ps y T st m Σ,
  ~ In y (param_names ps) ->
  params_ok_sctx_b env ps ((y, T, st, m) :: Σ) =
  params_ok_sctx_b env ps Σ.
Proof.
  intros env ps.
  induction ps as [| p ps IH]; intros y T st m Σ Hnotin.
  - reflexivity.
  - simpl in Hnotin |- *.
    rewrite sctx_check_ok_cons_ne.
    + rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
    + intros Heq. apply Hnotin. left. exact Heq.
Qed.

Lemma alpha_rename_params_params_ok_sctx_b_forward :
  forall env used ps psr ρ used' Σ Σr,
    alpha_rename_params [] used ps = (psr, ρ, used') ->
    NoDup (param_names ps) ->
    (forall x, In x (param_names ps) -> In x used) ->
    ctx_alpha ρ Σ Σr ->
    params_ok_sctx_b env ps Σ = true ->
    params_ok_sctx_b env psr Σr = true.
Proof.
  intros env used ps.
  revert used.
  induction ps as [| p ps IH]; intros used psr ρ used' Σ Σr
    Hrename Hnodup Hused Halpha Hparams.
  - simpl in Hrename. inversion Hrename; subst.
    inversion Halpha; subst. reflexivity.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params [] (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst. simpl in Hparams.
    inversion Hnodup as [| ? ? Hxp_notin Hnodup_tail]; subst.
    inversion Halpha as [| ? Γ Γr ? xr Tctx stctx mctx Halpha_tail
      Hfresh_ctx Hfresh_range]; subst.
    simpl.
    apply andb_true_iff in Hparams as [Hhead Htail_full].
    assert (Hxp_used : In xp used).
    { apply Hused. simpl. left. reflexivity. }
    assert (Hsafe_xp : ~ In xp (rename_range ((xp, fresh_ident xp used) :: ρ0))).
    { simpl. intros [Heq | Hin].
      - apply (fresh_ident_not_in xp used). rewrite Heq. exact Hxp_used.
      - eapply alpha_rename_params_range_fresh_used_nil.
        + exact Hps.
        + exact Hin.
        + simpl. right. exact Hxp_used. }
    assert (Hhead_r :
      sctx_check_ok env (fresh_ident xp used) T
        ((fresh_ident xp used, Tctx, stctx, mctx) :: Γr) = true).
    { assert (Hlookup_xp :
        lookup_rename xp ((xp, fresh_ident xp used) :: ρ0) =
        fresh_ident xp used).
      { simpl. rewrite ident_eqb_refl. reflexivity. }
      assert (Hhead_lookup :
        sctx_check_ok env
          (lookup_rename xp ((xp, fresh_ident xp used) :: ρ0)) T
          ((fresh_ident xp used, Tctx, stctx, mctx) :: Γr) = true).
      { eapply ctx_alpha_check_ok_forward.
        - exact Halpha.
        - exact Hsafe_xp.
        - exact Hhead. }
      rewrite Hlookup_xp in Hhead_lookup.
      exact Hhead_lookup. }
    rewrite Hhead_r.
    rewrite (params_ok_sctx_b_cons_notin env ps0 (fresh_ident xp used)
      Tctx stctx mctx Γr).
    + eapply IH.
      * exact Hps.
      * exact Hnodup_tail.
      * intros x Hin. simpl. right. apply Hused. simpl. right. exact Hin.
      * exact Halpha_tail.
      * rewrite <- (params_ok_sctx_b_cons_notin env ps xp
          Tctx stctx mctx Γ).
        -- exact Htail_full.
        -- exact Hxp_notin.
    + rewrite <- params_ctx_names_param_names.
      intro Hin.
      eapply alpha_rename_params_names_fresh_used.
      * exact Hps.
      * exact Hin.
      * simpl. left. reflexivity.
Qed.

Lemma alpha_rename_params_params_ok_env_b_forward :
  forall env used ps psr ρ used' Γ Γr,
    alpha_rename_params [] used ps = (psr, ρ, used') ->
    NoDup (ctx_names (params_ctx ps)) ->
    (forall x, In x (param_names ps) -> In x used) ->
    ctx_alpha ρ (sctx_of_ctx Γ) (sctx_of_ctx Γr) ->
    params_ok_env_b env ps Γ = true ->
    params_ok_env_b env psr Γr = true.
Proof.
  intros env used ps psr ρ used' Γ Γr Hrename Hnodup Hused Halpha Hparams.
  unfold params_ok_env_b in *.
  eapply alpha_rename_params_params_ok_sctx_b_forward.
  - exact Hrename.
  - rewrite <- params_ctx_names_param_names. exact Hnodup.
  - exact Hused.
  - exact Halpha.
  - exact Hparams.
Qed.

Lemma alpha_rename_fn_def_used_extends : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  forall x, In x used -> In x used'.
Proof.
  intros used f fr used' Hrename x Hin.
  destruct f as [fname lifetimes outs ps ret body].
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

Lemma alpha_rename_fn_def_params_fresh_used : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  forall x, In x (ctx_names (params_ctx (fn_params fr))) -> ~ In x used.
Proof.
  intros used f fr used' Hrename x Hin Hused.
  destruct f as [fname lifetimes outs ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl in Hin.
  eapply alpha_rename_params_names_fresh_used.
  - exact Hps.
  - exact Hin.
  - apply in_or_app. right. apply in_or_app. right. exact Hused.
Qed.

Lemma alpha_rename_fn_def_params_nodup : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  NoDup (ctx_names (params_ctx (fn_params fr))).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  eapply alpha_rename_params_names_nodup. exact Hps.
Qed.

Lemma alpha_rename_fn_def_params_ctx_alpha : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  exists ρ, ctx_alpha ρ
    (params_ctx (fn_params f)) (params_ctx (fn_params fr)).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  exists ρ.
  eapply alpha_rename_params_ctx_alpha_nil. exact Hps.
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
	  + injection Hrename as <- _. constructor.
	  + injection Hrename as <- _.
	    apply EA_Place.
	    apply rename_place_alpha_sound.
	    intros Hin_range. apply (Hdisj (place_name p)).
	    * simpl. left. reflexivity.
	    * exact Hin_range.
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
  + destruct (disjoint_names_app_l (free_vars_expr e)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg :: rest => free_vars_expr arg ++ go rest
          end) l) (rename_range ρ) Hdisj) as [Hdisj_callee Hdisj_args].
    destruct (alpha_rename_expr ρ used e) as [callee_r used0] eqn:Hcallee.
    remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used0 l) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as <- _.
    constructor.
    * eapply IH.
      -- pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
         assert (expr_size e < n) as Hlt_callee by lia.
         exact Hlt_callee.
      -- exact Hdisj_callee.
      -- exact Hcallee.
    * eapply alpha_rename_call_args_sound.
      -- intros used_arg earg er0 used_tail Hin_arg Hdisj0 Hrename0.
         eapply IH.
         ++ pose proof (expr_size_callexpr_arg_lt e l earg Hin_arg) as Harg_lt.
            assert (expr_size earg < n) as Hlt_arg by lia.
            exact Hlt_arg.
         ++ exact Hdisj0.
         ++ exact Hrename0.
	      -- exact Hdisj_args.
	      -- symmetry. exact Hargs.
	  + remember
	      ((fix go (used0 : list ident) (fields0 : list (string * expr))
	          : list (string * expr) * list ident :=
	          match fields0 with
	          | [] => ([], used0)
	          | (fname, e0) :: rest =>
	              let (e0', used1) := alpha_rename_expr ρ used0 e0 in
	              let (rest', used2) := go used1 rest in
	              ((fname, e0') :: rest', used2)
	          end) used l1) as r eqn:Hfields.
	    destruct r as [fieldsr used_fields].
	    injection Hrename as <- _.
	    apply EA_Struct.
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
      ρ (fresh_ident x used :: used) ps)
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
  destruct f as [fname lifetimes outs ps ret body].
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

Lemma typed_args_cons_inv : forall fenv Ω n Γ er ers pr psr Γ',
  typed_args fenv Ω n Γ (er :: ers) (pr :: psr) Γ' ->
  exists T Γ1,
    typed fenv Ω n Γ er T Γ1 /\
    ty_compatible Ω T (param_ty pr) /\
    typed_args fenv Ω n Γ1 ers psr Γ'.
Proof.
  intros fenv Ω n Γ er ers pr psr Γ' Htyped.
  inversion Htyped; subst.
  exists T_e, Γ1. repeat split; assumption.
Qed.

Lemma typed_call_inv : forall fenv Ω n Γ fname args T Γ',
  typed fenv Ω n Γ (ECall fname args) T Γ' ->
  exists fdef σ,
    In fdef fenv /\
    fn_name fdef = fname /\
    apply_lt_ty σ (fn_ret fdef) = T /\
    typed_args fenv Ω n Γ args (apply_lt_params σ (fn_params fdef)) Γ'.
Proof.
  intros fenv Ω n Γ fname args T Γ' Htyped.
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

Lemma alpha_rename_call_args_typed_backward : forall fenv0 fenvr Ω n ρ Γ0 Γr args argsr used used' ps0 psr Γr',
  (forall Γa Γb used0 e er used1 T Γb',
      In e args ->
      ctx_alpha ρ Γa Γb ->
      (forall x, In x (ctx_names Γb) -> In x used0) ->
      (forall x, In x (rename_range ρ) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      typed fenvr Ω n Γb er T Γb' ->
      exists Γa',
        typed fenv0 Ω n Γa e T Γa' /\
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
  typed_args fenvr Ω n Γr argsr psr Γr' ->
  exists Γ0',
    typed_args fenv0 Ω n Γ0 args ps0 Γ0' /\
    ctx_alpha ρ Γ0' Γr'.
Proof.
  intros fenv0 fenvr Ω n ρ Γ0 Γr args.
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
    destruct (typed_args_cons_inv fenvr Ω n Γr ar restr pr psr_tail Γr' Htyped_args)
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
    + (* ULinear: Hmerge has the form (if Bool.eqb consumed flags then ... else ...) = Some _ *)
      lazymatch goal with
      | Hm : (if Bool.eqb (st_consumed b2) (st_consumed ?bX) then _ else _) = Some _ |- _ =>
          destruct (Bool.eqb (st_consumed b2) (st_consumed bX)) eqn:Heqb;
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

Lemma ctx_alpha_merge_forward : forall ρ Γ02 Γ2r Γ03 Γ3r Γ4,
  ctx_alpha ρ Γ02 Γ2r ->
  ctx_alpha ρ Γ03 Γ3r ->
  ctx_merge Γ02 Γ03 = Some Γ4 ->
  exists Γ4r, ctx_merge Γ2r Γ3r = Some Γ4r /\ ctx_alpha ρ Γ4 Γ4r.
Proof.
  intros ρ Γ02 Γ2r Γ03 Γ3r Γ4 Halpha2.
  revert Γ03 Γ3r Γ4.
  induction Halpha2 as [Γ02 | ρ' Γ02' Γ2r' x xr T b2 m2 Halpha2' IH2 Hxr_ctx Hxr_range];
    intros Γ03 Γ3r Γ4 Halpha3 Hmerge.
  - inversion Halpha3; subst.
    exists Γ4. split; [exact Hmerge | constructor].
  - inversion Halpha3; subst.
    simpl in Hmerge. rewrite ident_eqb_refl in Hmerge. simpl in Hmerge.
    lazymatch goal with
    | H_alpha3' : ctx_alpha ρ' ?Γ03t ?Γ3rt |- _ =>
        destruct (ctx_merge Γ02' Γ03t) as [rest4 |] eqn:Hmerge_rest;
        [| discriminate];
        destruct (IH2 Γ03t Γ3rt rest4 H_alpha3' Hmerge_rest)
          as [rest4r [Hmerge4r Hctx4r]];
        assert (Hrest_names : ~ In xr (ctx_names rest4r)) by
          (rewrite (ctx_same_bindings_names _ _
             (ctx_merge_same_bindings _ Γ3rt _ Hmerge4r));
           exact Hxr_ctx)
    end.
    simpl. rewrite ident_eqb_refl. simpl. rewrite Hmerge4r.
    destruct (ty_usage T) eqn:Hu.
    + lazymatch goal with
      | Hm : (if Bool.eqb (st_consumed b2) (st_consumed ?bX) then _ else _) = Some _ |- _ =>
          destruct (Bool.eqb (st_consumed b2) (st_consumed bX)) eqn:Heqb;
          [injection Hm as <-;
           eexists; split;
           [reflexivity |
            constructor; [exact Hctx4r | exact Hrest_names | exact Hxr_range]]
          | discriminate]
      end.
    + injection Hmerge as <-.
      eexists. split. reflexivity.
      constructor; [exact Hctx4r | exact Hrest_names | exact Hxr_range].
    + injection Hmerge as <-.
      eexists. split. reflexivity.
      constructor; [exact Hctx4r | exact Hrest_names | exact Hxr_range].
Qed.

Lemma sctx_same_bindings_names_alpha : forall Σ Σ',
  sctx_same_bindings Σ Σ' ->
  ctx_names Σ' = ctx_names Σ.
Proof.
  intros Σ Σ' Hsame.
  induction Hsame as [| [[[x T] st] m] [[[x' T'] st'] m'] Σ Σ'
      Hentry Htail IH].
  - reflexivity.
  - inversion Hentry; subst. simpl. rewrite IH. reflexivity.
Qed.

Lemma lookup_field_b_in_alpha : forall fname fields e,
  lookup_field_b fname fields = Some e ->
  In e (map snd fields).
Proof.
  intros fname fields.
  induction fields as [| [fname0 e0] rest IH]; intros e Hlookup;
    simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb fname fname0) eqn:Hname.
    + injection Hlookup as <-. simpl. left. reflexivity.
    + simpl. right. eapply IH. exact Hlookup.
Qed.

Lemma alpha_rename_struct_fields_lookup_exists_forward :
  forall ρ used fields fieldsr used' fname e,
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname0, e0) :: rest =>
          let (e0', used1) := alpha_rename_expr ρ used0 e0 in
          let (rest', used2) := go used1 rest in
          ((fname0, e0') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  lookup_field_b fname fields = Some e ->
  exists er used0 used1,
    lookup_field_b fname fieldsr = Some er /\
    alpha_rename_expr ρ used0 e = (er, used1) /\
    (forall x, In x used -> In x used0).
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname0 e0] rest IH]; intros used fieldsr used' fname e
    Hrename Hlookup; simpl in Hrename, Hlookup.
  - discriminate.
  - destruct (alpha_rename_expr ρ used e0) as [e0r used1] eqn:He0.
    destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
          : list (string * expr) * list ident :=
          match fields0 with
          | [] => ([], used0)
          | (fname1, e1) :: rest1 =>
              let (e1', used2) := alpha_rename_expr ρ used0 e1 in
              let (rest', used3) := go used2 rest1 in
              ((fname1, e1') :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct (String.eqb fname fname0) eqn:Hname.
    + injection Hlookup as <-.
      exists e0r, used, used1. repeat split.
      * simpl. rewrite Hname. reflexivity.
      * exact He0.
      * intros x Hin. exact Hin.
    + destruct (IH used1 restr used2 fname e Hrest Hlookup)
        as [er [used0 [used_tail [Hlookup_r [Hren Hused]]]]].
      exists er, used0, used_tail. repeat split.
      * simpl. rewrite Hname. exact Hlookup_r.
      * exact Hren.
      * intros x Hin. apply Hused.
        eapply alpha_rename_expr_used_extends.
        -- exact He0.
        -- exact Hin.
Qed.

Lemma typed_args_env_structural_cons_inv :
  forall env Ω n Σ e es p ps Σ',
  typed_args_env_structural env Ω n Σ (e :: es) (p :: ps) Σ' ->
  exists T_e Σ1,
    typed_env_structural env Ω n Σ e T_e Σ1 /\
    ty_compatible_b Ω T_e (param_ty p) = true /\
    typed_args_env_structural env Ω n Σ1 es ps Σ'.
Proof.
  intros env Ω n Σ e es p ps Σ' Htyped.
  inversion Htyped; subst.
  exists T_e, Σ1. repeat split; assumption.
Qed.

Lemma alpha_rename_typed_args_env_structural_forward :
  forall env Ω n ρ Σ Σr args argsr used used' ps psr Σ',
  (forall Σa Σb used0 e er used1 T Σa',
      In e args ->
      ctx_alpha ρ Σa Σb ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range ρ) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      typed_env_structural env Ω n Σa e T Σa' ->
      exists Σb',
        typed_env_structural env Ω n Σb er T Σb' /\
        ctx_alpha ρ Σa' Σb') ->
  ctx_alpha ρ Σ Σr ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range ρ) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range ρ) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr ρ used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  typed_args_env_structural env Ω n Σ args ps Σ' ->
  exists Σr',
    typed_args_env_structural env Ω n Σr argsr psr Σr' /\
    ctx_alpha ρ Σ' Σr'.
Proof.
  intros env Ω n ρ Σ Σr args.
  revert Σ Σr.
  induction args as [| arg rest IH]; intros Σ Σr argsr used used' ps psr Σ'
    Hexpr Hctx Hctx_used Hrange_used Hdisj Hparams Hrename Htyped_args;
    simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr. split; [constructor | exact Hctx].
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
    destruct ps as [| p ps_tail].
    { inversion Htyped_args. }
    destruct psr as [| pr psr_tail].
    { inversion Hparams. }
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    destruct (typed_args_env_structural_cons_inv env Ω n Σ arg rest p ps_tail Σ'
      Htyped_args) as [Targ [Σ1 [Htyped_arg [Hcompat Htyped_tail]]]].
    destruct (Hexpr Σ Σr used arg ar used1 Targ Σ1)
      as [Σr1 [Htyped_arg_r Hctx_arg]].
    + left. reflexivity.
    + exact Hctx.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + exact Htyped_arg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range ρ) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH Σ1 Σr1 restr used1 used2 ps_tail psr_tail Σ')
        as [Σr2 [Htyped_tail_r Hctx_tail]].
      * intros Σa Σb used0 e er used_tail T Σa' Hin Halpha Hcu Hru Hd Hr Ht.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Halpha.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
        -- exact Ht.
      * exact Hctx_arg.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exact Htyped_tail.
      * exists Σr2. split.
        -- eapply TESArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              exact Hcompat.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
Qed.

Lemma alpha_rename_typed_fields_env_structural_forward :
  forall env Ω n ρ lts args_ty Σ Σr fields fieldsr used used' defs Σ',
  (forall Σa Σb used0 e er used1 T Σa',
      In e (map snd fields) ->
      ctx_alpha ρ Σa Σb ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range ρ) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      typed_env_structural env Ω n Σa e T Σa' ->
      exists Σb',
        typed_env_structural env Ω n Σb er T Σb' /\
        ctx_alpha ρ Σa' Σb') ->
  ctx_alpha ρ Σ Σr ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range ρ) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range ρ) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr ρ used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  typed_fields_env_structural env Ω n lts args_ty Σ fields defs Σ' ->
  exists Σr',
    typed_fields_env_structural env Ω n lts args_ty Σr fieldsr defs Σr' /\
    ctx_alpha ρ Σ' Σr'.
Proof.
  intros env Ω n ρ lts args_ty Σ Σr fields fieldsr used used' defs Σ'
    Hexpr Hctx Hctx_used Hrange_used Hdisj Hrename Htyped_fields.
  revert Σr used fieldsr used' Hctx Hctx_used Hrange_used Hrename.
  induction Htyped_fields; intros Σr0 used0 fieldsr0 used_out
    Hctx Hctx_used Hrange_used Hrename.
  - exists Σr0. split; [constructor | exact Hctx].
  - destruct (alpha_rename_struct_fields_lookup_exists_forward ρ used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    destruct (Hexpr Σ Σr0 used_field e_field e_fieldr used_field_out
      T_field Σ1)
      as [Σr1 [Htyped_field_r Hctx_field]].
    + exact Hfield_in.
    + exact Hctx.
    + intros x Hin. apply Hused_prefix. apply Hctx_used. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used. exact Hin.
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
                 end) rest) (rename_range ρ) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range ρ) Hdisj) as [_ Hrest_disj].
           eapply IH.
           ++ exact Hrest_disj.
           ++ exact H.
    + exact Hrename_field.
    + exact H0.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr Hdisj Σr1 used0 fieldsr0 used_out
        Hctx_field Hctx_used_tail Hrange_used Hrename)
        as [Σr2 [Htyped_rest_r Hctx_rest]].
      exists Σr2. split.
      * eapply TESFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * exact Hctx_rest.
Qed.

Lemma params_alpha_refl : forall ps,
  params_alpha ps ps.
Proof.
  induction ps as [| [m x T] ps IH].
  - constructor.
  - constructor.
    + unfold same_param_shape. simpl. split; reflexivity.
    + exact IH.
Qed.

Lemma expr_as_place_alpha_rename_some_forward :
  forall ρ used e er used' p,
  alpha_rename_expr ρ used e = (er, used') ->
  expr_as_place e = Some p ->
  expr_as_place er = Some (rename_place ρ p).
Proof.
  intros ρ used e.
  revert used.
  induction e; intros used er used' p0 Hrename Hplace; simpl in Hrename;
    try (injection Hrename as <- _; simpl in Hplace; try discriminate;
         injection Hplace as <-; reflexivity).
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. discriminate.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. discriminate.
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l).
    injection Hrename as <- _. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used0 l).
    injection Hrename as <- _. discriminate.
  - destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
                : list (string * expr) * list ident :=
                 match fields0 with
                 | [] => ([], used0)
                 | (fname, e0) :: rest =>
                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
                     let (rest', used2) := go used1 rest in
                     ((fname, e0') :: rest', used2)
                 end) used l1).
    injection Hrename as <- _. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- <-.
    simpl in Hplace.
    destruct (expr_as_place e) as [p1 |] eqn:Hp0; [|discriminate].
    injection Hplace as <-.
    simpl. rewrite (IHe used er0 used0 p1 He eq_refl). reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. discriminate.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2].
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3].
    injection Hrename as <- _. discriminate.
Qed.

Lemma expr_as_place_alpha_rename_none_forward :
  forall ρ used e er used',
  alpha_rename_expr ρ used e = (er, used') ->
  expr_as_place e = None ->
  expr_as_place er = None.
Proof.
  intros ρ used e.
  revert used.
  induction e; intros used er used' Hrename Hplace; simpl in Hrename;
    try (injection Hrename as <- _; simpl in Hplace; try discriminate; exact Hplace).
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2).
    injection Hrename as <- _. reflexivity.
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l).
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used0 l).
    injection Hrename as <- _. reflexivity.
  - destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
                : list (string * expr) * list ident :=
                 match fields0 with
                 | [] => ([], used0)
                 | (fname, e0) :: rest =>
                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
                     let (rest', used2) := go used1 rest in
                     ((fname, e0') :: rest', used2)
                 end) used l1).
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- <-.
    simpl in Hplace |- *.
    destruct (expr_as_place e) as [p |] eqn:Hp; [discriminate |].
    rewrite (IHe used er0 used0 He eq_refl). reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e1) as [e1r used1].
    destruct (alpha_rename_expr ρ used1 e2) as [e2r used2].
    destruct (alpha_rename_expr ρ used2 e3) as [e3r used3].
    injection Hrename as <- _. reflexivity.
Qed.

Lemma alpha_rename_let_body_disjoint_forward :
  forall ρ used1 x xr e2,
    xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
    disjoint_names (free_vars_expr e2) (rename_range ρ) ->
    disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: ρ)).
Proof.
  intros ρ used1 x xr e2 Hxr Hdisj y Hy Hin.
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  - subst y.
    eapply fresh_ident_not_in.
    rewrite <- Hxr.
    right. apply in_or_app. left. exact Hy.
  - eapply Hdisj; eauto.
Qed.

Lemma alpha_rename_let_bound_safe_forward :
  forall ρ used1 x xr e2,
    xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
    ~ In x (rename_range ρ) ->
    ~ In x (rename_range ((x, xr) :: ρ)).
Proof.
  intros ρ used1 x xr e2 Hxr Hsafe Hin.
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  -
    eapply fresh_ident_not_in.
    rewrite <- Hxr.
    rewrite <- Heq.
    simpl. left. reflexivity.
  - exact (Hsafe Hin).
Qed.

Lemma alpha_rename_typed_env_structural_forward :
  forall env Ω n ρ Σ Σr e er used used' T Σ',
    ctx_alpha ρ Σ Σr ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range ρ) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range ρ) ->
    alpha_rename_expr ρ used e = (er, used') ->
    typed_env_structural env Ω n Σ e T Σ' ->
    exists Σr',
      typed_env_structural env Ω n Σr er T Σr' /\
      ctx_alpha ρ Σ' Σr'.
Proof.
  assert (Hsize : forall fuel env Ω n ρ Σ Σr e er used used' T Σ',
    expr_size e < fuel ->
    ctx_alpha ρ Σ Σr ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range ρ) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range ρ) ->
    alpha_rename_expr ρ used e = (er, used') ->
    typed_env_structural env Ω n Σ e T Σ' ->
    exists Σr',
      typed_env_structural env Ω n Σr er T Σr' /\
      ctx_alpha ρ Σ' Σr').
  {
    induction fuel as [| fuel IH]; intros env Ω n ρ Σ Σr e er used used' T Σ'
      Hlt Hctx Hctx_used Hrange_used Hdisj Hrename Htyped.
    - lia.
    - destruct Htyped; simpl in Hrename.
      + injection Hrename as <- <-.
        exists Σr. split; [constructor | exact Hctx].
      + injection Hrename as <- <-.
        exists Σr. split; [constructor | exact Hctx].
      + injection Hrename as <- <-.
        exists Σr. split; [constructor | exact Hctx].
      + injection Hrename as <- <-.
        exists Σr. split; [constructor | exact Hctx].
      + injection Hrename as <- <-.
        exists Σr. split.
        * eapply TES_Var_Copy.
          -- change (typed_place_env_structural env Σr
               (PVar (lookup_rename x ρ)) T) with
               (typed_place_env_structural env Σr
                 (rename_place ρ (PVar x)) T).
             eapply alpha_rename_typed_place_env_structural_forward.
             ++ exact Hctx.
             ++ apply Hdisj. simpl. left. reflexivity.
             ++ exact H.
          -- exact H0.
        * exact Hctx.
      + injection Hrename as <- <-.
        assert (Hsafe : ~ In x (rename_range ρ)).
        { apply Hdisj. simpl. left. reflexivity. }
        destruct (ctx_alpha_consume_path_forward
          ρ Σ Σr x [] Σ' Hctx Hsafe H1) as [Σr' [Hconsume_r Hctx_r]].
        exists Σr'. split.
        * eapply TES_Var_Move.
          -- change (typed_place_env_structural env Σr
               (PVar (lookup_rename x ρ)) T) with
               (typed_place_env_structural env Σr
                 (rename_place ρ (PVar x)) T).
             eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- exact H0.
          -- exact Hconsume_r.
        * exact Hctx_r.
      + injection Hrename as <- <-.
        exists Σr. split.
        * eapply TES_Place_Copy.
          -- eapply alpha_rename_typed_place_env_structural_forward.
             ++ exact Hctx.
             ++ rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity.
             ++ exact H.
          -- exact H0.
        * exact Hctx.
      + injection Hrename as <- <-.
        assert (Hsafe_root : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
        destruct (ctx_alpha_consume_path_forward
          ρ Σ Σr x path Σ' Hctx
          ltac:(rewrite <- (place_path_root p x path H1); exact Hsafe_root)
          H2) as [Σr' [Hconsume_r Hctx_r]].
        exists Σr'. split.
        * eapply TES_Place_Move.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- exact H0.
          -- eapply place_path_rename_place_some. exact H1.
          -- exact Hconsume_r.
        * exact Hctx_r.
      + injection Hrename as <- <-.
        exists Σr. split; [econstructor; eauto | exact Hctx].
      + destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
                    : list (string * expr) * list ident :=
                    match fields0 with
                    | [] => ([], used0)
                    | (fname, e) :: rest =>
                        let (e', used1) := alpha_rename_expr ρ used0 e in
                        let (rest', used2) := go used1 rest in
                        ((fname, e') :: rest', used2)
                    end) used fields) as [fieldsr used_fields] eqn:Hfields.
        injection Hrename as <- <-.
        destruct (alpha_rename_typed_fields_env_structural_forward
          env Ω n ρ lts args Σ Σr fields fieldsr used used_fields
          (Facet.TypeSystem.Program.struct_fields sdef) Σ') as [Σr' [Hfields_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used1 T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_struct_field_snd_lt sname lts args fields e0 Hin)
               as Hfield_lt.
             eapply Nat.lt_le_trans.
             ++ exact Hfield_lt.
             ++ apply Nat.lt_succ_r. exact Hlt.
          -- exact Halpha.
          -- exact Hcu.
          -- exact Hru.
          -- exact Hd.
          -- exact Hr.
          -- exact Ht.
        * exact Hctx.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hfields.
        * exact H3.
        * exists Σr'. split.
          -- eapply TES_Struct; eauto.
          -- exact Hctx_r.
      + destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
          (rename_range ρ)) as [Hdisj1 Hdisj2].
        { intros y Hy. apply Hdisj. simpl. right. exact Hy. }
        destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
        remember (fresh_ident x (x :: free_vars_expr e2 ++ used1)) as xr eqn:Hxr.
        remember (xr :: x :: free_vars_expr e2 ++ used1) as used2 eqn:Hused2.
        destruct (alpha_rename_expr ((x, xr) :: ρ) used2 e2)
          as [e2r used3] eqn:He2.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr e1 e1r used used1 T1 Σ1)
          as [Σr1 [Htyped1_r Hctx1_r]]; try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends.
          - exact He1.
          - apply Hctx_used.
            rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
            + exact Hy.
            + eapply typed_env_structural_same_bindings. exact Htyped1_r. }
        assert (Hrange_used1 : forall y, In y (rename_range ρ) -> In y used1).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
        assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
        { subst xr. intro Hin.
          apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
          right. apply in_or_app. right.
          apply Hctx_used1. exact Hin. }
        assert (Hfresh_range : ~ In xr (rename_range ρ)).
        { subst xr. intro Hin.
          apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
          right. apply in_or_app. right.
          apply Hrange_used1. exact Hin. }
        assert (Hctx_body : ctx_alpha ((x, xr) :: ρ)
          (sctx_add x T m Σ1) (sctx_add xr T m Σr1)).
        { eapply ctx_alpha_add_fresh_forward; eauto. }
        assert (Hctx_used2 : forall y,
          In y (ctx_names (sctx_add xr T m Σr1)) -> In y used2).
        { subst used2. intros y Hy. simpl in Hy.
          destruct Hy as [Hy | Hy]; [left; exact Hy |].
          right. right. apply in_or_app. right.
          apply Hctx_used1. exact Hy. }
        assert (Hrange_used2 : forall y,
          In y (rename_range ((x, xr) :: ρ)) -> In y used2).
        { subst used2. intros y Hy. simpl in Hy.
          destruct Hy as [Hy | Hy].
          - left. exact Hy.
          - right. right. apply in_or_app. right.
            apply Hrange_used1. exact Hy. }
        destruct (IH env Ω n ((x, xr) :: ρ)
          (sctx_add x T m Σ1) (sctx_add xr T m Σr1)
          e2 e2r used2 used3 T2 Σ2) as [Σr2 [Htyped2_r Hctx2_r]].
        * simpl in Hlt. lia.
        * exact Hctx_body.
        * exact Hctx_used2.
        * exact Hrange_used2.
        * eapply alpha_rename_let_body_disjoint_forward; eauto.
        * exact He2.
        * exact Htyped2.
        * exists (sctx_remove xr Σr2). split.
          -- eapply TES_Let.
             ++ exact Htyped1_r.
             ++ exact H.
             ++ exact Htyped2_r.
             ++ assert (Hlookup_xr :
                  lookup_rename x ((x, xr) :: ρ) = xr).
                { simpl. rewrite ident_eqb_refl. reflexivity. }
                rewrite <- Hlookup_xr.
                eapply ctx_alpha_check_ok_forward.
                ** exact Hctx2_r.
                ** eapply alpha_rename_let_bound_safe_forward.
                   --- exact Hxr.
                   --- apply Hdisj. simpl. left. reflexivity.
                ** exact H0.
          -- eapply ctx_alpha_remove_bound. exact Hctx2_r.
      + destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
          (rename_range ρ)) as [Hdisj1 Hdisj2].
        { intros y Hy. apply Hdisj. simpl. right. exact Hy. }
        destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
        remember (fresh_ident x (x :: free_vars_expr e2 ++ used1)) as xr eqn:Hxr.
        remember (xr :: x :: free_vars_expr e2 ++ used1) as used2 eqn:Hused2.
        destruct (alpha_rename_expr ((x, xr) :: ρ) used2 e2)
          as [e2r used3] eqn:He2.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr e1 e1r used used1 T1 Σ1)
          as [Σr1 [Htyped1_r Hctx1_r]]; try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends.
          - exact He1.
          - apply Hctx_used.
            rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
            + exact Hy.
            + eapply typed_env_structural_same_bindings. exact Htyped1_r. }
        assert (Hrange_used1 : forall y, In y (rename_range ρ) -> In y used1).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
        assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
        { subst xr. intro Hin.
          apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
          right. apply in_or_app. right.
          apply Hctx_used1. exact Hin. }
        assert (Hfresh_range : ~ In xr (rename_range ρ)).
        { subst xr. intro Hin.
          apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
          right. apply in_or_app. right.
          apply Hrange_used1. exact Hin. }
        assert (Hctx_body : ctx_alpha ((x, xr) :: ρ)
          (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
        { eapply ctx_alpha_add_fresh_forward; eauto. }
        assert (Hctx_used2 : forall y,
          In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
        { subst used2. intros y Hy. simpl in Hy.
          destruct Hy as [Hy | Hy]; [left; exact Hy |].
          right. right. apply in_or_app. right.
          apply Hctx_used1. exact Hy. }
        assert (Hrange_used2 : forall y,
          In y (rename_range ((x, xr) :: ρ)) -> In y used2).
        { subst used2. intros y Hy. simpl in Hy.
          destruct Hy as [Hy | Hy].
          - left. exact Hy.
          - right. right. apply in_or_app. right.
            apply Hrange_used1. exact Hy. }
        destruct (IH env Ω n ((x, xr) :: ρ)
          (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)
          e2 e2r used2 used3 T2 Σ2) as [Σr2 [Htyped2_r Hctx2_r]].
        * simpl in Hlt. lia.
        * exact Hctx_body.
        * exact Hctx_used2.
        * exact Hrange_used2.
        * eapply alpha_rename_let_body_disjoint_forward; eauto.
        * exact He2.
        * exact Htyped2.
        * exists (sctx_remove xr Σr2). split.
          -- eapply TES_LetInfer.
             ++ exact Htyped1_r.
             ++ exact Htyped2_r.
             ++ assert (Hlookup_xr :
                  lookup_rename x ((x, xr) :: ρ) = xr).
                { simpl. rewrite ident_eqb_refl. reflexivity. }
                rewrite <- Hlookup_xr.
                eapply ctx_alpha_check_ok_forward.
                ** exact Hctx2_r.
                ** eapply alpha_rename_let_bound_safe_forward.
                   --- exact Hxr.
                   --- apply Hdisj. simpl. left. reflexivity.
                ** exact H.
          -- eapply ctx_alpha_remove_bound. exact Hctx2_r.
      + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr e er0 used used0 T Σ')
          as [Σr' [Htyped_r Hctx_r]]; try solve [simpl in Hlt; lia | eauto].
        exists Σr'. split; [eapply TES_Drop; exact Htyped_r | exact Hctx_r].
      + destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
          (rename_range ρ) Hdisj) as [Hdisj_p Hdisj_new].
        destruct (alpha_rename_expr ρ used e_new) as [er_new used_new] eqn:Hnew.
        injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. exact Hdisj_p. }
        destruct (IH env Ω n ρ Σ Σr e_new er_new used used_new T_new Σ1)
          as [Σr1 [Htyped_new_r Hctx_new_r]]; try solve [simpl in Hlt; lia | eauto].
        assert (Hsafe_x : ~ In x (rename_range ρ)).
        { rewrite <- (place_path_root p x path H0). exact Hsafe_p. }
        destruct (ctx_alpha_restore_path_forward
          ρ Σ1 Σr1 x path Σ2 Hctx_new_r Hsafe_x H4)
          as [Σr2 [Hrestore_r Hctx_restore]].
        exists Σr2. split.
        * eapply TES_Replace_Path.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- eapply place_path_rename_place_some. exact H0.
          -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
          -- exact Htyped_new_r.
          -- exact H2.
          -- eapply ctx_alpha_path_available_forward; eauto.
          -- exact Hrestore_r.
        * exact Hctx_restore.
      + destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
          (rename_range ρ) Hdisj) as [Hdisj_p Hdisj_new].
        destruct (alpha_rename_expr ρ used e_new) as [er_new used_new] eqn:Hnew.
        injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. exact Hdisj_p. }
        destruct (IH env Ω n ρ Σ Σr e_new er_new used used_new T_new Σ')
          as [Σr' [Htyped_new_r Hctx_new_r]]; try solve [simpl in Hlt; lia | eauto].
        exists Σr'. split.
        * eapply TES_Replace_Indirect.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- eapply place_path_rename_place_none. exact H0.
          -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
          -- exact Htyped_new_r.
          -- exact H2.
        * exact Hctx_new_r.
      + destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
          (rename_range ρ) Hdisj) as [Hdisj_p Hdisj_new].
        destruct (alpha_rename_expr ρ used e_new) as [er_new used_new] eqn:Hnew.
        injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. exact Hdisj_p. }
        destruct (IH env Ω n ρ Σ Σr e_new er_new used used_new T_new Σ')
          as [Σr' [Htyped_new_r Hctx_new_r]]; try solve [simpl in Hlt; lia | eauto].
        assert (Hsafe_x : ~ In x (rename_range ρ)).
        { rewrite <- (place_path_root p x path H1). exact Hsafe_p. }
        exists Σr'. split.
        * eapply TES_Assign_Path.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- exact H0.
          -- eapply place_path_rename_place_some. exact H1.
          -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
          -- exact Htyped_new_r.
          -- exact H3.
          -- eapply ctx_alpha_path_available_forward; eauto.
        * exact Hctx_new_r.
      + destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
          (rename_range ρ) Hdisj) as [Hdisj_p Hdisj_new].
        destruct (alpha_rename_expr ρ used e_new) as [er_new used_new] eqn:Hnew.
        injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. exact Hdisj_p. }
        destruct (IH env Ω n ρ Σ Σr e_new er_new used used_new T_new Σ')
          as [Σr' [Htyped_new_r Hctx_new_r]]; try solve [simpl in Hlt; lia | eauto].
        exists Σr'. split.
        * eapply TES_Assign_Indirect.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- exact H0.
          -- eapply place_path_rename_place_none. exact H1.
          -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
          -- exact Htyped_new_r.
          -- exact H3.
        * exact Hctx_new_r.
      + injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
        exists Σr. split.
        * eapply TES_BorrowShared.
          eapply alpha_rename_typed_place_env_structural_forward; eauto.
        * exact Hctx.
      + injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
        exists Σr. split.
        * eapply TES_BorrowUnique.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- eapply place_path_rename_place_some. exact H0.
          -- eapply ctx_alpha_lookup_mut_forward.
             ++ exact Hctx.
             ++ rewrite <- (place_path_root p x path H0). exact Hsafe_p.
             ++ exact H1.
        * exact Hctx.
      + injection Hrename as <- <-.
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
        exists Σr. split.
        * eapply TES_BorrowUnique_Indirect.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- eapply place_path_rename_place_none. exact H0.
          -- eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
        * exact Hctx.
      + destruct (alpha_rename_expr ρ used r) as [rr usedr] eqn:Hr.
        injection Hrename as <- <-.
        assert (Hplace_r : expr_as_place rr = Some (rename_place ρ p)).
        { eapply expr_as_place_alpha_rename_some_forward; eauto. }
        assert (Hsafe_p : ~ In (place_root p) (rename_range ρ)).
        { rewrite <- place_name_root.
          apply Hdisj.
          simpl.
          eapply expr_as_place_place_name_in_free_vars. exact H. }
        exists Σr. split.
        * eapply TES_Deref_Place.
          -- exact Hplace_r.
          -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
          -- exact H1.
        * exact Hctx.
      + destruct (alpha_rename_expr ρ used r) as [rr usedr] eqn:Hr.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr r rr used usedr
          (MkTy u (TRef la rk T)) Σ') as [Σr' [Htyped_r Hctx_r]];
          try solve [simpl in Hlt; lia | eauto].
        exists Σr'. split.
        * eapply TES_Deref_Expr.
          -- eapply expr_as_place_alpha_rename_none_forward; eauto.
          -- exact Htyped_r.
          -- exact H0.
        * exact Hctx_r.
      + destruct (disjoint_names_app_l (free_vars_expr e1)
          (free_vars_expr e2 ++ free_vars_expr e3) (rename_range ρ))
          as [Hdisj1 Hdisj23].
        { intros y Hy. apply Hdisj. simpl. exact Hy. }
        destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
          (rename_range ρ) Hdisj23) as [Hdisj2 Hdisj3].
        destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
        destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
        destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr e1 e1r used used1 T_cond Σ1)
          as [Σr1 [Htyped1_r Hctx1_r]]; try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends.
          - exact He1.
          - apply Hctx_used.
            rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
            + exact Hy.
            + eapply typed_env_structural_same_bindings. exact Htyped1_r. }
        assert (Hrange_used1 : forall y, In y (rename_range ρ) -> In y used1).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
        destruct (IH env Ω n ρ Σ1 Σr1 e2 e2r used1 used2 T2 Σ2)
          as [Σr2 [Htyped2_r Hctx2_r]]; try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used2 : forall y, In y (ctx_names Σr1) -> In y used2).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends; [exact He2 |].
          apply Hctx_used1. exact Hy. }
        assert (Hrange_used2 : forall y, In y (rename_range ρ) -> In y used2).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
        destruct (IH env Ω n ρ Σ1 Σr1 e3 e3r used2 used3 T3 Σ3)
          as [Σr3 [Htyped3_r Hctx3_r]]; try solve [simpl in Hlt; lia | eauto].
        destruct (ctx_alpha_merge_forward
          ρ Σ2 Σr2 Σ3 Σr3 Σ4 Hctx2_r Hctx3_r H1)
          as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4. split.
        * eapply TES_If; eauto.
        * exact Hctx_merge.
      + destruct ((fix go (used0 : list ident) (args0 : list expr)
                    : list expr * list ident :=
                    match args0 with
                    | [] => ([], used0)
                    | arg :: rest =>
                        let (arg', used1) := alpha_rename_expr ρ used0 arg in
                        let (rest', used2) := go used1 rest in
                        (arg' :: rest', used2)
                    end) used args) as [argsr used_args] eqn:Hargs.
        injection Hrename as <- <-.
        destruct (alpha_rename_typed_args_env_structural_forward
          env Ω n ρ Σ Σr args argsr used used_args
          (apply_lt_params σ (fn_params fdef))
          (apply_lt_params σ (fn_params fdef)) Σ') as [Σr' [Hargs_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used1 T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_call_arg_lt fname args e0 Hin) as Harg_lt.
             eapply Nat.lt_le_trans.
             ++ exact Harg_lt.
             ++ apply Nat.lt_succ_r. exact Hlt.
          -- exact Halpha.
          -- exact Hcu.
          -- exact Hru.
          -- exact Hd.
          -- exact Hr.
          -- exact Ht.
        * exact Hctx.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * apply params_alpha_refl.
        * exact Hargs.
        * exact H1.
        * exists Σr'. split; [econstructor; eauto | exact Hctx_r].
      + destruct (disjoint_names_app_l (free_vars_expr callee)
          ((fix go (args0 : list expr) : list ident :=
              match args0 with
              | [] => []
              | arg :: rest => free_vars_expr arg ++ go rest
              end) args) (rename_range ρ) Hdisj) as [Hdisj_callee Hdisj_args].
        destruct (alpha_rename_expr ρ used callee) as [calleer used1] eqn:Hcallee.
        destruct ((fix go (used0 : list ident) (args0 : list expr)
                    : list expr * list ident :=
                    match args0 with
                    | [] => ([], used0)
                    | arg :: rest =>
                        let (arg', used2) := alpha_rename_expr ρ used0 arg in
                        let (rest', used3) := go used2 rest in
                        (arg' :: rest', used3)
                    end) used1 args) as [argsr used_args] eqn:Hargs.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr callee calleer used used1
          (MkTy u (TFn param_tys ret)) Σ1) as [Σr1 [Hcallee_r Hctx1_r]];
          try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends.
          - exact Hcallee.
          - apply Hctx_used.
            rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
            + exact Hy.
            + eapply typed_env_structural_same_bindings. exact Hcallee_r. }
        assert (Hrange_used1 : forall y, In y (rename_range ρ) -> In y used1).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
        destruct (alpha_rename_typed_args_env_structural_forward
          env Ω n ρ Σ1 Σr1 args argsr used1 used_args
          (params_of_tys param_tys) (params_of_tys param_tys) Σ')
          as [Σr' [Hargs_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used_tail T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_callexpr_arg_lt callee args e0 Hin) as Harg_lt.
             eapply Nat.lt_le_trans.
             ++ exact Harg_lt.
             ++ apply Nat.lt_succ_r. exact Hlt.
          -- exact Halpha.
          -- exact Hcu.
          -- exact Hru.
          -- exact Hd.
          -- exact Hr.
          -- exact Ht.
        * exact Hctx1_r.
        * exact Hctx_used1.
        * exact Hrange_used1.
        * exact Hdisj_args.
        * apply params_alpha_refl.
        * exact Hargs.
        * assumption.
        * exists Σr'. split; [eapply TES_CallExpr_Fn; eauto | exact Hctx_r].
      + destruct (disjoint_names_app_l (free_vars_expr callee)
          ((fix go (args0 : list expr) : list ident :=
              match args0 with
              | [] => []
              | arg :: rest => free_vars_expr arg ++ go rest
              end) args) (rename_range ρ) Hdisj) as [Hdisj_callee Hdisj_args].
        destruct (alpha_rename_expr ρ used callee) as [calleer used1] eqn:Hcallee.
        destruct ((fix go (used0 : list ident) (args0 : list expr)
                    : list expr * list ident :=
                    match args0 with
                    | [] => ([], used0)
                    | arg :: rest =>
                        let (arg', used2) := alpha_rename_expr ρ used0 arg in
                        let (rest', used3) := go used2 rest in
                        (arg' :: rest', used3)
                    end) used1 args) as [argsr used_args] eqn:Hargs.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr callee calleer used used1
          (MkTy u (TForall m bounds body)) Σ1) as [Σr1 [Hcallee_r Hctx1_r]];
          try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends.
          - exact Hcallee.
          - apply Hctx_used.
            rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
            + exact Hy.
            + eapply typed_env_structural_same_bindings. exact Hcallee_r. }
        assert (Hrange_used1 : forall y, In y (rename_range ρ) -> In y used1).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
        destruct (alpha_rename_typed_args_env_structural_forward
          env Ω n ρ Σ1 Σr1 args argsr used1 used_args
          (params_of_tys (map (open_bound_ty σ) param_tys))
          (params_of_tys (map (open_bound_ty σ) param_tys)) Σ')
          as [Σr' [Hargs_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used_tail T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_callexpr_arg_lt callee args e0 Hin) as Harg_lt.
             eapply Nat.lt_le_trans.
             ++ exact Harg_lt.
             ++ apply Nat.lt_succ_r. exact Hlt.
          -- exact Halpha.
          -- exact Hcu.
          -- exact Hru.
          -- exact Hd.
          -- exact Hr.
          -- exact Ht.
        * exact Hctx1_r.
        * exact Hctx_used1.
        * exact Hrange_used1.
        * exact Hdisj_args.
        * apply params_alpha_refl.
        * exact Hargs.
        * assumption.
        * exists Σr'. split; [eapply TES_CallExpr_Forall; eauto | exact Hctx_r].
  }
  intros env Ω n ρ Σ Σr e er used used' T Σ'
    Hctx Hctx_used Hrange_used Hdisj Hrename Htyped.
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
  destruct f as [fname lifetimes outs ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  injection Hrename as <- <-.
  unfold typed_fn_env_structural in *. simpl in *.
  destruct Htyped as [T_body [Γ_out [Htyped_body [Hcompat Hparams]]]].
  destruct (alpha_rename_typed_env_structural_forward
    env outs lifetimes ρ
    (sctx_of_ctx (params_ctx ps)) (sctx_of_ctx (params_ctx psr))
    body bodyr used1 used2 T_body (sctx_of_ctx Γ_out))
    as [Σr_out [Htyped_body_r Hctx_out_r]].
  - eapply alpha_rename_params_ctx_alpha_nil. exact Hps.
  - intros x Hin.
    eapply alpha_rename_params_names_in_used.
    + exact Hps.
    + exact Hin.
  - intros x Hin.
    eapply alpha_rename_params_range_in_used_nil.
    + exact Hps.
    + exact Hin.
  - intros x Hfree Hrange.
    eapply alpha_rename_params_range_fresh_used_nil.
    + exact Hps.
    + exact Hrange.
    + apply in_or_app. right. apply in_or_app. left. exact Hfree.
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
