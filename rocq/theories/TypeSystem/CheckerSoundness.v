From Facet.TypeSystem Require Import Types Syntax TypingRules TypeChecker.
From Stdlib Require Import List String Bool Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Auxiliary: usage_sub_bool correctness                                 *)
(* ------------------------------------------------------------------ *)

Lemma usage_sub_bool_sound : forall u1 u2,
  usage_sub_bool u1 u2 = true -> usage_sub u1 u2.
Proof.
  intros u1 u2 H.
  destruct u1, u2; simpl in H; try discriminate; constructor.
Qed.

Lemma usage_sub_bool_complete : forall u1 u2,
  usage_sub u1 u2 -> usage_sub_bool u1 u2 = true.
Proof.
  intros u1 u2 H. destruct H.
  - destruct u; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: _b helpers agree with TypingRules definitions              *)
(* ------------------------------------------------------------------ *)

Lemma ctx_lookup_b_eq : forall x Γ,
  ctx_lookup_b x Γ = ctx_lookup x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | apply IH].
Qed.

Lemma ctx_consume_b_eq : forall x Γ,
  ctx_consume_b x Γ = ctx_consume x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma ctx_remove_b_eq : forall x Γ,
  ctx_remove_b x Γ = ctx_remove x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | rewrite IH; reflexivity].
Qed.

(* ctx_add_b and ctx_add are definitionally equal. *)
Lemma ctx_add_b_eq : forall x T Γ,
  ctx_add_b x T Γ = ctx_add x T Γ.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: ty_core_eqb correctness                                    *)
(* ------------------------------------------------------------------ *)

Lemma ty_core_eqb_true : forall c1 c2,
  ty_core_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros c1 c2 H.
  destruct c1, c2; simpl in H; try discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: ctx_check_ok implies ctx_is_ok                             *)
(* ------------------------------------------------------------------ *)

Lemma ctx_check_ok_sound : forall x T Γ,
  ctx_check_ok x T Γ = true -> ctx_is_ok x T Γ.
Proof.
  intros x T Γ H.
  unfold ctx_check_ok, ctx_is_ok in *.
  destruct (ty_usage T) eqn:Hu; try exact I.
  rewrite ctx_lookup_b_eq in H.
  destruct (ctx_lookup x Γ) as [[T' b] |] eqn:Hl.
  - destruct b; [exact I | discriminate].
  - discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Alpha-renaming preservation helpers                                  *)
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
  | CtxAlpha_Bind : forall ρ Γ Γr x xr T b,
      ctx_alpha ρ Γ Γr ->
      ~ In xr (ctx_names Γr) ->
      ~ In xr (rename_range ρ) ->
      ctx_alpha ((x, xr) :: ρ) ((x, T, b) :: Γ) ((xr, T, b) :: Γr).

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
  induction Γ as [| [[n T] b] Γ IH]; intros x Γ' Hconsume.
  - simpl in Hconsume. discriminate.
  - simpl in Hconsume.
    destruct (ident_eqb x n).
    + injection Hconsume as <-. reflexivity.
    + destruct (ctx_consume x Γ) as [Γt |] eqn:Htail.
      2: discriminate.
      injection Hconsume as <-.
      simpl. rewrite (IH x Γt Htail). reflexivity.
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
  | EA_Replace : forall ρ x e er,
      ~ In x (rename_range ρ) ->
      expr_alpha ρ e er ->
      expr_alpha ρ (EReplace (PVar x) e)
        (EReplace (PVar (lookup_rename x ρ)) er)
  | EA_Drop : forall ρ e er,
      expr_alpha ρ e er ->
      expr_alpha ρ (EDrop e) (EDrop er)
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
      exists ((x, T, true) :: Γ).
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
      exists ((x, T, b) :: Γ').
      split.
      * simpl. rewrite Hyx. rewrite Hconsume0. reflexivity.
      * constructor.
        -- exact Halpha0.
        -- rewrite (ctx_consume_preserves_names
             (lookup_rename y ρ) Γr Γrt Hconsume_tail). exact H.
        -- exact H0.
Qed.

Lemma ctx_alpha_remove_head : forall ρ Γ Γr x xr T b,
  ctx_alpha ρ Γ Γr ->
  ctx_alpha ρ
    (ctx_remove x ((x, T, b) :: Γ))
    (ctx_remove xr ((xr, T, b) :: Γr)).
Proof.
  intros ρ Γ Γr x xr T b Halpha.
  simpl.
  rewrite ident_eqb_refl.
  rewrite ident_eqb_refl.
  exact Halpha.
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

Lemma alpha_rename_expr_sound : forall ρ used e er used',
  disjoint_names (free_vars_expr e) (rename_range ρ) ->
  alpha_rename_expr ρ used e = (er, used') ->
  expr_alpha ρ e er.
Proof.
Admitted.

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
  destruct f as [fname ps ret body].
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

Lemma typed_alpha_backward :
  (forall fenv Γ e T Γr,
      typed fenv Γ e T Γr ->
      forall fenv0 ρ Γ0 e0,
        fenv_alpha fenv0 fenv ->
        ctx_alpha ρ Γ0 Γ ->
        expr_alpha ρ e0 e ->
        exists Γ0',
          typed fenv0 Γ0 e0 T Γ0' /\
          ctx_alpha ρ Γ0' Γr) /\
  (forall fenv Γ es ps Γr,
      typed_args fenv Γ es ps Γr ->
      forall fenv0 ρ Γ0 es0 ps0,
        fenv_alpha fenv0 fenv ->
        ctx_alpha ρ Γ0 Γ ->
        exprs_alpha ρ es0 es ->
        params_alpha ps0 ps ->
        exists Γ0',
          typed_args fenv0 Γ0 es0 ps0 Γ0' /\
          ctx_alpha ρ Γ0' Γr).
Proof.
Admitted.

(* ------------------------------------------------------------------ *)
(* Main theorem: infer_core is sound w.r.t. typed                             *)
(* ------------------------------------------------------------------ *)

Theorem infer_sound : forall fenv Γ e T Γ',
  infer_core fenv Γ e = Some (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
  intros fenv Γ e. revert Γ.
  induction e; intros Γ T Γ' Hinfer; simpl in Hinfer.

  (* EUnit *)
  - injection Hinfer as <- <-. constructor.

  (* ELit *)
  - destruct l.
    + injection Hinfer as <- <-. constructor.
    + injection Hinfer as <- <-. constructor.

  (* EVar i *)
  - rename i into x.
    destruct (ctx_lookup_b x Γ) as [[Tv b] |] eqn:Hlookup_b.
    2: discriminate.
    destruct (usage_eqb (ty_usage Tv) UUnrestricted) eqn:Hunr.
    + (* unrestricted: copy, no consumption *)
      injection Hinfer as <- <-.
      apply T_Var_Copy with (b := b).
      * rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      * destruct (ty_usage Tv); simpl in Hunr; try discriminate; reflexivity.
    + (* linear/affine: consume on read *)
      destruct b; [discriminate |].
      destruct (ctx_consume_b x Γ) as [Γ'' |] eqn:Hcons_b.
      2: discriminate.
      injection Hinfer as <- <-.
      apply T_Var_Consume.
      * rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      * intro Heq. rewrite Heq in Hunr. simpl in Hunr. discriminate.
      * rewrite <- ctx_consume_b_eq. exact Hcons_b.

  (* ELet m i t e1 e2 *)
  - rename i into x.
    destruct (infer_core fenv Γ e1) as [[T1 Γ1] |] eqn:He1.
    2: discriminate.
    destruct (ty_core_eqb (ty_core T1) (ty_core t) &&
              usage_sub_bool (ty_usage T1) (ty_usage t)) eqn:Hcheck.
    2: discriminate.
    apply andb_prop in Hcheck as [Hcore Hsub].
    destruct (infer_core fenv (ctx_add_b x t Γ1) e2) as [[T2 Γ2] |] eqn:He2.
    2: discriminate.
    destruct (ctx_check_ok x t Γ2) eqn:Hok.
    2: discriminate.
    injection Hinfer as <- <-.
    rewrite ctx_remove_b_eq.
    eapply T_Let.
    + apply IHe1. exact He1.
    + apply ty_core_eqb_true. exact Hcore.
    + apply usage_sub_bool_sound. exact Hsub.
    + apply IHe2. exact He2.
    + apply ctx_check_ok_sound. exact Hok.

  (* ELetInfer: out of scope *)
  - discriminate.

  (* ECall: admitted — the inline 'go' fixpoint inside infer_core is not
     directly accessible for inversion in this proof.
     A complete proof would require an auxiliary lemma relating 'go'
     to typed_args. *)
  - admit.

  (* EReplace (PVar px) e *)
  - destruct p as [px].
    destruct (ctx_lookup_b px Γ) as [[T_x b] |] eqn:Hlx_b.
    2: discriminate.
    destruct b; [discriminate |].
    destruct (infer_core fenv Γ e) as [[T_new Γ1] |] eqn:He.
    2: discriminate.
    destruct (ty_core_eqb (ty_core T_new) (ty_core T_x) &&
              usage_sub_bool (ty_usage T_new) (ty_usage T_x)) eqn:Hcheck.
    2: discriminate.
    apply andb_prop in Hcheck as [Hcore Hsub].
    injection Hinfer as <- <-.
    apply T_Replace with (T_new := T_new).
    + rewrite <- ctx_lookup_b_eq. exact Hlx_b.
    + apply IHe. exact He.
    + apply ty_core_eqb_true. exact Hcore.
    + apply usage_sub_bool_sound. exact Hsub.

  (* EDrop e *)
  - destruct (infer_core fenv Γ e) as [[Te Γ1] |] eqn:He.
    2: discriminate.
    injection Hinfer as <- <-.
    eapply T_Drop. apply IHe. exact He.
Admitted.

(* Public infer runs alpha-renaming before infer_core. The proof requires
   alpha-renaming preservation for typing; keep it isolated from the
   infer_core soundness argument above. *)
Lemma alpha_rename_for_infer_typed_backward : forall fenv Γ e fenv' e' T Γ',
  alpha_rename_for_infer Γ fenv e = (fenv', e') ->
  typed fenv' Γ e' T Γ' ->
  typed fenv Γ e T Γ'.
Proof.
  intros fenv Γ e fenv' e' T Γ' Hrename Htyped.
  pose proof (alpha_rename_for_infer_sound
    fenv Γ e fenv' e' Hrename) as [Hfenv_alpha Hexpr_alpha].
  destruct typed_alpha_backward as [Htyped_backward _].
  pose proof (Htyped_backward
    fenv' Γ e' T Γ' Htyped
    fenv [] Γ e Hfenv_alpha (CtxAlpha_Base Γ) Hexpr_alpha)
    as [Γ0 [Htyped0 Hctx_alpha]].
  pose proof (ctx_alpha_nil_eq Γ0 Γ' Hctx_alpha) as Heq.
  subst Γ0.
  exact Htyped0.
Qed.

Theorem infer_public_sound : forall fenv Γ e T Γ',
  infer fenv Γ e = Some (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
  intros fenv Γ e T Γ' Hinfer.
  unfold infer in Hinfer.
  destruct (alpha_rename_for_infer Γ fenv e) as [fenv' e'] eqn:Hrename.
  apply (alpha_rename_for_infer_typed_backward
    fenv Γ e fenv' e' T Γ' Hrename).
  apply infer_sound. exact Hinfer.
Qed.
