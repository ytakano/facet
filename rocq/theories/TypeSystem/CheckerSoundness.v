From Facet.TypeSystem Require Import Types Syntax TypingRules TypeChecker.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

Scheme typed_ind' := Induction for typed Sort Prop
with typed_args_ind' := Induction for typed_args Sort Prop.
Combined Scheme typed_typed_args_ind from typed_ind', typed_args_ind'.

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

Lemma lookup_fn_b_sound : forall fname fenv fdef,
  lookup_fn_b fname fenv = Some fdef ->
  In fdef fenv /\ fn_name fdef = fname.
Proof.
  intros fname fenv.
  induction fenv as [| f fs IH]; intros fdef Hlookup.
  - discriminate.
  - simpl in Hlookup.
    destruct (ident_eqb fname (fn_name f)) eqn:Hname.
    + injection Hlookup as <-.
      apply ident_eqb_eq in Hname.
      split; [left; reflexivity | symmetry; exact Hname].
    + destruct (IH fdef Hlookup) as [Hin Hfn].
      split; [right; exact Hin | exact Hfn].
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

Lemma ctx_alpha_remove_bound : forall ρ Γ Γr x xr,
  ctx_alpha ((x, xr) :: ρ) Γ Γr ->
  ctx_alpha ρ (ctx_remove x Γ) (ctx_remove xr Γr).
Proof.
  intros ρ Γ Γr x xr Halpha.
  inversion Halpha; subst.
  simpl. rewrite ident_eqb_refl. rewrite ident_eqb_refl.
  assumption.
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
  | CtxSame_Cons : forall x T b b' Γ Γ',
      ctx_same_bindings Γ Γ' ->
      ctx_same_bindings ((x, T, b) :: Γ) ((x, T, b') :: Γ').

Lemma ctx_same_bindings_refl : forall Γ,
  ctx_same_bindings Γ Γ.
Proof.
  induction Γ as [| [[x T] b] Γ IH].
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
  induction H12 as [| x T b b' Γ Γ' H12 IH]; intros Γ3 H23.
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
  induction Γ as [| [[n T] b] Γ IH]; intros x Γ' Hconsume.
  - discriminate.
  - simpl in Hconsume.
    destruct (ident_eqb x n).
    + injection Hconsume as <-. constructor. apply ctx_same_bindings_refl.
    + destruct (ctx_consume x Γ) as [Γt |] eqn:Htail.
      2: discriminate.
      injection Hconsume as <-.
      constructor. eapply IH. exact Htail.
Qed.

Lemma ctx_remove_same_bindings_head : forall x T b b' Γ Γ',
  ctx_same_bindings Γ Γ' ->
  ctx_remove x ((x, T, b) :: Γ) = Γ ->
  ctx_remove x ((x, T, b') :: Γ') = Γ'.
Proof.
  intros x T b b' Γ Γ' _ _.
  simpl. rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma ctx_same_bindings_remove_head : forall x T b Γ Γ',
  ctx_same_bindings ((x, T, b) :: Γ) Γ' ->
  ctx_same_bindings Γ (ctx_remove x Γ').
Proof.
  intros x T b Γ Γ' Hsame.
  inversion Hsame; subst.
  simpl. rewrite ident_eqb_refl. assumption.
Qed.

Lemma typed_same_bindings :
  (forall fenv Γ e T Γ',
      typed fenv Γ e T Γ' ->
      ctx_same_bindings Γ Γ') /\
  (forall fenv Γ es ps Γ',
      typed_args fenv Γ es ps Γ' ->
      ctx_same_bindings Γ Γ').
Proof.
  assert (H : forall fenv,
    (forall Γ e T Γ',
        typed fenv Γ e T Γ' -> ctx_same_bindings Γ Γ') /\
    (forall Γ es ps Γ',
        typed_args fenv Γ es ps Γ' -> ctx_same_bindings Γ Γ')).
  {
    intro fenv.
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
          Hbody : ctx_same_bindings (ctx_add ?x ?T ?Γ1) ?Γ2
          |- ctx_same_bindings ?Γ (ctx_remove ?x ?Γ2) =>
            eapply ctx_same_bindings_trans;
            [ exact Hhead
            | eapply ctx_same_bindings_remove_head; exact Hbody ]
        end
      ];
      try solve [eapply ctx_same_bindings_trans; eassumption].
  }
  split; intros fenv; destruct (H fenv) as [Ht Hargs]; [apply Ht | apply Hargs].
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
  | EDrop e => S (expr_size e)
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
  destruct f as [fname ps ret body].
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
  + destruct p as [px].
    destruct (disjoint_names_cons_l px (free_vars_expr e)
      (rename_range ρ) Hdisj) as [Hpx Hdisj_e].
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    constructor.
    * exact Hpx.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact Hdisj_e.
      -- exact He.
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    constructor.
    eapply IH.
    * simpl in Hlt. lia.
    * exact Hdisj.
    * exact He.
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

Lemma typed_args_cons_inv : forall fenv Γ er ers pr psr Γ',
  typed_args fenv Γ (er :: ers) (pr :: psr) Γ' ->
  exists T Γ1,
    typed fenv Γ er T Γ1 /\
    ty_core T = ty_core (param_ty pr) /\
    usage_sub (ty_usage T) (ty_usage (param_ty pr)) /\
    typed_args fenv Γ1 ers psr Γ'.
Proof.
  intros fenv Γ er ers pr psr Γ' Htyped.
  inversion Htyped; subst.
  exists T_e, Γ1. repeat split; assumption.
Qed.

Lemma typed_call_inv : forall fenv Γ fname args T Γ',
  typed fenv Γ (ECall fname args) T Γ' ->
  exists fdef,
    In fdef fenv /\
    fn_name fdef = fname /\
    fn_ret fdef = T /\
    typed_args fenv Γ args (fn_params fdef) Γ'.
Proof.
  intros fenv Γ fname args T Γ' Htyped.
  inversion Htyped; subst.
  exists fdef. repeat split; assumption.
Qed.

Lemma alpha_rename_call_args_typed_backward : forall fenv0 fenvr ρ Γ0 Γr args argsr used used' ps0 psr Γr',
  (forall Γa Γb used0 e er used1 T Γb',
      In e args ->
      ctx_alpha ρ Γa Γb ->
      (forall x, In x (ctx_names Γb) -> In x used0) ->
      (forall x, In x (rename_range ρ) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      typed fenvr Γb er T Γb' ->
      exists Γa',
        typed fenv0 Γa e T Γa' /\
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
  typed_args fenvr Γr argsr psr Γr' ->
  exists Γ0',
    typed_args fenv0 Γ0 args ps0 Γ0' /\
    ctx_alpha ρ Γ0' Γr'.
Proof.
  intros fenv0 fenvr ρ Γ0 Γr args.
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
    destruct (typed_args_cons_inv fenvr Γr ar restr pr psr_tail Γr' Htyped_args)
      as [Targ [Γr1 [Htyped_arg_r [Hcore [Hsub Htyped_tail_r]]]]].
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
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite HT. exact Hcore.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite HT. exact Hsub.
           ++ exact Htyped_tail.
        -- exact Hctx_tail.
Qed.

Lemma alpha_rename_typed_backward : forall fenv0 fenvr ρ Γ0 Γr e er used used' T Γr',
  fenv_alpha fenv0 fenvr ->
  ctx_alpha ρ Γ0 Γr ->
  (forall x, In x (ctx_names Γr) -> In x used) ->
  (forall x, In x (rename_range ρ) -> In x used) ->
  disjoint_names (free_vars_expr e) (rename_range ρ) ->
  alpha_rename_expr ρ used e = (er, used') ->
  typed fenvr Γr er T Γr' ->
  exists Γ0',
    typed fenv0 Γ0 e T Γ0' /\
    ctx_alpha ρ Γ0' Γr'.
Proof.
  assert (Hsize : forall n fenv0 fenvr ρ Γ0 Γr e er used used' T Γr',
    expr_size e < n ->
    fenv_alpha fenv0 fenvr ->
    ctx_alpha ρ Γ0 Γr ->
    (forall x, In x (ctx_names Γr) -> In x used) ->
    (forall x, In x (rename_range ρ) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range ρ) ->
    alpha_rename_expr ρ used e = (er, used') ->
    typed fenvr Γr er T Γr' ->
    exists Γ0',
      typed fenv0 Γ0 e T Γ0' /\
      ctx_alpha ρ Γ0' Γr').
  {
  induction n as [| n IH]; intros fenv0 fenvr ρ Γ0 Γr e er used used' T Γr'
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
    | Hte1 : typed fenvr Γr e1r ?T1r ?Γ1r |- _ =>
      destruct (IH fenv0 fenvr ρ Γ0 Γr e1 e1r used used1 T1r Γ1r
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
          | Hte1 : typed fenvr Γr e1r _ _ |- _ => eapply Hsame; exact Hte1
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
        (ctx_add i t Γ01) (ctx_add xr t Γ1)).
    { constructor; exact Hctx1 || exact Hxr_ctx || exact Hxr_range. }
    assert (Hctx_ext_used :
      forall x, In x (ctx_names (ctx_add xr t Γ1)) ->
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
    | Hte2 : typed fenvr (ctx_add ?xrr t Γ1) e2r ?T2r ?Γ2r |- _ =>
      destruct (IH fenv0 fenvr ((i, xr) :: ρ)
        (ctx_add i t Γ01) (ctx_add xrr t Γ1)
        e2 e2r (xr :: i :: free_vars_expr e2 ++ used1) used2 T2r Γ2r
        ltac:(simpl in Hlt; lia)
        Hfenv Hctx_ext Hctx_ext_used Hrange_ext_used Hdisj2_ext He2 Hte2)
        as [Γ02 [Htyped2 Hctx2]]
    end.
	    exists (ctx_remove i Γ02). split.
	    { eapply T_Let.
	      - exact Htyped1.
	      - assumption.
	      - assumption.
	      - exact Htyped2.
	      - eapply ctx_alpha_is_ok_backward.
	        + exact Hctx2.
	        + simpl. intros [Heq | Hinr].
	          * apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
	            fold xr. rewrite Heq. left. reflexivity.
	          * apply (Hdisj i); simpl; [left; reflexivity | exact Hinr].
	        + simpl. rewrite ident_eqb_refl. exact H11. }
	    { eapply ctx_alpha_remove_bound. exact Hctx2. }
  + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
       i :: free_vars_expr e2 ++ used1) e2)
      as [e2r used2] eqn:He2.
    injection Hrename as <- _.
    inversion Htyped.
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
    | Htyped_call : typed fenvr Γr (ECall ?fname argsr) T Γr' |- _ =>
      destruct (typed_call_inv fenvr Γr fname argsr T Γr' Htyped_call)
        as [fdef [Hinr [Hname_r [Hret_r Hargs_typed]]]];
      destruct (fenv_alpha_in_backward fenv0 fenvr fdef Hfenv Hinr)
        as [fdef0 [Hin0 Hshape]];
      destruct Hshape as [Hname [Hret Hparams]]
    end.
    assert (Hargs_back :
      exists Γ0',
        typed_args fenv0 Γ0 l (fn_params fdef0) Γ0' /\
        ctx_alpha ρ Γ0' Γr').
    { eapply alpha_rename_call_args_typed_backward.
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
      - exact Hparams.
      - symmetry. exact Hargs.
      - lazymatch goal with
        | Hargs_typed : typed_args fenvr Γr argsr _ Γr' |- _ => exact Hargs_typed
        end. }
    destruct Hargs_back as [Γ0' [Htyped_args0 Hctx0]].
    exists Γ0'. split.
    * rewrite <- Hret_r. rewrite <- Hret.
      eapply T_Call.
      -- exact Hin0.
      -- rewrite Hname. exact Hname_r.
      -- exact Htyped_args0.
    * exact Hctx0.
  + destruct p as [px].
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    inversion Htyped; subst.
    assert (Hsafe : ~ In px (rename_range ρ)).
    { intros Hin. apply (Hdisj px); simpl; [left; reflexivity | exact Hin]. }
    assert (Hdisj_e : disjoint_names (free_vars_expr e) (rename_range ρ)).
    { intros x Hin Hinr. exact (Hdisj x (or_intror Hin) Hinr). }
    lazymatch goal with
    | Hte : typed fenvr Γr er0 ?Tnew ?Γr1 |- _ =>
      destruct (IH fenv0 fenvr ρ Γ0 Γr e er0 used used0 Tnew Γr1
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
      - exact Htyped0.
      - assumption.
      - assumption. }
    { exact Hctx0. }
  + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    inversion Htyped; subst.
    destruct (IH fenv0 fenvr ρ Γ0 Γr e er0 used used0 T0 Γr'
      ltac:(simpl in Hlt; lia)
      Hfenv Hctx Hctx_used Hrange_used Hdisj He H1)
      as [Γ0' [Htyped0 Hctx0]].
    exists Γ0'. split; [eapply T_Drop; exact Htyped0 | exact Hctx0].
  }
  intros fenv0 fenvr ρ Γ0 Γr e er used used' T Γr'
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

Lemma infer_call_args_sound : forall fenv Γ args params Γ',
  (forall Γ0 e T Γ1,
      In e args ->
      infer_core fenv Γ0 e = Some (T, Γ1) ->
      typed fenv Γ0 e T Γ1) ->
  ((fix go (Γ0 : ctx) (as_ : list expr) (ps : list param)
      : option ctx :=
      match as_, ps with
      | [], [] => Some Γ0
      | [], _ :: _ => None
      | _ :: _, [] => None
      | e' :: es, p :: ps' =>
          match infer_core fenv Γ0 e' with
          | None => None
          | Some (T_e, Γ1) =>
              if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) &&
                 usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
              then go Γ1 es ps'
              else None
          end
      end) Γ args params) = Some Γ' ->
  typed_args fenv Γ args params Γ'.
Proof.
  intros fenv Γ args.
  revert Γ.
  induction args as [| e es IH]; intros Γ params Γ' Hexpr Hgo;
    destruct params as [| p ps]; simpl in Hgo; try discriminate.
  - injection Hgo as <-. constructor.
  - destruct (infer_core fenv Γ e) as [[T_e Γ1] |] eqn:He;
      try discriminate.
    destruct (ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) &&
              usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p)))
      eqn:Hcheck; try discriminate.
    apply andb_prop in Hcheck as [Hcore Hsub].
    eapply TArgs_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + apply ty_core_eqb_true. exact Hcore.
    + apply usage_sub_bool_sound. exact Hsub.
    + eapply IH.
      * intros Γ0 e0 T0 Γ0' Hin Hinfer0.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Hinfer0.
      * exact Hgo.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem: infer_core is sound w.r.t. typed                             *)
(* ------------------------------------------------------------------ *)

Theorem infer_sound : forall fenv Γ e T Γ',
  infer_core fenv Γ e = Some (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
  assert (Hsize : forall n fenv Γ e T Γ',
    expr_size e < n ->
    infer_core fenv Γ e = Some (T, Γ') ->
    typed fenv Γ e T Γ').
  {
  induction n as [| n IH]; intros fenv Γ e T Γ' Hlt Hinfer.
  - lia.
  - destruct e; simpl in Hinfer.

  (* EUnit *)
  + injection Hinfer as <- <-. constructor.

  (* ELit *)
  + destruct l.
    * injection Hinfer as <- <-. constructor.
    * injection Hinfer as <- <-. constructor.

  (* EVar i *)
  + rename i into x.
    destruct (ctx_lookup_b x Γ) as [[Tv b] |] eqn:Hlookup_b.
    2: discriminate.
    destruct (usage_eqb (ty_usage Tv) UUnrestricted) eqn:Hunr.
    * (* unrestricted: copy, no consumption *)
      injection Hinfer as <- <-.
      apply T_Var_Copy with (b := b).
      -- rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      -- destruct (ty_usage Tv); simpl in Hunr; try discriminate; reflexivity.
    * (* linear/affine: consume on read *)
      destruct b; [discriminate |].
      destruct (ctx_consume_b x Γ) as [Γ'' |] eqn:Hcons_b.
      2: discriminate.
      injection Hinfer as <- <-.
      apply T_Var_Consume.
      -- rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      -- intro Heq. rewrite Heq in Hunr. simpl in Hunr. discriminate.
      -- rewrite <- ctx_consume_b_eq. exact Hcons_b.

  (* ELet m i t e1 e2 *)
  + rename i into x.
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
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He1.
    * apply ty_core_eqb_true. exact Hcore.
    * apply usage_sub_bool_sound. exact Hsub.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He2.
    * apply ctx_check_ok_sound. exact Hok.

  (* ELetInfer: out of scope *)
  + discriminate.

  (* ECall *)
  + destruct (lookup_fn_b i fenv) as [fdef |] eqn:Hlookup.
    2: discriminate.
    remember
      ((fix go (Γ0 : ctx) (as_ : list expr) (ps : list param)
          : option ctx :=
          match as_, ps with
          | [], [] => Some Γ0
          | [], _ :: _ => None
          | _ :: _, [] => None
          | e' :: es, p :: ps' =>
              match infer_core fenv Γ0 e' with
              | None => None
              | Some (T_e, Γ1) =>
                  if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) &&
                     usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
                  then go Γ1 es ps'
                  else None
              end
          end) Γ l (fn_params fdef)) as r eqn:Hgo.
    destruct r as [Γcall |]; try discriminate.
    injection Hinfer as <- <-.
    destruct (lookup_fn_b_sound i fenv fdef Hlookup) as [Hin Hname].
    eapply T_Call.
    * exact Hin.
    * exact Hname.
    * eapply infer_call_args_sound.
      -- intros Γ0 e0 T0 Γ0' Hin_arg Hinfer0.
         eapply IH.
         ++ pose proof (expr_size_call_arg_lt i l e0 Hin_arg) as Harg_lt.
            assert (expr_size e0 < n) as Hlt_arg by lia.
            exact Hlt_arg.
         ++ exact Hinfer0.
      -- symmetry. exact Hgo.

  (* EReplace (PVar px) e *)
  + destruct p as [px].
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
    * rewrite <- ctx_lookup_b_eq. exact Hlx_b.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He.
    * apply ty_core_eqb_true. exact Hcore.
    * apply usage_sub_bool_sound. exact Hsub.

  (* EDrop e *)
  + destruct (infer_core fenv Γ e) as [[Te Γ1] |] eqn:He.
    2: discriminate.
    injection Hinfer as <- <-.
    eapply T_Drop.
    eapply IH.
    * simpl in Hlt. lia.
    * exact He.
  }
  intros fenv Γ e T Γ' Hinfer.
  eapply (Hsize (S (expr_size e))).
  - lia.
  - exact Hinfer.
Qed.

(* Public infer runs alpha-renaming before infer_core. The proof requires
   alpha-renaming preservation for typing; keep it isolated from the
   infer_core soundness argument above. *)
Lemma alpha_rename_for_infer_typed_backward : forall fenv Γ e fenv' e' T Γ',
  alpha_rename_for_infer Γ fenv e = (fenv', e') ->
  typed fenv' Γ e' T Γ' ->
  typed fenv Γ e T Γ'.
Proof.
  intros fenv Γ e fenv' e' T Γ' Hrename Htyped.
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
    fenv fenv0 [] Γ Γ e er used used' T Γ'
    Hfenv_alpha (CtxAlpha_Base Γ)
    Hctx_used Hrange_used Hdisj He Htyped)
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
