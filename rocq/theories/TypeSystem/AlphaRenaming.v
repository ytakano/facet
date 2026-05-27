From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
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

Lemma alpha_rename_idents_used_extends :
  forall ρ used xs xsr ρ' used',
    alpha_rename_idents ρ used xs = (xsr, ρ', used') ->
    forall x, In x used -> In x used'.
Proof.
  intros ρ used xs.
  revert ρ used.
  induction xs as [| x xs IH]; intros ρ used xsr ρ' used' Hrename y Hin;
    simpl in Hrename.
  - injection Hrename as _ _ <-. exact Hin.
  - destruct (alpha_rename_idents ρ
      (fresh_ident x used :: used) xs) as [(xsr_tail, ρ_tail) used_tail]
      eqn:Htail.
    injection Hrename as _ _ <-.
    eapply IH.
    + exact Htail.
    + right. exact Hin.
Qed.

Lemma alpha_rename_idents_fresh_used :
  forall ρ used xs xsr ρ' used',
    alpha_rename_idents ρ used xs = (xsr, ρ', used') ->
    Forall (fun x => ~ In x used) xsr.
Proof.
  intros ρ used xs.
  revert ρ used.
  induction xs as [| x xs IH]; intros ρ used xsr ρ' used' Hrename;
    simpl in Hrename.
  - injection Hrename as <- _ _. constructor.
  - destruct (alpha_rename_idents ρ
      (fresh_ident x used :: used) xs) as [(xsr_tail, ρ_tail) used_tail]
      eqn:Htail.
    injection Hrename as <- _ _.
    constructor.
    + apply fresh_ident_not_in.
    + pose proof (IH ρ (fresh_ident x used :: used)
        xsr_tail ρ_tail used_tail Htail)
        as Hfresh_tail.
      clear Htail.
      revert Hfresh_tail.
      induction xsr_tail as [| y ys IHys]; intros Hfresh_tail.
      * constructor.
      * inversion Hfresh_tail; subst. constructor.
        -- intros Hiny. apply H1. right. exact Hiny.
        -- apply IHys. exact H2.
Qed.

Lemma alpha_rename_idents_outputs_in_used :
  forall ρ used xs xsr ρ' used',
    alpha_rename_idents ρ used xs = (xsr, ρ', used') ->
    forall x, In x xsr -> In x used'.
Proof.
  intros ρ used xs.
  revert ρ used.
  induction xs as [| x xs IH]; intros ρ used xsr ρ' used' Hrename y Hin;
    simpl in Hrename.
  - injection Hrename as <- _ _. contradiction.
  - destruct (alpha_rename_idents ρ
      (fresh_ident x used :: used) xs) as [(xsr_tail, ρ_tail) used_tail]
      eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    destruct Hin as [Hy | Hin].
    + subst y. eapply alpha_rename_idents_used_extends.
      * exact Htail.
      * left. reflexivity.
    + eapply IH.
      * exact Htail.
      * exact Hin.
Qed.

Lemma alpha_rename_idents_outputs_nodup :
  forall ρ used xs xsr ρ' used',
    alpha_rename_idents ρ used xs = (xsr, ρ', used') ->
    NoDup xsr.
Proof.
  intros ρ used xs.
  revert ρ used.
  induction xs as [| x xs IH]; intros ρ used xsr ρ' used' Hrename;
    simpl in Hrename.
  - injection Hrename as <- _ _. constructor.
  - destruct (alpha_rename_idents ρ
      (fresh_ident x used :: used) xs) as [(xsr_tail, ρ_tail) used_tail]
      eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    constructor.
    + intro Hin.
      pose proof (alpha_rename_idents_fresh_used _ _ _ _ _ _ Htail)
        as Hfresh_tail.
      rewrite Forall_forall in Hfresh_tail.
      specialize (Hfresh_tail (fresh_ident x used) Hin).
      apply Hfresh_tail. left. reflexivity.
    + eapply IH. exact Htail.
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
  | EA_MakeClosure : forall ρ fname captures,
      expr_alpha ρ
        (EMakeClosure fname captures)
        (EMakeClosure fname (map (fun x => lookup_rename x ρ) captures))
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
  | EA_CallGeneric : forall ρ fname type_args args argsr,
      exprs_alpha ρ args argsr ->
      expr_alpha ρ
        (ECallGeneric fname type_args args)
        (ECallGeneric fname type_args argsr)
  | EA_CallExpr : forall ρ callee calleer args argsr,
      expr_alpha ρ callee calleer ->
      exprs_alpha ρ args argsr ->
      expr_alpha ρ (ECallExpr callee args) (ECallExpr calleer argsr)
  | EA_Struct : forall ρ name lts args fields fieldsr,
      expr_alpha ρ (EStruct name lts args fields) (EStruct name lts args fieldsr)
  | EA_Enum : forall ρ enum_name variant_name lts args payloads payloadsr,
      exprs_alpha ρ payloads payloadsr ->
      expr_alpha ρ
        (EEnum enum_name variant_name lts args payloads)
        (EEnum enum_name variant_name lts args payloadsr)
  | EA_Match : forall ρ scrut scrutr branches branchesr,
      expr_alpha ρ
        (EMatch scrut branches)
        (EMatch scrutr branchesr)
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

Lemma params_alpha_length :
  forall ps psr,
    params_alpha ps psr ->
    List.length ps = List.length psr.
Proof.
  intros ps psr Halpha.
  induction Halpha; simpl; congruence.
Qed.

Lemma match_binder_params_alpha_rename_idents :
  forall ρ used binders bindersr ρ' used' tys ps,
    alpha_rename_idents ρ used binders = (bindersr, ρ', used') ->
    match_binder_params binders tys = infer_ok ps ->
    exists psr,
      match_binder_params bindersr tys = infer_ok psr /\
      params_alpha ps psr /\
      alpha_rename_params ρ used ps = (psr, ρ', used').
Proof.
  intros ρ used binders.
  revert ρ used.
  induction binders as [| x xs IH]; intros ρ used bindersr ρ' used' tys ps
    Hidents Hparams; simpl in Hidents, Hparams.
  - destruct tys; try discriminate.
    injection Hidents as <- <- <-.
    injection Hparams as <-.
    exists []. repeat split; constructor.
  - destruct tys as [| T Ts]; try discriminate.
    destruct (alpha_rename_idents ρ
      (fresh_ident x used :: used) xs) as [[xsr_tail ρ_tail] used_tail]
      eqn:Htail.
    inversion Hidents; subst; clear Hidents.
    destruct (match_binder_params xs Ts) as [ps_tail | err] eqn:Hparams_tail;
      try discriminate.
    injection Hparams as <-.
    destruct (IH _ _ _ _ _ _ _ Htail Hparams_tail)
      as [psr_tail [Hparamsr_tail [Halpha_tail Hrename_tail]]].
    exists (MkParam MImmutable (fresh_ident x used) T :: psr_tail).
    simpl. rewrite Hparamsr_tail. split.
    + reflexivity.
    + split.
      * constructor.
        -- unfold same_param_shape. simpl. split; reflexivity.
        -- exact Halpha_tail.
      * rewrite Hrename_tail. reflexivity.
Qed.

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
  - destruct (alpha_rename_expr ρ used e1) as [er0 used0].
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ used0)) :: ρ)
      (fresh_ident i (i :: free_vars_expr e2 ++ used0) ::
       i :: free_vars_expr e2 ++ used0) e2).
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
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l0).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
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
  - destruct ((fix go (used0 : list ident) (payloads0 : list expr)
                : list expr * list ident :=
                 match payloads0 with
                 | [] => ([], used0)
                 | e0 :: rest =>
                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
                     let (rest', used2) := go used1 rest in
                     (e0' :: rest', used2)
                 end) used l1).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    destruct ((fix go (used0 : list ident)
                    (branches0 : list (string * list ident * expr))
                : list (string * list ident * expr) * list ident :=
                 match branches0 with
                 | [] => ([], used0)
                 | (variant_name, binders, e0) :: rest =>
                     let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
                     let '(binders', ρ_branch, used1) :=
                       alpha_rename_idents ρ binder_seed binders in
                     let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
                     let (rest', used3) := go used2 rest in
                     ((variant_name, binders', e0') :: rest', used3)
                 end) used0 l).
    injection Hrename as <- _. simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    inversion Hrename; subst; clear Hrename. simpl in Hplace.
    try discriminate; contradiction.
  - simpl in Hrename.
    destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    inversion Hrename; subst; clear Hrename.
    simpl in Hplace. discriminate.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    injection Hrename as <- _.
    simpl in Hplace.
    destruct (expr_as_place er0) as [pr0 |] eqn:Hpr0; [|discriminate].
    inversion Hplace; subst; clear Hplace.
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
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l0).
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
  - destruct ((fix go (used0 : list ident) (payloads0 : list expr)
                : list expr * list ident :=
                 match payloads0 with
                 | [] => ([], used0)
                 | e0 :: rest =>
                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
                     let (rest', used2) := go used1 rest in
                     (e0' :: rest', used2)
                 end) used l1).
    injection Hrename as <- _. reflexivity.
	  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
	    destruct ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
	                : list (string * list ident * expr) * list ident :=
	                 match branches0 with
	                 | [] => ([], used0)
	                 | (variant_name, binders, e0) :: rest =>
	                     let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
	                     let '(binders', ρ_branch, used1) :=
	                       alpha_rename_idents ρ binder_seed binders in
	                     let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
	                     let (rest', used3) := go used2 rest in
	                     ((variant_name, binders', e0') :: rest', used3)
	                 end) used0 l).
	    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    injection Hrename as <- _. reflexivity.
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnone.
    destruct (expr_as_place er0) as [pr |] eqn:Hpr; [inversion Hnone |].
    simpl. rewrite (IHe used er0 _ He Hpr). reflexivity.
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
  | EMakeClosure _ _ => 1
  | EPlace _ => 1
  | ELet _ _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ELetInfer _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ECall _ args =>
      S ((fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | ECallGeneric _ _ args =>
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
  | EEnum _ _ _ _ payloads =>
      S ((fix go (payloads0 : list expr) : nat :=
            match payloads0 with
            | [] => 0
            | e :: rest => expr_size e + go rest
            end) payloads)
  | EMatch scrut branches =>
      S (expr_size scrut +
         (fix go (branches0 : list (string * list ident * expr)) : nat :=
            match branches0 with
            | [] => 0
            | (_, _, e) :: rest => expr_size e + go rest
            end) branches)
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

Lemma expr_size_call_generic_arg_lt : forall fname type_args args arg,
  In arg args ->
  expr_size arg < expr_size (ECallGeneric fname type_args args).
Proof.
  intros fname type_args args.
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

Lemma expr_size_enum_payload_lt :
  forall enum_name variant_name lts args payloads payload,
    In payload payloads ->
    expr_size payload < expr_size (EEnum enum_name variant_name lts args payloads).
Proof.
  intros enum_name variant_name lts args payloads.
  induction payloads as [| p rest IH]; intros payload Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH payload Hin). simpl in IH. lia.
Qed.

Lemma expr_size_match_scrutinee_lt :
  forall scrut branches,
    expr_size scrut < expr_size (EMatch scrut branches).
Proof.
  intros. simpl. lia.
Qed.

Lemma expr_size_match_branch_lt :
  forall scrut branches variant binders branch,
    In (variant, binders, branch) branches ->
    expr_size branch < expr_size (EMatch scrut branches).
Proof.
  intros scrut branches.
  induction branches as [| [[name binders0] e] rest IH];
    intros variant binders branch Hin.
  - contradiction.
  - simpl in *. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. lia.
    + specialize (IH variant binders branch Hin). simpl in IH. lia.
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
    inversion Hrename; subst; clear Hrename.
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

Lemma alpha_rename_match_branches_used_extends :
  forall ρ used branches branchesr used',
  (forall ρ0 used0 name binders e er used1,
      In (name, binders, e) branches ->
      alpha_rename_expr ρ0 used0 e = (er, used1) ->
      forall x, In x used0 -> In x used1) ->
  ((fix go (used0 : list ident)
      (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name, binders, e) :: rest =>
          let binder_seed := binders ++ free_vars_expr e ++ used0 in
          let '(binders', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders in
          let (e', used2) := alpha_rename_expr ρ_branch used1 e in
          let (rest', used3) := go used2 rest in
          ((name, binders', e') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  forall x, In x used -> In x used'.
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name binders] e] rest IH];
    intros used branchesr used' Hexpr Hrename x Hin; simpl in Hrename.
  - injection Hrename as _ <-. exact Hin.
  - set (binder_seed := binders ++ free_vars_expr e ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders)
      as [[bindersr ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e) as [er used2] eqn:He.
    destruct ((fix go (used0 : list ident)
          (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used0)
          | (name0, binders0, e0) :: rest0 =>
              let '(binders0', ρ_branch0, used3) :=
                alpha_rename_idents ρ
                  (binders0 ++ free_vars_expr e0 ++ used0) binders0 in
              let (e0', used4) := alpha_rename_expr ρ_branch0 used3 e0 in
              let (rest', used5) := go used4 rest0 in
              ((name0, binders0', e0') :: rest', used5)
          end) used2 rest) as [restr used3] eqn:Hrest.
    subst binder_seed.
    simpl in Hrename.
    rewrite Hbinders in Hrename.
    rewrite He in Hrename.
    rewrite Hrest in Hrename.
    injection Hrename as _ <-.
    eapply IH.
    + intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin_rest Hrename0.
      eapply (Hexpr ρ0 used0 name0 binders0 e0 er0 used_tail).
      * right. exact Hin_rest.
      * exact Hrename0.
    + exact Hrest.
    + eapply (Hexpr ρ_branch used1 name binders e er used2).
      * left. reflexivity.
      * exact He.
      * eapply alpha_rename_idents_used_extends.
        -- exact Hbinders.
        -- apply in_or_app. right.
           apply in_or_app. right. exact Hin.
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
  + remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used l0) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as _ <-.
    eapply alpha_rename_call_args_used_extends.
    * intros used0 e er0 used1 Hin_arg Hrename0.
      eapply IH.
      -- pose proof (expr_size_call_generic_arg_lt i l l0 e Hin_arg)
          as Harg_lt.
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
  + remember
      ((fix go (used0 : list ident) (payloads0 : list expr)
          : list expr * list ident :=
          match payloads0 with
          | [] => ([], used0)
          | e0 :: rest =>
              let (e0', used1) := alpha_rename_expr ρ used0 e0 in
              let (rest', used2) := go used1 rest in
              (e0' :: rest', used2)
          end) used l1) as r eqn:Hpayloads.
    destruct r as [payloadsr used_payloads].
    injection Hrename as _ <-.
    eapply alpha_rename_call_args_used_extends.
    * intros used_arg epayload er0 used_tail Hin_payload Hrename0.
      eapply IH.
      -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 epayload Hin_payload)
           as Hpayload_lt.
         assert (expr_size epayload < n) as Hlt_payload by lia.
         exact Hlt_payload.
      -- exact Hrename0.
    * symmetry. exact Hpayloads.
    * exact Hin.
  + destruct (alpha_rename_expr ρ used e) as [scrutr used0] eqn:Hscrut.
    remember
      ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
	          match branches0 with
	          | [] => ([], used0)
	          | (variant_name, binders, e0) :: rest =>
	              let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
	              let '(binders', ρ_branch, used1) :=
	                alpha_rename_idents ρ binder_seed binders in
	              let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
	              let (rest', used3) := go used2 rest in
	              ((variant_name, binders', e0') :: rest', used3)
	          end) used0 l) as r eqn:Hbranches.
    destruct r as [branchesr used_branches].
    injection Hrename as _ <-.
    eapply alpha_rename_match_branches_used_extends.
    * intros ρ_branch used_branch variant_name binders ebranch er0 used_tail Hin_branch Hrename0.
      eapply IH.
      -- pose proof (expr_size_match_branch_lt e l variant_name binders ebranch Hin_branch)
           as Hbranch_lt.
         assert (expr_size ebranch < n) as Hlt_branch by lia.
         exact Hlt_branch.
      -- exact Hrename0.
    * symmetry. exact Hbranches.
    * eapply IH.
      -- pose proof (expr_size_match_scrutinee_lt e l) as Hscrut_lt.
         assert (expr_size e < n) as Hlt_scrut by lia.
         exact Hlt_scrut.
      -- exact Hscrut.
      -- exact Hin.
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
	    inversion Hrename; subst; exact Hin.
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

Lemma alpha_rename_match_branches_local_store_names_in_used :
  forall ρ used branches branchesr used',
    (forall ρ0 used0 name binders e er used1,
        In (name, binders, e) branches ->
        alpha_rename_expr ρ0 used0 e = (er, used1) ->
        forall x, In x (expr_local_store_names er) -> In x used1) ->
    ((fix go (used0 : list ident)
        (branches0 : list (string * list ident * expr))
        : list (string * list ident * expr) * list ident :=
        match branches0 with
        | [] => ([], used0)
        | (name, binders, e) :: rest =>
            let '(binders', ρ_branch, used1) :=
              alpha_rename_idents ρ
                (binders ++ free_vars_expr e ++ used0) binders in
            let (e', used2) := alpha_rename_expr ρ_branch used1 e in
            let (rest', used3) := go used2 rest in
            ((name, binders', e') :: rest', used3)
        end) used branches) = (branchesr, used') ->
    forall x, In x (match_branches_local_store_names branchesr) -> In x used'.
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name binders] e] rest IH];
    intros used branchesr used' Hexpr Hrename x Hin; simpl in Hrename.
  - injection Hrename as <- <-. simpl in Hin. contradiction.
  - destruct (alpha_rename_idents ρ
      (binders ++ free_vars_expr e ++ used) binders)
      as [[bindersr ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e) as [er used2] eqn:He.
    destruct ((fix go (used0 : list ident)
          (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used0)
          | (name0, binders0, e0) :: rest0 =>
              let '(binders0', ρ_branch0, used3) :=
                alpha_rename_idents ρ
                  (binders0 ++ free_vars_expr e0 ++ used0) binders0 in
              let (e0', used4) := alpha_rename_expr ρ_branch0 used3 e0 in
              let (rest', used5) := go used4 rest0 in
              ((name0, binders0', e0') :: rest', used5)
          end) used2 rest) as [restr used3] eqn:Hrest.
    injection Hrename as <- <-.
    simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply alpha_rename_match_branches_used_extends.
      * intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin_rest Hrename0.
        eapply alpha_rename_expr_used_extends. exact Hrename0.
      * exact Hrest.
      * eapply alpha_rename_expr_used_extends.
        -- exact He.
        -- eapply alpha_rename_idents_outputs_in_used; eassumption.
    + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply alpha_rename_match_branches_used_extends.
        -- intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin_rest Hrename0.
           eapply alpha_rename_expr_used_extends. exact Hrename0.
        -- exact Hrest.
        -- eapply (Hexpr ρ_branch used1 name binders e er used2).
           ++ left. reflexivity.
           ++ exact He.
           ++ exact Hin.
      * eapply IH.
        -- intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin_rest Hrename0.
           eapply (Hexpr ρ0 used0 name0 binders0 e0 er0 used_tail).
           ++ right. exact Hin_rest.
           ++ exact Hrename0.
        -- exact Hrest.
        -- exact Hin.
Qed.

Lemma Forall_fresh_weaken : forall (used used' xs : list ident),
  (forall x, In x used -> In x used') ->
  Forall (fun x => ~ In x used') xs ->
  Forall (fun x => ~ In x used) xs.
Proof.
  intros used used' xs Hextends Hfresh.
  induction Hfresh as [| x xs Hnot Hfresh IH].
  - constructor.
  - constructor.
    + intro Hin. apply Hnot. apply Hextends. exact Hin.
    + exact IH.
Qed.

Lemma NoDup_app_from_Forall : forall (xs ys : list ident),
  NoDup xs ->
  NoDup ys ->
  Forall (fun x => ~ In x ys) xs ->
  NoDup (xs ++ ys).
Proof.
  intros xs ys Hxs Hys Hfresh.
  induction Hxs as [| x xs Hnotin Hnodup IH]; simpl.
  - exact Hys.
  - inversion Hfresh as [| ? ? Hnotin_ys Hfresh_tail]; subst.
    constructor.
    + intro Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * apply Hnotin. exact Hin.
      * apply Hnotin_ys. exact Hin.
    + apply IH. exact Hfresh_tail.
Qed.

Lemma Forall_not_in_app_of_used :
  forall (xs ys used : list ident),
    (forall x, In x xs -> In x used) ->
    Forall (fun y => ~ In y used) ys ->
    Forall (fun x => ~ In x ys) xs.
Proof.
  intros xs ys used Hxs Hys.
  induction xs as [| x xs IH].
  - constructor.
  - constructor.
    + intro Hin_ys.
      rewrite Forall_forall in Hys.
      specialize (Hys x Hin_ys).
      apply Hys. apply Hxs. simpl. left. reflexivity.
    + apply IH. intros y Hy. apply Hxs. simpl. right. exact Hy.
Qed.

Lemma alpha_rename_call_args_local_store_names_in_used :
  forall ρ used args argsr used',
    (forall used0 e er used1,
        In e args ->
        alpha_rename_expr ρ used0 e = (er, used1) ->
        forall x, In x (expr_local_store_names er) -> In x used1) ->
    ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used args) = (argsr, used') ->
    forall x, In x (args_local_store_names argsr) -> In x used'.
Proof.
  intros ρ used args.
  revert used.
  induction args as [| arg rest IH]; intros used argsr used' Hexpr Hrename x Hin;
    simpl in Hrename.
  - injection Hrename as <- <-. simpl in Hin. contradiction.
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
    injection Hrename as <- <-.
    simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply alpha_rename_call_args_used_extends.
      * intros used0 e er0 used_tail Hin_rest Hrename0.
        eapply alpha_rename_expr_used_extends. exact Hrename0.
      * exact Hrest.
      * eapply Hexpr.
        -- left. reflexivity.
        -- exact Harg.
        -- exact Hin.
    + eapply IH.
      * intros used0 e er0 used_tail Hin_rest Hrename0.
        eapply Hexpr.
        -- right. exact Hin_rest.
        -- exact Hrename0.
      * exact Hrest.
      * exact Hin.
Qed.

Lemma alpha_rename_struct_fields_local_store_names_in_used :
  forall ρ used fields fieldsr used',
    (forall used0 fname e er used1,
        In (fname, e) fields ->
        alpha_rename_expr ρ used0 e = (er, used1) ->
        forall x, In x (expr_local_store_names er) -> In x used1) ->
    ((fix go (used0 : list ident) (fields0 : list (string * expr))
        : list (string * expr) * list ident :=
        match fields0 with
        | [] => ([], used0)
        | (fname, e) :: rest =>
            let (e', used1) := alpha_rename_expr ρ used0 e in
            let (rest', used2) := go used1 rest in
            ((fname, e') :: rest', used2)
        end) used fields) = (fieldsr, used') ->
    forall x, In x (fields_local_store_names fieldsr) -> In x used'.
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname e] rest IH]; intros used fieldsr used' Hexpr Hrename x Hin;
    simpl in Hrename.
  - injection Hrename as <- <-. simpl in Hin. contradiction.
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
    injection Hrename as <- <-.
    simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply alpha_rename_struct_fields_used_extends.
      * intros used0 fname0 e0 er0 used_tail Hin_rest Hrename0.
        eapply alpha_rename_expr_used_extends. exact Hrename0.
      * exact Hrest.
      * eapply Hexpr.
        -- left. reflexivity.
        -- exact He.
        -- exact Hin.
    + eapply IH.
      * intros used0 fname0 e0 er0 used_tail Hin_rest Hrename0.
        eapply Hexpr.
        -- right. exact Hin_rest.
        -- exact Hrename0.
      * exact Hrest.
      * exact Hin.
Qed.

Lemma alpha_rename_expr_local_store_names_in_used :
  forall rho used e er used',
    alpha_rename_expr rho used e = (er, used') ->
    forall x, In x (expr_local_store_names er) -> In x used'.
Proof.
  assert (Hsize : forall n rho used e er used',
    expr_size e < n ->
    alpha_rename_expr rho used e = (er, used') ->
    forall x, In x (expr_local_store_names er) -> In x used').
  {
  induction n as [| n IH]; intros rho used e er used' Hlt Hrename x Hin.
  - lia.
  - destruct e; simpl in Hrename.
    + injection Hrename as <- <-. simpl in Hin. contradiction.
    + injection Hrename as <- <-. simpl in Hin. contradiction.
    + injection Hrename as <- <-. simpl in Hin. contradiction.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: rho)
        (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
         i :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      injection Hrename as <- <-.
      simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply alpha_rename_expr_used_extends.
        -- exact He2.
        -- right. right. apply in_or_app. right.
           eapply IH.
           ++ simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
           ++ exact He1.
           ++ exact Hin.
      * destruct Hin as [Heq | Hin].
        -- subst. eapply alpha_rename_expr_used_extends.
           ++ exact He2.
           ++ simpl. left. reflexivity.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
           ++ exact He2.
           ++ exact Hin.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: rho)
        (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
         i :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      injection Hrename as <- <-.
      simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply alpha_rename_expr_used_extends.
        -- exact He2.
        -- right. right. apply in_or_app. right.
           eapply IH.
           ++ simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
           ++ exact He1.
           ++ exact Hin.
      * destruct Hin as [Heq | Hin].
        -- subst. eapply alpha_rename_expr_used_extends.
           ++ exact He2.
           ++ simpl. left. reflexivity.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
           ++ exact He2.
           ++ exact Hin.
	    + injection Hrename as <- <-. simpl in Hin. contradiction.
	    + injection Hrename as <- <-. simpl in Hin. contradiction.
	    + injection Hrename as <- <-. simpl in Hin. contradiction.
	    + remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used l) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_call in Hin.
      eapply alpha_rename_call_args_local_store_names_in_used.
      * intros used0 e er0 used1 Hin_arg Hrename0.
        eapply IH.
        -- pose proof (expr_size_call_arg_lt i l e Hin_arg) as Harg_lt.
           assert (expr_size e < n) as Hlt_arg by lia. exact Hlt_arg.
        -- exact Hrename0.
      * symmetry. exact Hargs.
      * exact Hin.
    + remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used l0) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_call_generic in Hin.
      eapply alpha_rename_call_args_local_store_names_in_used.
      * intros used0 e er0 used1 Hin_arg Hrename0.
        eapply IH.
        -- pose proof (expr_size_call_generic_arg_lt i l l0 e Hin_arg)
             as Harg_lt.
           assert (expr_size e < n) as Hlt_arg by lia. exact Hlt_arg.
        -- exact Hrename0.
      * symmetry. exact Hargs.
      * exact Hin.
    + destruct (alpha_rename_expr rho used e) as [callee_r used0] eqn:Hcallee.
      remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1') := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1' rest in
                (arg' :: rest', used2)
            end) used0 l) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_call_expr in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply alpha_rename_call_args_used_extends.
        -- intros used_arg earg er0 used_tail Hin_arg Hrename0.
           eapply alpha_rename_expr_used_extends. exact Hrename0.
        -- symmetry. exact Hargs.
        -- eapply IH.
           ++ pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
              assert (expr_size e < n) as Hlt_callee by lia. exact Hlt_callee.
           ++ exact Hcallee.
           ++ exact Hin.
      * eapply alpha_rename_call_args_local_store_names_in_used.
        -- intros used_arg earg er0 used_tail Hin_arg Hrename0.
           eapply IH.
           ++ pose proof (expr_size_callexpr_arg_lt e l earg Hin_arg) as Harg_lt.
              assert (expr_size earg < n) as Hlt_arg by lia. exact Hlt_arg.
           ++ exact Hrename0.
        -- symmetry. exact Hargs.
        -- exact Hin.
    + remember
        ((fix go (used0 : list ident) (fields0 : list (string * expr))
            : list (string * expr) * list ident :=
            match fields0 with
            | [] => ([], used0)
            | (fname, e0) :: rest =>
                let (e0', used1) := alpha_rename_expr rho used0 e0 in
                let (rest', used2) := go used1 rest in
                ((fname, e0') :: rest', used2)
            end) used l1) as r eqn:Hfields.
      destruct r as [fieldsr used_fields].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_struct in Hin.
      eapply alpha_rename_struct_fields_local_store_names_in_used.
      * intros used0 fname efield er0 used1 Hin_field Hrename0.
        eapply IH.
        -- pose proof (expr_size_struct_field_lt s l l0 l1 fname efield Hin_field) as Hfield_lt.
           assert (expr_size efield < n) as Hlt_field by lia. exact Hlt_field.
        -- exact Hrename0.
    * symmetry. exact Hfields.
    * exact Hin.
    + remember
        ((fix go (used0 : list ident) (payloads0 : list expr)
            : list expr * list ident :=
            match payloads0 with
            | [] => ([], used0)
            | e0 :: rest =>
                let (e0', used1) := alpha_rename_expr rho used0 e0 in
                let (rest', used2) := go used1 rest in
                (e0' :: rest', used2)
            end) used l1) as r eqn:Hpayloads.
      destruct r as [payloadsr used_payloads].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_enum in Hin.
      eapply alpha_rename_call_args_local_store_names_in_used.
      * intros used_arg epayload er0 used_tail Hin_payload Hrename0.
        eapply IH.
        -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 epayload Hin_payload)
             as Hpayload_lt.
           assert (expr_size epayload < n) as Hlt_payload by lia. exact Hlt_payload.
        -- exact Hrename0.
      * symmetry. exact Hpayloads.
      * exact Hin.
	    + destruct (alpha_rename_expr rho used e) as [scrutr used0] eqn:Hscrut.
	      remember
	        ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
	            : list (string * list ident * expr) * list ident :=
		            match branches0 with
		            | [] => ([], used0)
		            | (variant_name, binders, e0) :: rest =>
		                let '(binders', rho_branch, used1) :=
		                  alpha_rename_idents rho
		                    (binders ++ free_vars_expr e0 ++ used0) binders in
		                let (e0', used2) := alpha_rename_expr rho_branch used1 e0 in
		                let (rest', used3) := go used2 rest in
		                ((variant_name, binders', e0') :: rest', used3)
		            end) used0 l) as r eqn:Hbranches.
	      destruct r as [branchesr used_branches].
	      inversion Hrename; subst; clear Hrename.
	      simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
		      * eapply alpha_rename_match_branches_used_extends.
		        -- intros rho_branch used_branch variant_name binders ebranch er0 used_tail
	                Hin_branch Hrename0.
		           eapply alpha_rename_expr_used_extends. exact Hrename0.
	        -- symmetry. exact Hbranches.
	        -- eapply IH.
	           ++ pose proof (expr_size_match_scrutinee_lt e l) as Hscrut_lt.
	              assert (expr_size e < n) as Hlt_scrut by lia. exact Hlt_scrut.
	           ++ exact Hscrut.
	           ++ exact Hin.
		      * eapply alpha_rename_match_branches_local_store_names_in_used.
		        -- intros rho_branch used_branch variant_name binders ebranch er0 used_tail
	                Hin_branch Hrename0.
	           eapply IH.
	           ++ pose proof (expr_size_match_branch_lt e l variant_name binders ebranch Hin_branch)
	                as Hbranch_lt.
	              assert (expr_size ebranch < n) as Hlt_branch by lia. exact Hlt_branch.
	           ++ exact Hrename0.
	        -- symmetry. exact Hbranches.
	        -- exact Hin.
	    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
	      injection Hrename as <- <-.
	      eapply IH.
	      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
	      * exact He.
	      * exact Hin.
	    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
	      injection Hrename as <- <-.
	      eapply IH.
	      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
	      * exact He.
	      * exact Hin.
    + injection Hrename as <- <-. simpl in Hin. contradiction.
    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
      injection Hrename as <- <-.
      eapply IH.
      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
      * exact He.
      * exact Hin.
    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
      injection Hrename as <- <-.
      eapply IH.
      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
      * exact He.
      * exact Hin.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
      destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
      injection Hrename as <- <-.
      simpl in Hin. repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin | [Hin | Hin]].
      * eapply alpha_rename_expr_used_extends.
        -- exact He3.
        -- eapply alpha_rename_expr_used_extends.
           ++ exact He2.
           ++ eapply IH.
              ** simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
              ** exact He1.
              ** exact Hin.
      * eapply alpha_rename_expr_used_extends.
        -- exact He3.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
           ++ exact He2.
           ++ exact Hin.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e3 < n) as Hlt_e3 by lia. exact Hlt_e3.
        -- exact He3.
        -- exact Hin.
  }
  intros rho used e er used' Hrename.
  eapply (Hsize (S (expr_size e))).
  - apply Nat.lt_succ_diag_r.
  - exact Hrename.
Qed.

Lemma alpha_rename_call_args_local_store_names_fresh_used :
  forall ρ used args argsr used',
    (forall used0 e er used1,
        In e args ->
        alpha_rename_expr ρ used0 e = (er, used1) ->
        Forall (fun x => ~ In x used0) (expr_local_store_names er)) ->
    ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used args) = (argsr, used') ->
    Forall (fun x => ~ In x used) (args_local_store_names argsr).
Proof.
  intros ρ used args.
  revert used.
  induction args as [| arg rest IH]; intros used argsr used' Hexpr Hrename;
    simpl in Hrename.
  - injection Hrename as <- _. simpl. constructor.
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
    injection Hrename as <- _.
    simpl. apply Forall_app. split.
    + eapply Hexpr.
      * left. reflexivity.
      * exact Harg.
    + eapply Forall_fresh_weaken.
      * intros x Hin.
        eapply alpha_rename_expr_used_extends.
        -- exact Harg.
        -- exact Hin.
      * eapply IH.
        -- intros used0 e er0 used_tail Hin_rest Hrename0.
           eapply Hexpr.
           ++ right. exact Hin_rest.
           ++ exact Hrename0.
        -- exact Hrest.
Qed.

Lemma alpha_rename_struct_fields_local_store_names_fresh_used :
  forall ρ used fields fieldsr used',
    (forall used0 fname e er used1,
        In (fname, e) fields ->
        alpha_rename_expr ρ used0 e = (er, used1) ->
        Forall (fun x => ~ In x used0) (expr_local_store_names er)) ->
    ((fix go (used0 : list ident) (fields0 : list (string * expr))
        : list (string * expr) * list ident :=
        match fields0 with
        | [] => ([], used0)
        | (fname, e) :: rest =>
            let (e', used1) := alpha_rename_expr ρ used0 e in
            let (rest', used2) := go used1 rest in
            ((fname, e') :: rest', used2)
        end) used fields) = (fieldsr, used') ->
    Forall (fun x => ~ In x used) (fields_local_store_names fieldsr).
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname e] rest IH]; intros used fieldsr used' Hexpr Hrename;
    simpl in Hrename.
  - injection Hrename as <- _. simpl. constructor.
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
    injection Hrename as <- _.
    simpl. apply Forall_app. split.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + eapply Forall_fresh_weaken.
      * intros x Hin.
        eapply alpha_rename_expr_used_extends.
        -- exact He.
        -- exact Hin.
      * eapply IH.
        -- intros used0 fname0 e0 er0 used_tail Hin_rest Hrename0.
           eapply Hexpr.
           ++ right. exact Hin_rest.
           ++ exact Hrename0.
        -- exact Hrest.
Qed.

Lemma alpha_rename_match_branches_local_store_names_fresh_used :
  forall ρ used branches branchesr used',
    (forall ρ0 used0 name binders e er used1,
        In (name, binders, e) branches ->
        alpha_rename_expr ρ0 used0 e = (er, used1) ->
        Forall (fun x => ~ In x used0) (expr_local_store_names er)) ->
    ((fix go (used0 : list ident)
        (branches0 : list (string * list ident * expr))
        : list (string * list ident * expr) * list ident :=
        match branches0 with
        | [] => ([], used0)
        | (name, binders, e) :: rest =>
            let binder_seed := binders ++ free_vars_expr e ++ used0 in
            let '(binders', ρ_branch, used1) :=
              alpha_rename_idents ρ binder_seed binders in
            let (e', used2) := alpha_rename_expr ρ_branch used1 e in
            let (rest', used3) := go used2 rest in
            ((name, binders', e') :: rest', used3)
        end) used branches) = (branchesr, used') ->
    Forall (fun x => ~ In x used) (match_branches_local_store_names branchesr).
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name binders] e] rest IH];
    intros used branchesr used' Hexpr Hrename; simpl in Hrename.
  - injection Hrename as <- _. simpl. constructor.
  - set (binder_seed := binders ++ free_vars_expr e ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders)
      as [[bindersr ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e) as [er used2] eqn:He.
    destruct ((fix go (used0 : list ident)
          (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
	          match branches0 with
	          | [] => ([], used0)
	          | (name0, binders0, e0) :: rest0 =>
	              let '(binders0', ρ_branch0, used2) :=
	                alpha_rename_idents ρ
	                  (binders0 ++ free_vars_expr e0 ++ used0) binders0 in
              let (e0', used3) := alpha_rename_expr ρ_branch0 used2 e0 in
              let (rest', used4) := go used3 rest0 in
              ((name0, binders0', e0') :: rest', used4)
          end) used2 rest) as [restr used3] eqn:Hrest.
	    subst binder_seed.
	    simpl in Hrename.
	    rewrite Hbinders in Hrename.
	    rewrite He in Hrename.
	    rewrite Hrest in Hrename.
	    injection Hrename as <- _.
    simpl. apply Forall_app. split.
    + pose proof (alpha_rename_idents_fresh_used _ _ _ _ _ _ Hbinders)
        as Hbinders_fresh.
      eapply Forall_fresh_weaken.
      * intros x Hin.
        apply in_or_app. right. apply in_or_app. right. exact Hin.
      * exact Hbinders_fresh.
    + apply Forall_app. split.
      * eapply Forall_fresh_weaken.
        -- intros x Hin.
           eapply alpha_rename_idents_used_extends.
           ++ exact Hbinders.
           ++ apply in_or_app. right.
              apply in_or_app. right. exact Hin.
        -- eapply (Hexpr ρ_branch used1 name binders e er used2).
           ++ left. reflexivity.
           ++ exact He.
      * eapply Forall_fresh_weaken.
        -- intros x Hin.
           eapply alpha_rename_expr_used_extends.
           ++ exact He.
           ++ eapply alpha_rename_idents_used_extends.
              ** exact Hbinders.
              ** apply in_or_app. right.
                 apply in_or_app. right. exact Hin.
        -- eapply IH.
           ++ intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin_rest Hrename0.
              eapply (Hexpr ρ0 used0 name0 binders0 e0 er0 used_tail).
              ** right. exact Hin_rest.
              ** exact Hrename0.
           ++ exact Hrest.
Qed.

Lemma alpha_rename_expr_local_store_names_fresh_used :
  forall rho used e er used',
    alpha_rename_expr rho used e = (er, used') ->
    Forall (fun x => ~ In x used) (expr_local_store_names er).
Proof.
  assert (Hsize : forall n rho used e er used',
    expr_size e < n ->
    alpha_rename_expr rho used e = (er, used') ->
    Forall (fun x => ~ In x used) (expr_local_store_names er)).
  {
  induction n as [| n IH]; intros rho used e er used' Hlt Hrename.
  - lia.
  - destruct e; simpl in Hrename.
    + injection Hrename as <- _. simpl. constructor.
    + injection Hrename as <- _. simpl. constructor.
    + injection Hrename as <- _. simpl. constructor.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: rho)
        (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
         i :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      injection Hrename as <- _.
      simpl. apply Forall_app. split.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
        -- exact He1.
      * constructor.
        -- intro Hin.
           eapply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
           right. apply in_or_app. right.
           eapply alpha_rename_expr_used_extends; eauto.
        -- apply (Forall_fresh_weaken used
             (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
              i :: free_vars_expr e2 ++ used1)).
           ++ intros x Hin.
              right. right. apply in_or_app. right.
              eapply alpha_rename_expr_used_extends; eauto.
           ++ eapply IH.
              ** simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
              ** exact He2.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: rho)
        (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
         i :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      injection Hrename as <- _.
      simpl. apply Forall_app. split.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
        -- exact He1.
      * constructor.
        -- intro Hin.
           eapply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
           right. apply in_or_app. right.
           eapply alpha_rename_expr_used_extends; eauto.
        -- apply (Forall_fresh_weaken used
             (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
              i :: free_vars_expr e2 ++ used1)).
           ++ intros x Hin.
              right. right. apply in_or_app. right.
              eapply alpha_rename_expr_used_extends; eauto.
           ++ eapply IH.
              ** simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
              ** exact He2.
	    + injection Hrename as <- _. simpl. constructor.
	    + injection Hrename as <- _. simpl. constructor.
	    + injection Hrename as <- _. simpl. constructor.
	    + remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used l) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call.
      eapply alpha_rename_call_args_local_store_names_fresh_used.
      * intros used0 e er0 used1 Hin_arg Hrename0.
        eapply IH.
        -- pose proof (expr_size_call_arg_lt i l e Hin_arg) as Harg_lt.
           assert (expr_size e < n) as Hlt_arg by lia.
           exact Hlt_arg.
        -- exact Hrename0.
      * symmetry. exact Hargs.
    + remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used l0) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call_generic.
      eapply alpha_rename_call_args_local_store_names_fresh_used.
      * intros used0 e er0 used1 Hin_arg Hrename0.
        eapply IH.
        -- pose proof (expr_size_call_generic_arg_lt i l l0 e Hin_arg)
             as Harg_lt.
           assert (expr_size e < n) as Hlt_arg by lia.
           exact Hlt_arg.
        -- exact Hrename0.
      * symmetry. exact Hargs.
    + destruct (alpha_rename_expr rho used e) as [callee_r used0] eqn:Hcallee.
      remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1') := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1' rest in
                (arg' :: rest', used2)
            end) used0 l) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call_expr.
      apply Forall_app. split.
      * eapply IH.
        -- pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
           assert (expr_size e < n) as Hlt_callee by lia.
           exact Hlt_callee.
        -- exact Hcallee.
      * eapply Forall_fresh_weaken.
        -- intros x Hin.
           eapply alpha_rename_expr_used_extends; eauto.
        -- eapply alpha_rename_call_args_local_store_names_fresh_used.
           ++ intros used_arg earg er0 used_tail Hin_arg Hrename0.
              eapply IH.
              ** pose proof (expr_size_callexpr_arg_lt e l earg Hin_arg) as Harg_lt.
                 assert (expr_size earg < n) as Hlt_arg by lia.
                 exact Hlt_arg.
              ** exact Hrename0.
           ++ symmetry. exact Hargs.
    + remember
        ((fix go (used0 : list ident) (fields0 : list (string * expr))
            : list (string * expr) * list ident :=
            match fields0 with
            | [] => ([], used0)
            | (fname, e0) :: rest =>
                let (e0', used1) := alpha_rename_expr rho used0 e0 in
                let (rest', used2) := go used1 rest in
                ((fname, e0') :: rest', used2)
            end) used l1) as r eqn:Hfields.
      destruct r as [fieldsr used_fields].
      injection Hrename as <- _.
      rewrite expr_local_store_names_struct.
      eapply alpha_rename_struct_fields_local_store_names_fresh_used.
      * intros used0 fname efield er0 used1 Hin_field Hrename0.
        eapply IH.
        -- pose proof (expr_size_struct_field_lt s l l0 l1 fname efield Hin_field) as Hfield_lt.
           assert (expr_size efield < n) as Hlt_field by lia.
           exact Hlt_field.
        -- exact Hrename0.
      * symmetry. exact Hfields.
    + remember
        ((fix go (used0 : list ident) (payloads0 : list expr)
            : list expr * list ident :=
            match payloads0 with
            | [] => ([], used0)
            | e0 :: rest =>
                let (e0', used1) := alpha_rename_expr rho used0 e0 in
                let (rest', used2) := go used1 rest in
                (e0' :: rest', used2)
            end) used l1) as r eqn:Hpayloads.
      destruct r as [payloadsr used_payloads].
      injection Hrename as <- _.
      rewrite expr_local_store_names_enum.
      eapply alpha_rename_call_args_local_store_names_fresh_used.
      * intros used0 epayload er0 used1 Hin_payload Hrename0.
        eapply IH.
        -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 epayload Hin_payload)
             as Hpayload_lt.
           assert (expr_size epayload < n) as Hlt_payload by lia.
           exact Hlt_payload.
        -- exact Hrename0.
      * symmetry. exact Hpayloads.
	    + destruct (alpha_rename_expr rho used e) as [scrutr used0] eqn:Hscrut.
		      remember
		        ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
		            : list (string * list ident * expr) * list ident :=
		            match branches0 with
		            | [] => ([], used0)
		            | (variant_name, binders, e0) :: rest =>
		                let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
		                let '(binders', ρ_branch, used1) :=
		                  alpha_rename_idents rho binder_seed binders in
		                let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
		                let (rest', used3) := go used2 rest in
		                ((variant_name, binders', e0') :: rest', used3)
		            end) used0 l) as r eqn:Hbranches.
	      destruct r as [branchesr used_branches].
	      injection Hrename as <- _. simpl. apply Forall_app. split.
	      * eapply IH.
	        -- pose proof (expr_size_match_scrutinee_lt e l) as Hscrut_lt.
	           assert (expr_size e < n) as Hlt_scrut by lia. exact Hlt_scrut.
	        -- exact Hscrut.
	      * apply (Forall_fresh_weaken used used0).
	        -- intros x Hin.
	           eapply alpha_rename_expr_used_extends; eauto.
	        -- eapply alpha_rename_match_branches_local_store_names_fresh_used.
		           ++ intros rho_branch used_branch variant_name binders ebranch er0 used_tail
	                 Hin_branch Hrename0.
		              eapply IH.
		              ** pose proof (expr_size_match_branch_lt e l variant_name binders ebranch Hin_branch)
		                   as Hbranch_lt.
		                 assert (expr_size ebranch < n) as Hlt_branch by lia. exact Hlt_branch.
	              ** exact Hrename0.
	           ++ symmetry. exact Hbranches.
	    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
	      inversion Hrename; subst. simpl.
	      eapply IH.
	      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
	      * exact He.
	    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
	      inversion Hrename; subst. simpl.
	      eapply IH.
	      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
	      * exact He.
    + injection Hrename as <- _. simpl. constructor.
    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
      inversion Hrename; subst. simpl.
      eapply IH.
      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
      * exact He.
    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
      inversion Hrename; subst. simpl.
      eapply IH.
      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
      * exact He.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
      destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
      injection Hrename as <- _.
      simpl. apply Forall_app. split.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
        -- exact He1.
      * apply Forall_app. split.
        -- apply (Forall_fresh_weaken used used1).
           ++ intros x Hin.
              eapply alpha_rename_expr_used_extends; eauto.
           ++ eapply IH.
              ** simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
              ** exact He2.
        -- apply (Forall_fresh_weaken used used2).
           ++ intros x Hin.
              eapply alpha_rename_expr_used_extends.
              ** exact He2.
              ** eapply alpha_rename_expr_used_extends; eauto.
           ++ eapply IH.
              ** simpl in Hlt. assert (expr_size e3 < n) as Hlt_e3 by lia. exact Hlt_e3.
              ** exact He3.
  }
  intros rho used e er used' Hrename.
  eapply (Hsize (S (expr_size e))).
  - apply Nat.lt_succ_diag_r.
  - exact Hrename.
Qed.

Lemma alpha_rename_call_args_local_store_names_nodup :
  forall ρ used args argsr used',
    (forall used0 e er used1,
        In e args ->
        alpha_rename_expr ρ used0 e = (er, used1) ->
        NoDup (expr_local_store_names er)) ->
    ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used args) = (argsr, used') ->
    NoDup (args_local_store_names argsr).
Proof.
  intros ρ used args.
  revert used.
  induction args as [| arg rest IH]; intros used argsr used' Hexpr Hrename;
    simpl in Hrename.
  - injection Hrename as <- _. simpl. constructor.
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
    injection Hrename as <- _.
    simpl.
    eapply NoDup_app_from_Forall.
    + eapply Hexpr.
      * left. reflexivity.
      * exact Harg.
    + eapply IH.
      * intros used0 e er0 used_tail Hin_rest Hrename0.
        eapply Hexpr.
        -- right. exact Hin_rest.
        -- exact Hrename0.
      * exact Hrest.
    + eapply Forall_not_in_app_of_used with (used := used1).
      * intros x Hin.
        eapply alpha_rename_expr_local_store_names_in_used.
        -- exact Harg.
        -- exact Hin.
      * eapply alpha_rename_call_args_local_store_names_fresh_used.
        -- intros used0 e er0 used_tail Hin_rest Hrename0.
           eapply alpha_rename_expr_local_store_names_fresh_used.
           exact Hrename0.
        -- exact Hrest.
Qed.

Lemma alpha_rename_struct_fields_local_store_names_nodup :
  forall ρ used fields fieldsr used',
    (forall used0 fname e er used1,
        In (fname, e) fields ->
        alpha_rename_expr ρ used0 e = (er, used1) ->
        NoDup (expr_local_store_names er)) ->
    ((fix go (used0 : list ident) (fields0 : list (string * expr))
        : list (string * expr) * list ident :=
        match fields0 with
        | [] => ([], used0)
        | (fname, e) :: rest =>
            let (e', used1) := alpha_rename_expr ρ used0 e in
            let (rest', used2) := go used1 rest in
            ((fname, e') :: rest', used2)
        end) used fields) = (fieldsr, used') ->
    NoDup (fields_local_store_names fieldsr).
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname e] rest IH]; intros used fieldsr used' Hexpr Hrename;
    simpl in Hrename.
  - injection Hrename as <- _. simpl. constructor.
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
    injection Hrename as <- _.
    simpl.
    eapply NoDup_app_from_Forall.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + eapply IH.
      * intros used0 fname0 e0 er0 used_tail Hin_rest Hrename0.
        eapply Hexpr.
        -- right. exact Hin_rest.
        -- exact Hrename0.
      * exact Hrest.
    + eapply Forall_not_in_app_of_used with (used := used1).
      * intros x Hin.
        eapply alpha_rename_expr_local_store_names_in_used.
        -- exact He.
        -- exact Hin.
      * eapply alpha_rename_struct_fields_local_store_names_fresh_used.
        -- intros used0 fname0 e0 er0 used_tail Hin_rest Hrename0.
           eapply alpha_rename_expr_local_store_names_fresh_used.
           exact Hrename0.
        -- exact Hrest.
Qed.

Lemma alpha_rename_match_branches_local_store_names_nodup :
  forall ρ used branches branchesr used',
    (forall ρ0 used0 name binders e er used1,
        In (name, binders, e) branches ->
        alpha_rename_expr ρ0 used0 e = (er, used1) ->
        NoDup (expr_local_store_names er)) ->
    ((fix go (used0 : list ident)
        (branches0 : list (string * list ident * expr))
        : list (string * list ident * expr) * list ident :=
        match branches0 with
        | [] => ([], used0)
        | (name, binders, e) :: rest =>
            let binder_seed := binders ++ free_vars_expr e ++ used0 in
            let '(binders', ρ_branch, used1) :=
              alpha_rename_idents ρ binder_seed binders in
            let (e', used2) := alpha_rename_expr ρ_branch used1 e in
            let (rest', used3) := go used2 rest in
            ((name, binders', e') :: rest', used3)
        end) used branches) = (branchesr, used') ->
    NoDup (match_branches_local_store_names branchesr).
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name binders] e] rest IH];
    intros used branchesr used' Hexpr Hrename; simpl in Hrename.
	  - injection Hrename as <- _. simpl. constructor.
	  - set (binder_seed := binders ++ free_vars_expr e ++ used).
	    destruct (alpha_rename_idents ρ binder_seed binders)
	      as [[bindersr ρ_branch] used1] eqn:Hbinders.
	    destruct (alpha_rename_expr ρ_branch used1 e) as [er used2] eqn:He.
	    destruct ((fix go (used0 : list ident)
	          (branches0 : list (string * list ident * expr))
	          : list (string * list ident * expr) * list ident :=
	          match branches0 with
	          | [] => ([], used0)
	          | (name0, binders0, e0) :: rest0 =>
	              let '(binders0', ρ_branch0, used3) :=
	                alpha_rename_idents ρ
	                  (binders0 ++ free_vars_expr e0 ++ used0) binders0 in
	              let (e0', used4) := alpha_rename_expr ρ_branch0 used3 e0 in
	              let (rest', used5) := go used4 rest0 in
	              ((name0, binders0', e0') :: rest', used5)
	          end) used2 rest) as [restr used3] eqn:Hrest.
	    subst binder_seed.
	    simpl in Hrename.
	    rewrite Hbinders in Hrename.
	    rewrite He in Hrename.
	    rewrite Hrest in Hrename.
	    injection Hrename as <- _.
	    simpl.
	    eapply NoDup_app_from_Forall.
	    + eapply alpha_rename_idents_outputs_nodup. exact Hbinders.
	    + eapply NoDup_app_from_Forall.
	      * eapply (Hexpr ρ_branch used1 name binders e er used2).
	        -- left. reflexivity.
	        -- exact He.
	      * eapply IH.
	        -- intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin_rest Hrename0.
	           eapply (Hexpr ρ0 used0 name0 binders0 e0 er0 used_tail).
	           ++ right. exact Hin_rest.
	           ++ exact Hrename0.
	        -- exact Hrest.
	      * eapply Forall_not_in_app_of_used with (used := used2).
	        -- intros x Hin.
	           eapply alpha_rename_expr_local_store_names_in_used.
	           ++ exact He.
	           ++ exact Hin.
	        -- eapply alpha_rename_match_branches_local_store_names_fresh_used.
	           ++ intros ρ0 used0 name0 binders0 e0 er0 used_tail
	                Hin_rest Hrename0.
	              eapply alpha_rename_expr_local_store_names_fresh_used.
	              exact Hrename0.
	           ++ exact Hrest.
	    + eapply Forall_not_in_app_of_used with (used := used1).
	      * intros x Hin.
	        eapply alpha_rename_idents_outputs_in_used.
	        -- exact Hbinders.
	        -- exact Hin.
	      * apply Forall_app. split.
	        -- eapply alpha_rename_expr_local_store_names_fresh_used.
	           exact He.
	        -- eapply Forall_fresh_weaken.
	           ++ intros x Hin.
	              eapply alpha_rename_expr_used_extends.
	              ** exact He.
	              ** exact Hin.
	           ++ eapply alpha_rename_match_branches_local_store_names_fresh_used.
	              ** intros ρ0 used0 name0 binders0 e0 er0 used_tail
	                   Hin_rest Hrename0.
	                 eapply alpha_rename_expr_local_store_names_fresh_used.
	                 exact Hrename0.
	              ** exact Hrest.
Qed.

Lemma alpha_rename_expr_local_store_names_nodup :
  forall rho used e er used',
    alpha_rename_expr rho used e = (er, used') ->
    NoDup (expr_local_store_names er).
Proof.
  assert (Hsize : forall n rho used e er used',
    expr_size e < n ->
    alpha_rename_expr rho used e = (er, used') ->
    NoDup (expr_local_store_names er)).
  {
  induction n as [| n IH]; intros rho used e er used' Hlt Hrename.
  - lia.
  - destruct e; simpl in Hrename.
    + injection Hrename as <- _. simpl. constructor.
    + injection Hrename as <- _. simpl. constructor.
    + injection Hrename as <- _. simpl. constructor.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: rho)
        (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
         i :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      injection Hrename as <- _.
      simpl.
      eapply NoDup_app_from_Forall.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
        -- exact He1.
      * constructor.
        -- intro Hin.
           pose proof (alpha_rename_expr_local_store_names_fresh_used
             _ _ _ _ _ He2) as Hfresh_e2.
           rewrite Forall_forall in Hfresh_e2.
           specialize (Hfresh_e2 _ Hin).
           apply Hfresh_e2. simpl. left. reflexivity.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
           ++ exact He2.
      * apply Forall_forall. intros x Hx Hin.
        destruct Hin as [Heq | Hin].
        -- subst.
           apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
           right. apply in_or_app. right.
           eapply alpha_rename_expr_local_store_names_in_used.
           ++ exact He1.
           ++ exact Hx.
        -- pose proof (alpha_rename_expr_local_store_names_fresh_used
             _ _ _ _ _ He2) as Hfresh_e2.
           rewrite Forall_forall in Hfresh_e2.
           specialize (Hfresh_e2 _ Hin).
           apply Hfresh_e2. simpl. right. right.
           apply in_or_app. right.
           eapply alpha_rename_expr_local_store_names_in_used.
           ++ exact He1.
           ++ exact Hx.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((i, fresh_ident i (i :: free_vars_expr e2 ++ used1)) :: rho)
        (fresh_ident i (i :: free_vars_expr e2 ++ used1) ::
         i :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      injection Hrename as <- _.
      simpl.
      eapply NoDup_app_from_Forall.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
        -- exact He1.
      * constructor.
        -- intro Hin.
           pose proof (alpha_rename_expr_local_store_names_fresh_used
             _ _ _ _ _ He2) as Hfresh_e2.
           rewrite Forall_forall in Hfresh_e2.
           specialize (Hfresh_e2 _ Hin).
           apply Hfresh_e2. simpl. left. reflexivity.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
           ++ exact He2.
      * apply Forall_forall. intros x Hx Hin.
        destruct Hin as [Heq | Hin].
        -- subst.
           apply (fresh_ident_not_in i (i :: free_vars_expr e2 ++ used1)).
           right. apply in_or_app. right.
           eapply alpha_rename_expr_local_store_names_in_used.
           ++ exact He1.
           ++ exact Hx.
        -- pose proof (alpha_rename_expr_local_store_names_fresh_used
             _ _ _ _ _ He2) as Hfresh_e2.
           rewrite Forall_forall in Hfresh_e2.
           specialize (Hfresh_e2 _ Hin).
           apply Hfresh_e2. simpl. right. right.
           apply in_or_app. right.
	           eapply alpha_rename_expr_local_store_names_in_used.
	           ++ exact He1.
	           ++ exact Hx.
	    + injection Hrename as <- _. simpl. constructor.
	    + injection Hrename as <- _. simpl. constructor.
	    + injection Hrename as <- _. simpl. constructor.
	    + remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used l) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call.
      eapply alpha_rename_call_args_local_store_names_nodup.
      * intros used0 e er0 used1 Hin_arg Hrename0.
        eapply IH.
        -- pose proof (expr_size_call_arg_lt i l e Hin_arg) as Harg_lt.
           assert (expr_size e < n) as Hlt_arg by lia. exact Hlt_arg.
        -- exact Hrename0.
      * symmetry. exact Hargs.
    + remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used l0) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call_generic.
      eapply alpha_rename_call_args_local_store_names_nodup.
      * intros used0 e er0 used1 Hin_arg Hrename0.
        eapply IH.
        -- pose proof (expr_size_call_generic_arg_lt i l l0 e Hin_arg)
             as Harg_lt.
           assert (expr_size e < n) as Hlt_arg by lia. exact Hlt_arg.
        -- exact Hrename0.
      * symmetry. exact Hargs.
    + destruct (alpha_rename_expr rho used e) as [callee_r used0] eqn:Hcallee.
      remember
        ((fix go (used0 : list ident) (args0 : list expr)
            : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1') := alpha_rename_expr rho used0 arg in
                let (rest', used2) := go used1' rest in
                (arg' :: rest', used2)
            end) used0 l) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call_expr.
      eapply NoDup_app_from_Forall.
      * eapply IH.
        -- pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
           assert (expr_size e < n) as Hlt_callee by lia. exact Hlt_callee.
        -- exact Hcallee.
      * eapply alpha_rename_call_args_local_store_names_nodup.
        -- intros used_arg earg er0 used_tail Hin_arg Hrename0.
           eapply IH.
           ++ pose proof (expr_size_callexpr_arg_lt e l earg Hin_arg) as Harg_lt.
              assert (expr_size earg < n) as Hlt_arg by lia. exact Hlt_arg.
           ++ exact Hrename0.
        -- symmetry. exact Hargs.
      * eapply Forall_not_in_app_of_used with (used := used0).
        -- intros x Hin.
           eapply alpha_rename_expr_local_store_names_in_used.
           ++ exact Hcallee.
           ++ exact Hin.
        -- eapply alpha_rename_call_args_local_store_names_fresh_used.
           ++ intros used_arg earg er0 used_tail Hin_arg Hrename0.
              eapply alpha_rename_expr_local_store_names_fresh_used.
              exact Hrename0.
           ++ symmetry. exact Hargs.
    + remember
        ((fix go (used0 : list ident) (fields0 : list (string * expr))
            : list (string * expr) * list ident :=
            match fields0 with
            | [] => ([], used0)
            | (fname, e0) :: rest =>
                let (e0', used1) := alpha_rename_expr rho used0 e0 in
                let (rest', used2) := go used1 rest in
                ((fname, e0') :: rest', used2)
            end) used l1) as r eqn:Hfields.
      destruct r as [fieldsr used_fields].
      injection Hrename as <- _.
      rewrite expr_local_store_names_struct.
      eapply alpha_rename_struct_fields_local_store_names_nodup.
      * intros used0 fname efield er0 used1 Hin_field Hrename0.
        eapply IH.
        -- pose proof (expr_size_struct_field_lt s l l0 l1 fname efield Hin_field) as Hfield_lt.
           assert (expr_size efield < n) as Hlt_field by lia. exact Hlt_field.
        -- exact Hrename0.
      * symmetry. exact Hfields.
    + remember
        ((fix go (used0 : list ident) (payloads0 : list expr)
            : list expr * list ident :=
            match payloads0 with
            | [] => ([], used0)
            | e0 :: rest =>
                let (e0', used1) := alpha_rename_expr rho used0 e0 in
                let (rest', used2) := go used1 rest in
                (e0' :: rest', used2)
            end) used l1) as r eqn:Hpayloads.
      destruct r as [payloadsr used_payloads].
      injection Hrename as <- _.
      rewrite expr_local_store_names_enum.
      eapply alpha_rename_call_args_local_store_names_nodup.
      * intros used0 epayload er0 used1 Hin_payload Hrename0.
        eapply IH.
        -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 epayload Hin_payload)
             as Hpayload_lt.
           assert (expr_size epayload < n) as Hlt_payload by lia. exact Hlt_payload.
        -- exact Hrename0.
      * symmetry. exact Hpayloads.
	    + destruct (alpha_rename_expr rho used e) as [scrutr used0] eqn:Hscrut.
		      remember
		        ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
		            : list (string * list ident * expr) * list ident :=
		            match branches0 with
		            | [] => ([], used0)
		            | (variant_name, binders, e0) :: rest =>
		                let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
		                let '(binders', ρ_branch, used1) :=
		                  alpha_rename_idents rho binder_seed binders in
		                let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
		                let (rest', used3) := go used2 rest in
		                ((variant_name, binders', e0') :: rest', used3)
		            end) used0 l) as r eqn:Hbranches.
	      destruct r as [branchesr used_branches].
	      inversion Hrename; subst; clear Hrename. simpl.
	      eapply NoDup_app_from_Forall.
	      * eapply IH.
	        -- pose proof (expr_size_match_scrutinee_lt e l) as Hscrut_lt.
	           assert (expr_size e < n) as Hlt_scrut by lia. exact Hlt_scrut.
	        -- exact Hscrut.
		      * eapply alpha_rename_match_branches_local_store_names_nodup.
		        -- intros rho_branch used_branch variant_name binders ebranch er0 used_tail
	              Hin_branch Hrename0.
		           eapply IH.
	           ++ pose proof (expr_size_match_branch_lt e l variant_name binders ebranch Hin_branch)
	                as Hbranch_lt.
	              assert (expr_size ebranch < n) as Hlt_branch by lia. exact Hlt_branch.
	           ++ exact Hrename0.
	        -- symmetry. exact Hbranches.
	      * eapply Forall_not_in_app_of_used with (used := used0).
	        -- intros x Hin.
	           eapply alpha_rename_expr_local_store_names_in_used.
	           ++ exact Hscrut.
	           ++ exact Hin.
		        -- eapply alpha_rename_match_branches_local_store_names_fresh_used.
		           ++ intros rho_branch used_branch variant_name binders ebranch er0 used_tail
	                 Hin_branch Hrename0.
	              eapply alpha_rename_expr_local_store_names_fresh_used.
	              exact Hrename0.
	           ++ symmetry. exact Hbranches.
	    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
	      injection Hrename as <- _.
	      simpl.
	      eapply IH.
	      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
	      * exact He.
	    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
	      injection Hrename as <- _.
	      simpl.
	      eapply IH.
	      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
	      * exact He.
    + injection Hrename as <- _. simpl. constructor.
    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
      injection Hrename as <- _.
      simpl.
      eapply IH.
      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
      * exact He.
    + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
      injection Hrename as <- _.
      simpl.
      eapply IH.
      * simpl in Hlt. assert (expr_size e < n) as Hlt_e by lia. exact Hlt_e.
      * exact He.
    + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
      destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
      injection Hrename as <- _.
      simpl.
      eapply NoDup_app_from_Forall.
      * eapply IH.
        -- simpl in Hlt. assert (expr_size e1 < n) as Hlt_e1 by lia. exact Hlt_e1.
        -- exact He1.
      * eapply NoDup_app_from_Forall.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e2 < n) as Hlt_e2 by lia. exact Hlt_e2.
           ++ exact He2.
        -- eapply IH.
           ++ simpl in Hlt. assert (expr_size e3 < n) as Hlt_e3 by lia. exact Hlt_e3.
           ++ exact He3.
        -- eapply Forall_not_in_app_of_used with (used := used2).
           ++ intros x Hin.
              eapply alpha_rename_expr_local_store_names_in_used.
              ** exact He2.
              ** exact Hin.
           ++ eapply alpha_rename_expr_local_store_names_fresh_used.
              exact He3.
      * eapply Forall_not_in_app_of_used with (used := used1).
        -- intros x Hin.
           eapply alpha_rename_expr_local_store_names_in_used.
           ++ exact He1.
           ++ exact Hin.
        -- apply Forall_app. split.
           ++ eapply alpha_rename_expr_local_store_names_fresh_used.
              exact He2.
           ++ eapply Forall_fresh_weaken.
              ** intros x Hin.
                 eapply alpha_rename_expr_used_extends.
                 --- exact He2.
                 --- exact Hin.
              ** eapply alpha_rename_expr_local_store_names_fresh_used.
                 exact He3.
  }
  intros rho used e er used' Hrename.
  eapply (Hsize (S (expr_size e))).
  - apply Nat.lt_succ_diag_r.
  - exact Hrename.
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

Lemma ctx_names_app : forall Γ Δ,
  ctx_names (Γ ++ Δ) = ctx_names Γ ++ ctx_names Δ.
Proof.
  induction Γ as [| [[[x T] st] m] Γ IH]; intros Δ.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma params_ctx_app : forall ps qs,
  params_ctx (ps ++ qs) = params_ctx ps ++ params_ctx qs.
Proof.
  induction ps as [| p ps IH]; intros qs.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma alpha_rename_params_ctx_alpha_tail :
  forall used ps psr ρ used' Γ,
    alpha_rename_params [] used ps = (psr, ρ, used') ->
    (forall x, In x (ctx_names Γ) -> In x used) ->
    ctx_alpha ρ (params_ctx ps ++ Γ) (params_ctx psr ++ Γ).
Proof.
  intros used ps.
  revert used.
  induction ps as [| p ps IH]; intros used psr ρ used' Γ Hrename HΓ_used.
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
    + eapply IH.
      * exact Hps.
      * intros x Hin. right. apply HΓ_used. exact Hin.
    + rewrite ctx_names_app. intro Hin.
      apply in_app_or in Hin as [Hin_ps | Hin_Γ].
      * eapply alpha_rename_params_names_fresh_used.
        -- exact Hps.
        -- exact Hin_ps.
        -- left. reflexivity.
      * apply (fresh_ident_not_in xp used).
        apply HΓ_used. exact Hin_Γ.
	    + intro Hin.
	      destruct (alpha_rename_params_range_ctx_or_tail
	        _ _ _ _ _ _ Hps _ Hin) as [Hctx | Htail].
	      * eapply alpha_rename_params_names_fresh_used.
	        -- exact Hps.
	        -- exact Hctx.
	        -- left. reflexivity.
	      * simpl in Htail. contradiction.
Qed.

Lemma alpha_rename_params_ctx_alpha_extend_tail :
  forall ρ used ps psr ρ' used' Γ Γr,
    alpha_rename_params ρ used ps = (psr, ρ', used') ->
    ctx_alpha ρ Γ Γr ->
    (forall x, In x (ctx_names Γr) -> In x used) ->
    (forall x, In x (rename_range ρ) -> In x used) ->
    ctx_alpha ρ' (params_ctx ps ++ Γ) (params_ctx psr ++ Γr).
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Γ Γr
    Hrename Hctx HΓ_used Hρ_used.
  - simpl in Hrename. inversion Hrename; subst.
    simpl. exact Hctx.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst; clear Hrename.
    simpl.
    constructor.
    + eapply IH.
      * exact Hps.
      * exact Hctx.
      * intros y Hy. right. apply HΓ_used. exact Hy.
      * intros y Hy. right. apply Hρ_used. exact Hy.
    + intro Hin.
      rewrite ctx_names_app in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply alpha_rename_params_names_fresh_used.
        -- exact Hps.
        -- exact Hin.
        -- left. reflexivity.
      * eapply fresh_ident_not_in.
        apply HΓ_used. exact Hin.
    + intro Hin.
      destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _ Hps _ Hin)
        as [Hin_params | Hin_range].
      * eapply alpha_rename_params_names_fresh_used.
        -- exact Hps.
        -- exact Hin_params.
        -- left. reflexivity.
      * eapply fresh_ident_not_in.
        apply Hρ_used. exact Hin_range.
Qed.

Lemma alpha_rename_params_ctx_alpha_remove :
  forall ρ used ps psr ρ' used' Γ Γr,
    alpha_rename_params ρ used ps = (psr, ρ', used') ->
    ctx_alpha ρ' Γ Γr ->
    ctx_alpha ρ (ctx_remove_params ps Γ) (ctx_remove_params psr Γr).
Proof.
  intros ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Γ Γr
    Hrename Hctx.
  - simpl in Hrename. inversion Hrename; subst.
    simpl. exact Hctx.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst; clear Hrename.
    simpl.
    eapply IH.
    + exact Hps.
    + eapply ctx_alpha_remove_bound. exact Hctx.
Qed.

Lemma alpha_rename_params_ctx_alpha_stable_tail :
  forall used ps caps psr ρ used',
    alpha_rename_params []
      (param_names ps ++ param_names caps ++ used) ps =
      (psr, ρ, used') ->
    ctx_alpha ρ
      (params_ctx (ps ++ caps)) (params_ctx (psr ++ caps)).
Proof.
  intros used ps caps psr ρ used' Hrename.
  repeat rewrite params_ctx_app.
  eapply alpha_rename_params_ctx_alpha_tail.
  - exact Hrename.
  - intros x Hin.
    rewrite params_ctx_names_param_names in Hin.
    apply in_or_app. right. apply in_or_app. left. exact Hin.
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

Lemma ident_in_b_not_in_false_alpha : forall x xs,
  ~ In x xs ->
  ident_in_b x xs = false.
Proof.
  intros x xs Hnotin.
  induction xs as [| y ys IH].
  - reflexivity.
  - simpl in Hnotin |- *.
    apply orb_false_iff. split.
    + apply ident_eqb_neq. intro Heq. apply Hnotin. left. symmetry. exact Heq.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma ident_nodup_b_complete_alpha : forall xs,
  NoDup xs ->
  ident_nodup_b xs = true.
Proof.
  induction xs as [| x xs IH]; intros Hnodup.
  - reflexivity.
  - inversion Hnodup; subst. simpl.
    rewrite ident_in_b_not_in_false_alpha by assumption.
    simpl. apply IH. assumption.
Qed.

Lemma params_names_nodup_b_complete_alpha : forall ps,
  NoDup (ctx_names (params_ctx ps)) ->
  params_names_nodup_b ps = true.
Proof.
  intros ps Hnodup.
  unfold params_names_nodup_b.
  apply ident_nodup_b_complete_alpha. exact Hnodup.
Qed.

Lemma ctx_lookup_state_not_in_names_none : forall Γ x,
  ~ In x (ctx_names Γ) ->
  ctx_lookup_state x Γ = None.
Proof.
  induction Γ as [| [[[y T] st] m] Γ IH]; intros x Hnotin.
  - reflexivity.
  - simpl in Hnotin |- *.
    destruct (ident_eqb x y) eqn:Hxy.
    + apply ident_eqb_eq in Hxy. subst.
      exfalso. apply Hnotin. left. reflexivity.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma ctx_lookup_params_none_b_fresh_used : forall ps Γ used,
  (forall x, In x (ctx_names Γ) -> In x used) ->
  Forall (fun x => ~ In x used) (ctx_names (params_ctx ps)) ->
  ctx_lookup_params_none_b ps Γ = true.
Proof.
  induction ps as [| [m x T] ps IH]; intros Γ used HΓ Hfresh.
  - reflexivity.
  - simpl in Hfresh |- *.
    inversion Hfresh; subst.
    rewrite ctx_lookup_state_not_in_names_none.
    + eapply IH.
      * exact HΓ.
      * exact H2.
    + intros Hin. apply H1. apply HΓ. exact Hin.
Qed.

Lemma ctx_lookup_state_in_names_some :
  forall Γ x,
    In x (ctx_names Γ) ->
    exists T st, ctx_lookup_state x Γ = Some (T, st).
Proof.
  induction Γ as [| [[[y T] st] m] Γ IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst x. rewrite ident_eqb_refl. eauto.
    + destruct (ident_eqb x y) eqn:Hxy.
      * eauto.
      * apply IH. exact Hin.
Qed.

Lemma ctx_lookup_params_none_b_not_in_names :
  forall ps Γ x,
    ctx_lookup_params_none_b ps Γ = true ->
    In x (ctx_names (params_ctx ps)) ->
    ~ In x (ctx_names Γ).
Proof.
  induction ps as [| [m y T] ps IH]; intros Γ x Hfresh Hin Hctx; simpl in *.
  - contradiction.
  - destruct (ctx_lookup_state y Γ) as [[Ty st] |] eqn:Hlookup;
      try discriminate.
    destruct Hin as [Heq | Hin].
    + subst x.
      destruct (ctx_lookup_state_in_names_some Γ y Hctx)
        as [Ty' [st' Hsome]].
      rewrite Hlookup in Hsome. discriminate.
    + eapply IH; eassumption.
Qed.

Lemma alpha_rename_params_params_ok_sctx_b_forward_gen :
  forall env ρ used ps psr ρ' used' Σ Σr,
    alpha_rename_params ρ used ps = (psr, ρ', used') ->
    NoDup (param_names ps) ->
    (forall x, In x (param_names ps) -> In x used) ->
    (forall x, In x (rename_range ρ) -> In x used) ->
    ctx_alpha ρ' Σ Σr ->
    params_ok_sctx_b env ps Σ = true ->
    params_ok_sctx_b env psr Σr = true.
Proof.
  intros env ρ used ps.
  revert ρ used.
  induction ps as [| p ps IH]; intros ρ used psr ρ' used' Σ Σr
    Hrename Hnodup Hused Hrange_used Halpha Hparams.
  - simpl in Hrename. inversion Hrename; subst.
    exact Hparams.
  - destruct p as [m xp T].
    simpl in Hrename.
    destruct (alpha_rename_params ρ (fresh_ident xp used :: used) ps)
      as [[ps0 ρ0] used0] eqn:Hps.
    inversion Hrename; subst. simpl in Hparams.
    inversion Hnodup as [| ? ? Hxp_notin Hnodup_tail]; subst.
    inversion Halpha as [| ? Γ Γr ? xr Tctx stctx mctx Halpha_tail
      Hfresh_ctx Hfresh_range]; subst.
    simpl.
    apply andb_true_iff in Hparams as [Hhead Htail_full].
    assert (Hxp_used : In xp used).
    { apply Hused. simpl. left. reflexivity. }
    assert (Hhead_r :
      sctx_check_ok env (fresh_ident xp used) T
        ((fresh_ident xp used, Tctx, stctx, mctx) :: Γr) = true).
    { unfold sctx_check_ok, sctx_lookup in *.
      destruct (ty_usage T); try reflexivity.
      simpl in Hhead |- *.
      rewrite ident_eqb_refl in Hhead |- *.
      exact Hhead. }
    rewrite Hhead_r.
    rewrite (params_ok_sctx_b_cons_notin env ps0 (fresh_ident xp used)
      Tctx stctx mctx Γr).
    + eapply IH.
      * exact Hps.
      * exact Hnodup_tail.
      * intros x Hin. simpl. right. apply Hused. simpl. right. exact Hin.
      * intros x Hin. simpl. right. apply Hrange_used. exact Hin.
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
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  injection Hrename as _ <-.
  eapply alpha_rename_expr_used_extends.
  - exact Hbody.
  - eapply alpha_rename_params_used_extends.
    + exact Hps.
    + apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. right. exact Hin.
Qed.

Lemma alpha_rename_fn_def_params_fresh_used : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  forall x, In x (ctx_names (params_ctx (fn_params fr))) -> ~ In x used.
Proof.
  intros used f fr used' Hrename x Hin Hused.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl in Hin.
  eapply alpha_rename_params_names_fresh_used.
  - exact Hps.
  - exact Hin.
  - apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right. exact Hused.
Qed.

Lemma alpha_rename_fn_def_body_local_store_names_fresh_used :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    Forall (fun x => ~ In x used) (expr_local_store_names (fn_body fr)).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  eapply Forall_fresh_weaken.
  - intros x Hin.
    eapply alpha_rename_params_used_extends.
    + exact Hps.
    + apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. right. exact Hin.
  - eapply alpha_rename_expr_local_store_names_fresh_used.
    exact Hbody.
Qed.

Lemma alpha_rename_fn_def_body_local_store_names_fresh_params :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    Forall
      (fun x => ~ In x (ctx_names (params_ctx (fn_params fr))))
      (expr_local_store_names (fn_body fr)).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  pose proof (alpha_rename_expr_local_store_names_fresh_used
    ρ used1 body bodyr used2 Hbody) as Hfresh.
  inversion Hrename; subst. simpl.
  simpl in Hfresh.
  induction Hfresh as [| x xs Hnotin Hfresh IH].
  - constructor.
  - constructor.
    + intro Hin.
      apply Hnotin.
      eapply alpha_rename_params_names_in_used.
      * exact Hps.
      * exact Hin.
    + exact IH.
Qed.

Lemma alpha_rename_fn_def_params_nodup : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  NoDup (ctx_names (params_ctx (fn_params fr))).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  eapply alpha_rename_params_names_nodup. exact Hps.
Qed.

Lemma alpha_rename_fn_def_body_local_store_names_nodup :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (expr_local_store_names (fn_body fr)).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  eapply alpha_rename_expr_local_store_names_nodup. exact Hbody.
Qed.

Lemma alpha_rename_fn_def_params_body_local_store_names_nodup :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup
      (ctx_names (params_ctx (fn_params fr)) ++
       expr_local_store_names (fn_body fr)).
Proof.
  intros used f fr used' Hrename.
  eapply NoDup_app_from_Forall.
  - eapply alpha_rename_fn_def_params_nodup. exact Hrename.
  - eapply alpha_rename_fn_def_body_local_store_names_nodup. exact Hrename.
  - pose proof (alpha_rename_fn_def_body_local_store_names_fresh_params
      used f fr used' Hrename) as Hfresh.
    rewrite Forall_forall in Hfresh.
    apply Forall_forall. intros x Hin_params Hin_body.
    eapply Hfresh.
    + exact Hin_body.
    + exact Hin_params.
Qed.

Lemma alpha_rename_fn_def_params_ctx_alpha : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  exists ρ, ctx_alpha ρ
    (params_ctx (fn_params f)) (params_ctx (fn_params fr)).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  exists ρ.
  eapply alpha_rename_params_ctx_alpha_nil. exact Hps.
Qed.

Lemma alpha_rename_fn_def_captures : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  fn_captures fr = fn_captures f.
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. reflexivity.
Qed.

Lemma alpha_rename_fn_def_binding_params_ctx_alpha : forall used f fr used',
  alpha_rename_fn_def used f = (fr, used') ->
  exists ρ, ctx_alpha ρ
    (params_ctx (fn_params f ++ fn_captures f))
    (params_ctx (fn_params fr ++ fn_captures fr)).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  inversion Hrename; subst. simpl.
  exists ρ.
  eapply alpha_rename_params_ctx_alpha_stable_tail. exact Hps.
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
  + remember
      ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr ρ used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used l0) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as <- _.
    constructor.
    eapply alpha_rename_call_args_sound.
    * intros used0 e er0 used1 Hin Hdisj0 Hrename0.
      eapply IH.
      -- pose proof (expr_size_call_generic_arg_lt i l l0 e Hin)
           as Harg_lt.
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
		  + remember
		      ((fix go (used0 : list ident) (payloads0 : list expr)
		          : list expr * list ident :=
		          match payloads0 with
		          | [] => ([], used0)
		          | e0 :: rest =>
		              let (e0', used1) := alpha_rename_expr ρ used0 e0 in
		              let (rest', used2) := go used1 rest in
		              (e0' :: rest', used2)
		          end) used l1) as r eqn:Hpayloads.
		    destruct r as [payloadsr used_payloads].
		    injection Hrename as <- _.
		    apply EA_Enum.
		    eapply alpha_rename_call_args_sound.
		    * intros used0 epayload er0 used1 Hin Hdisj0 Hrename0.
		      eapply IH.
		      -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 epayload Hin)
		           as Hpayload_lt.
		         assert (expr_size epayload < n) as Hlt_payload by lia.
		         exact Hlt_payload.
		      -- exact Hdisj0.
		      -- exact Hrename0.
			    * exact Hdisj.
			    * symmetry. exact Hpayloads.
			  + destruct (alpha_rename_expr ρ used e) as [scrutr used0] eqn:Hscrut.
			    remember
			      ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
			          : list (string * list ident * expr) * list ident :=
				          match branches0 with
				          | [] => ([], used0)
				          | (variant_name, binders, e0) :: rest =>
				              let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
				              let '(binders', ρ_branch, used1) :=
				                alpha_rename_idents ρ binder_seed binders in
				              let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
				              let (rest', used3) := go used2 rest in
				              ((variant_name, binders', e0') :: rest', used3)
				          end) used0 l) as r eqn:Hbranches.
			    destruct r as [branchesr used_branches].
			    injection Hrename as <- _.
			    apply EA_Match.
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
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in H.
  simpl in H.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[ps' ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [body' used2] eqn:Hbody.
  inversion H; subst.
  unfold same_fn_shape. simpl.
  split; [reflexivity |].
  split; [reflexivity |].
  eapply alpha_rename_params_shape. exact Hps.
Qed.

Lemma alpha_rename_fn_def_static_fields :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    fn_name fr = fn_name f /\
    fn_lifetimes fr = fn_lifetimes f /\
    fn_outlives fr = fn_outlives f /\
    fn_captures fr = fn_captures f /\
    fn_ret fr = fn_ret f /\
    fn_type_params fr = fn_type_params f /\
    fn_bounds fr = fn_bounds f.
Proof.
  intros used f fr used' H.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in H. simpl in H.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[ps' rho] used1] eqn:Hps.
  destruct (alpha_rename_expr rho used1 body) as [body' used2] eqn:Hbody.
  inversion H; subst. simpl.
  repeat split; reflexivity.
Qed.

Lemma alpha_rename_fn_def_initial_root_env_rename :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params f))) ->
    exists rho used_params,
      alpha_rename_params []
        (param_names (fn_params f) ++
         param_names (fn_captures f) ++ free_vars_expr (fn_body f) ++ used)
        (fn_params f) = (fn_params fr, rho, used_params) /\
      root_env_rename rho (initial_root_env_for_fn f) =
        initial_root_env_for_params_origin (fn_params f) (fn_params fr).
Proof.
  intros used f fr used' Hrename Hnodup.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename.
  simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[ps' rho] used_params] eqn:Hps.
  destruct (alpha_rename_expr rho used_params body)
    as [body' used_body] eqn:Hbody.
  inversion Hrename; subst. simpl.
  exists rho, used_params.
  split; [exact Hps |].
  unfold initial_root_env_for_fn. simpl.
  eapply alpha_rename_params_initial_root_env_rename; eassumption.
Qed.

Lemma alpha_rename_fn_def_params_body :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    exists rho used_params,
      alpha_rename_params []
        (param_names (fn_params f) ++
         param_names (fn_captures f) ++ free_vars_expr (fn_body f) ++ used)
        (fn_params f) = (fn_params fr, rho, used_params) /\
      alpha_rename_expr rho used_params (fn_body f) =
        (fn_body fr, used').
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename.
  simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[ps' rho] used_params] eqn:Hps.
  destruct (alpha_rename_expr rho used_params body)
    as [body' used_body] eqn:Hbody.
  inversion Hrename; subst. simpl.
  exists rho, used_params.
  split; [exact Hps | exact Hbody].
Qed.

Lemma alpha_rename_fn_def_params_body_facts :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
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
      (forall x,
        In x (ctx_names
          (sctx_of_ctx (params_ctx (fn_params fr)))) ->
        In x used_params) /\
      (forall x, In x (rename_range rho) -> In x used_params) /\
      disjoint_names (free_vars_expr (fn_body f)) (rename_range rho).
Proof.
  intros used f fr used' Hrename.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename.
  simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr rho] used_params] eqn:Hps.
  destruct (alpha_rename_expr rho used_params body)
    as [bodyr used_body] eqn:Hbody.
  inversion Hrename; subst. simpl.
  exists rho, used_params.
  repeat split.
  - exact Hps.
  - exact Hbody.
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
    + apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. left. exact Hfree.
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

Lemma ctx_alpha_merge_many_forward :
  forall ρ Γ Γr tail tailr Γout,
    ctx_alpha ρ Γ Γr ->
    Forall2 (ctx_alpha ρ) tail tailr ->
    ctx_merge_many (ctx_of_sctx Γ) (map ctx_of_sctx tail) = Some Γout ->
    exists Γoutr,
      ctx_merge_many (ctx_of_sctx Γr) (map ctx_of_sctx tailr) = Some Γoutr /\
      ctx_alpha ρ Γout Γoutr.
Proof.
  intros ρ Γ Γr tail tailr Γout Hctx Htails Hmerge.
  revert Γ Γr Γout Hctx Hmerge.
  induction Htails as [|Σ Σr rest restr HΣ Hrest IH];
    intros Γ Γr Γout Hctx Hmerge.
  - simpl in Hmerge. inversion Hmerge; subst.
    exists Γr. split; [reflexivity | exact Hctx].
  - simpl in Hmerge.
    destruct (ctx_merge (ctx_of_sctx Γ) (ctx_of_sctx Σ)) as [Γm |] eqn:Hhead;
      try discriminate.
    destruct (ctx_alpha_merge_forward ρ Γ Γr Σ Σr Γm Hctx HΣ Hhead)
      as [Γmr [Hhead_r Hctx_m]].
    destruct (IH Γm Γmr Γout Hctx_m Hmerge)
      as [Γoutr [Htail_r Hctx_out]].
    exists Γoutr. simpl. unfold ctx_of_sctx in *. rewrite Hhead_r. split; assumption.
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

Lemma lookup_expr_branch_free_vars_in :
  forall x name branches e,
    lookup_expr_branch name branches = Some e ->
    In x (free_vars_expr e) ->
    In x ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
      match branches0 with
      | [] => []
      | (_, _, e0) :: rest => free_vars_expr e0 ++ go rest
      end) branches).
Proof.
  intros x name branches.
  induction branches as [|[[name0 binders0] e0] rest IH]; intros e Hlookup Hin;
    simpl in Hlookup.
  - discriminate.
  - simpl. destruct (String.eqb name name0) eqn:Hname.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma alpha_rename_expr_branches_lookup_exists_forward :
  forall ρ used branches branchesr used' name e,
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name0, binders0, e0) :: rest =>
          let binder_seed := binders0 ++ free_vars_expr e0 ++ used0 in
          let '(binders0', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders0 in
          let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
          let (rest', used3) := go used2 rest in
          ((name0, binders0', e0') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  lookup_expr_branch name branches = Some e ->
  exists ρ0 er used0 used1,
    lookup_expr_branch name branchesr = Some er /\
    alpha_rename_expr ρ0 used0 e = (er, used1) /\
    (forall x, In x used -> In x used0).
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name0 binders0] e0] rest IH];
    intros used branchesr used' name e Hrename Hlookup;
    simpl in Hrename, Hlookup.
  - discriminate.
  - set (binder_seed := binders0 ++ free_vars_expr e0 ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders0)
      as [[binders0r ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e0) as [e0r used2] eqn:He0.
    destruct ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used0)
          | (name1, binders1, e1) :: rest1 =>
              let '(binders1', ρ_branch1, used3) :=
                alpha_rename_idents ρ
                  (binders1 ++ free_vars_expr e1 ++ used0) binders1 in
              let (e1', used4) := alpha_rename_expr ρ_branch1 used3 e1 in
              let (rest', used5) := go used4 rest1 in
              ((name1, binders1', e1') :: rest', used5)
          end) used2 rest) as [restr used3] eqn:Hrest.
    subst binder_seed.
    simpl in Hrename.
    rewrite Hbinders in Hrename.
    rewrite He0 in Hrename.
    rewrite Hrest in Hrename.
    injection Hrename as <- <-.
    destruct (String.eqb name name0) eqn:Hname.
    + injection Hlookup as <-.
      exists ρ_branch, e0r, used1, used2. repeat split.
      * simpl. rewrite Hname. reflexivity.
      * exact He0.
      * intros x Hin.
        eapply alpha_rename_idents_used_extends.
        -- exact Hbinders.
        -- apply in_or_app. right. apply in_or_app. right. exact Hin.
    + destruct (IH used2 restr used3 name e Hrest Hlookup)
        as [ρ0 [er [used0 [used_tail [Hlookup_r [Hren Hused]]]]]].
      exists ρ0, er, used0, used_tail. repeat split.
      * simpl. rewrite Hname. exact Hlookup_r.
      * exact Hren.
      * intros x Hin. apply Hused.
        eapply alpha_rename_expr_used_extends; eauto.
        eapply alpha_rename_idents_used_extends.
        -- exact Hbinders.
        -- apply in_or_app. right. apply in_or_app. right. exact Hin.
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

Lemma lookup_expr_branch_in_alpha :
  forall name branches e,
    lookup_expr_branch name branches = Some e ->
    exists binders, In (name, binders, e) branches.
Proof.
  intros name branches.
  induction branches as [| [[name0 binders0] e0] rest IH]; intros e Hlookup;
    simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name name0) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name0.
      injection Hlookup as <-. exists binders0. left. reflexivity.
    + destruct (IH e Hlookup) as [binders Hin].
	      exists binders. right. exact Hin.
Qed.

Lemma lookup_expr_branch_binders_expr_in_alpha :
  forall name branches binders e,
    lookup_expr_branch_binders name branches = Some binders ->
    lookup_expr_branch name branches = Some e ->
    In (name, binders, e) branches.
Proof.
  intros name branches.
  induction branches as [| [[name0 binders0] e0] rest IH];
    intros binders e Hbinders Hexpr; simpl in Hbinders, Hexpr.
  - discriminate.
  - destruct (String.eqb name name0) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name0.
      injection Hbinders as <-.
      injection Hexpr as <-.
      left. reflexivity.
    + right. eapply IH; eassumption.
Qed.

Lemma lookup_expr_branch_snd_in_alpha :
  forall name branches e,
    lookup_expr_branch name branches = Some e ->
    In e (map snd branches).
Proof.
  intros name branches e Hlookup.
  destruct (lookup_expr_branch_in_alpha name branches e Hlookup) as [binders Hin].
  apply in_map with (f := snd) in Hin.
  simpl in Hin. exact Hin.
Qed.

Lemma alpha_rename_match_branches_lookup_exists_forward :
  forall ρ used branches branchesr used' name e,
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name0, binders0, e0) :: rest =>
          let binder_seed := binders0 ++ free_vars_expr e0 ++ used0 in
          let '(binders0', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders0 in
          let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
          let (rest', used3) := go used2 rest in
          ((name0, binders0', e0') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  lookup_expr_branch name branches = Some e ->
  exists ρ0 er used0 used1,
    lookup_expr_branch name branchesr = Some er /\
    alpha_rename_expr ρ0 used0 e = (er, used1) /\
    (forall x, In x used -> In x used0).
Proof.
  intros ρ used branches branchesr used' name e Hrename Hlookup.
  eapply alpha_rename_expr_branches_lookup_exists_forward; eauto.
Qed.

Lemma alpha_rename_match_branches_lookup_binders_forward :
  forall ρ used branches branchesr used' name,
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name0, binders0, e0) :: rest =>
          let binder_seed := binders0 ++ free_vars_expr e0 ++ used0 in
          let '(binders0', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders0 in
          let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
          let (rest', used3) := go used2 rest in
          ((name0, binders0', e0') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  lookup_expr_branch_binders name branches = Some [] ->
  lookup_expr_branch_binders name branchesr = Some [].
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name0 binders0] e0] rest IH];
    intros used branchesr used' name Hrename Hlookup;
    simpl in Hrename, Hlookup.
  - discriminate.
  - set (binder_seed := binders0 ++ free_vars_expr e0 ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders0)
      as [[binders0r ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e0) as [e0r used2] eqn:He0.
    destruct ((fix go (used0 : list ident)
          (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used0)
          | (name1, binders1, e1) :: rest1 =>
              let '(binders1', ρ_branch1, used3) :=
                alpha_rename_idents ρ
                  (binders1 ++ free_vars_expr e1 ++ used0) binders1 in
              let (e1', used4) := alpha_rename_expr ρ_branch1 used3 e1 in
              let (rest', used5) := go used4 rest1 in
              ((name1, binders1', e1') :: rest', used5)
          end) used2 rest) as [restr used3] eqn:Hrest.
    subst binder_seed.
    simpl in Hrename.
    rewrite Hbinders in Hrename.
    rewrite He0 in Hrename.
    rewrite Hrest in Hrename.
    injection Hrename as <- <-.
    destruct (String.eqb name name0) eqn:Hname.
    + simpl in Hlookup. injection Hlookup as Hbinders_empty.
      subst binders0.
      simpl in Hbinders. inversion Hbinders; subst; clear Hbinders.
      simpl. rewrite Hname. reflexivity.
    + simpl. rewrite Hname. eapply IH; eassumption.
Qed.

Lemma alpha_rename_match_branches_lookup_payload_forward :
  forall ρ used branches branchesr used' name binders e,
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name0, binders0, e0) :: rest =>
          let binder_seed := binders0 ++ free_vars_expr e0 ++ used0 in
          let '(binders0', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders0 in
          let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
          let (rest', used3) := go used2 rest in
          ((name0, binders0', e0') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  lookup_expr_branch_binders name branches = Some binders ->
  lookup_expr_branch name branches = Some e ->
  exists bindersr ρ0 er used_pre used_branch used_out,
    lookup_expr_branch_binders name branchesr = Some bindersr /\
    lookup_expr_branch name branchesr = Some er /\
    alpha_rename_idents ρ (binders ++ free_vars_expr e ++ used_pre) binders =
      (bindersr, ρ0, used_branch) /\
    alpha_rename_expr ρ0 used_branch e = (er, used_out) /\
    (forall x, In x used -> In x used_pre).
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name0 binders0] e0] rest IH];
    intros used branchesr used' name binders e Hrename Hbinders_lookup Hlookup;
    simpl in Hrename, Hbinders_lookup, Hlookup.
  - discriminate.
  - set (binder_seed := binders0 ++ free_vars_expr e0 ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders0)
      as [[binders0r ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e0) as [e0r used2] eqn:He0.
    destruct ((fix go (used0 : list ident)
          (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used0)
          | (name1, binders1, e1) :: rest1 =>
              let '(binders1', ρ_branch1, used3) :=
                alpha_rename_idents ρ
                  (binders1 ++ free_vars_expr e1 ++ used0) binders1 in
              let (e1', used4) := alpha_rename_expr ρ_branch1 used3 e1 in
              let (rest', used5) := go used4 rest1 in
              ((name1, binders1', e1') :: rest', used5)
          end) used2 rest) as [restr used3] eqn:Hrest.
    subst binder_seed.
    simpl in Hrename.
    rewrite Hbinders in Hrename.
    rewrite He0 in Hrename.
    rewrite Hrest in Hrename.
    injection Hrename as <- <-.
    destruct (String.eqb name name0) eqn:Hname.
    + injection Hbinders_lookup as <-.
      injection Hlookup as <-.
      exists binders0r, ρ_branch, e0r, used, used1, used2.
      repeat split.
      * simpl. rewrite Hname. reflexivity.
      * simpl. rewrite Hname. reflexivity.
      * exact Hbinders.
      * exact He0.
      * intros x Hin. exact Hin.
    + destruct (IH used2 restr used3 name binders e Hrest
        Hbinders_lookup Hlookup) as
        [bindersr [ρ0 [er [used_pre [used_branch [used_out
	          [Hbinders_r [Hlookup_r [Hids [Hren Hused_pre]]]]]]]]]].
      exists bindersr, ρ0, er, used_pre, used_branch, used_out.
      repeat split.
      * simpl. rewrite Hname. exact Hbinders_r.
      * simpl. rewrite Hname. exact Hlookup_r.
      * exact Hids.
      * exact Hren.
      * intros x Hin. apply Hused_pre.
        eapply alpha_rename_expr_used_extends.
        -- exact He0.
        -- eapply alpha_rename_idents_used_extends.
           ++ exact Hbinders.
           ++ apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma alpha_rename_match_branches_first_unknown_variant_branch :
  forall ρ used branches branchesr used' defs,
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name0, binders0, e0) :: rest =>
          let binder_seed := binders0 ++ free_vars_expr e0 ++ used0 in
          let '(binders0', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders0 in
          let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
          let (rest', used3) := go used2 rest in
          ((name0, binders0', e0') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  first_unknown_variant_branch branches defs = None ->
  first_unknown_variant_branch branchesr defs = None.
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name binders] e] rest IH]; intros used branchesr used' defs
    Hrename Hunknown; simpl in Hrename, Hunknown.
  - injection Hrename as <- <-. reflexivity.
  - set (binder_seed := binders ++ free_vars_expr e ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders)
      as [[bindersr ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e) as [er used2] eqn:Her.
    destruct ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
        : list (string * list ident * expr) * list ident :=
        match branches0 with
        | [] => ([], used0)
        | (name0, binders0, e0) :: rest0 =>
            let '(binders0', ρ_branch0, used3) :=
              alpha_rename_idents ρ
                (binders0 ++ free_vars_expr e0 ++ used0) binders0 in
            let (e0', used4) := alpha_rename_expr ρ_branch0 used3 e0 in
            let (rest', used5) := go used4 rest0 in
            ((name0, binders0', e0') :: rest', used5)
        end) used2 rest) as [restr used3] eqn:Hrest.
    subst binder_seed.
    simpl in Hrename.
    rewrite Hbinders in Hrename.
    rewrite Her in Hrename.
    rewrite Hrest in Hrename.
    injection Hrename as <- <-.
    simpl.
    destruct (lookup_enum_variant name defs) as [vdef |] eqn:Hlookup;
      [eapply IH; eauto | discriminate].
Qed.

Lemma lookup_expr_branch_disjoint_alpha :
  forall name branches e ρ,
    lookup_expr_branch name branches = Some e ->
    disjoint_names
      ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
          match branches0 with
          | [] => []
          | (_, _, e0) :: rest => free_vars_expr e0 ++ go rest
          end) branches)
      (rename_range ρ) ->
    disjoint_names (free_vars_expr e) (rename_range ρ).
Proof.
  intros name branches.
  induction branches as [| [[name0 binders0] e0] rest IH]; intros e ρ Hlookup Hdisj;
    simpl in Hlookup, Hdisj.
  - discriminate.
  - destruct (disjoint_names_app_l (free_vars_expr e0)
      ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
          match branches0 with
          | [] => []
          | (_, _, e1) :: rest0 => free_vars_expr e1 ++ go rest0
          end) rest) (rename_range ρ) Hdisj) as [Hdisj_head Hdisj_rest].
    destruct (String.eqb name name0) eqn:Hname.
    + injection Hlookup as <-. exact Hdisj_head.
    + eapply IH; eauto.
Qed.

Lemma alpha_rename_typed_match_tail_env_structural_forward :
  forall env Ω n ρ lts args Σ Σr branches branchesr used used' variants expected_core
      Σs Ts,
  (forall ρ0 Σa Σb used0 variant binders e er used1 T Σa',
      In (variant, binders, e) branches ->
      ctx_alpha ρ0 Σa Σb ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range ρ0) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range ρ0) ->
      alpha_rename_expr ρ0 used0 e = (er, used1) ->
      typed_env_structural env Ω n Σa e T Σa' ->
      exists Σb',
        typed_env_structural env Ω n Σb er T Σb' /\
        ctx_alpha ρ0 Σa' Σb') ->
  ctx_alpha ρ Σ Σr ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range ρ) -> In x used) ->
  disjoint_names
    ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
        match branches0 with
        | [] => []
        | (_, _, e) :: rest => free_vars_expr e ++ go rest
        end) branches)
    (rename_range ρ) ->
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name, binders, e) :: rest =>
          let binder_seed := binders ++ free_vars_expr e ++ used0 in
          let '(binders', ρ_branch, used1) :=
            alpha_rename_idents ρ binder_seed binders in
          let (e', used2) := alpha_rename_expr ρ_branch used1 e in
          let (rest', used3) := go used2 rest in
          ((name, binders', e') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  typed_match_tail_env_structural env Ω n lts args Σ branches variants
    expected_core Σs Ts ->
  exists Σrs,
    typed_match_tail_env_structural env Ω n lts args Σr branchesr variants
      expected_core Σrs Ts /\
    Forall2 (ctx_alpha ρ) Σs Σrs.
Proof.
  intros env Ω n ρ lts args Σ Σr branches branchesr used used' variants
    expected_core Σs Ts Hexpr Hctx Hctx_used Hrange_used Hdisj Hrename
    Htyped_tail.
  induction Htyped_tail.
  - exists []. split; [constructor | constructor].
  - destruct (alpha_rename_match_branches_lookup_payload_forward
      ρ used branches branchesr used' (enum_variant_name v) binders e
      Hrename H H3)
	      as [bindersr [ρ_branch [er [used_pre [used_branch [used_branch_out
	        [Hbinders_r [Hlookup_r [Hrename_binders
		          [Hrename_branch Hused_prefix]]]]]]]]]].
	    pose proof (lookup_expr_branch_binders_expr_in_alpha _ _ _ _ H H3)
	      as Hbranch_in.
	    unfold match_payload_params in H0.
	    destruct (match_binder_params_alpha_rename_idents
	      ρ (binders ++ free_vars_expr e ++ used_pre) binders bindersr ρ_branch
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
      ctx_alpha ρ_branch (sctx_add_params ps Σ) (sctx_add_params psr Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Hrename_params.
      - exact Hctx.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin. }
    destruct (Hexpr ρ_branch (sctx_add_params ps Σ) (sctx_add_params psr Σr)
      used_branch (enum_variant_name v) binders e er used_branch_out T
      Σv_payload)
      as [Σv_payload_r [Htyped_branch_r Hctx_branch_payload]].
    + exact Hbranch_in.
    + exact Hctx_payload.
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
	        -- exact H3.
	        -- exact Hdisj.
	        -- exact Hfree.
	        -- exact Hin_range.
	    + exact Hrename_branch.
	    + exact H4.
	    + assert (Hparams_ok_r :
	        params_ok_sctx_b env psr Σv_payload_r = true).
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
	        - exact Hctx_branch_payload.
	        - exact H5. }
	      specialize (IHHtyped_tail Hexpr Hctx Hdisj Hrename).
	      destruct IHHtyped_tail as [Σrs [Htail_r Hctxs_tail]].
	      exists (sctx_remove_params psr Σv_payload_r :: Σrs). split.
	      * eapply TESMatchTail_Cons.
	        -- exact Hbinders_r.
	        -- unfold match_payload_params. exact Hparams_r.
	        -- exact Hparams_nodup_r.
	        -- exact Hctx_none_r.
	        -- exact Hlookup_r.
	        -- exact Htyped_branch_r.
	        -- exact Hparams_ok_r.
	        -- reflexivity.
	        -- exact H7.
	        -- exact Htail_r.
      * constructor.
        -- subst Σv.
           eapply alpha_rename_params_ctx_alpha_remove.
           ++ exact Hrename_params.
           ++ exact Hctx_branch_payload.
        -- assumption.
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
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l0).
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
		  - destruct ((fix go (used0 : list ident) (payloads0 : list expr)
		                : list expr * list ident :=
		                 match payloads0 with
		                 | [] => ([], used0)
		                 | e0 :: rest =>
		                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
		                     let (rest', used2) := go used1 rest in
		                     (e0' :: rest', used2)
		                 end) used l1).
		    injection Hrename as <- _. discriminate.
		  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
		    destruct ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
		                : list (string * list ident * expr) * list ident :=
		                 match branches0 with
		                 | [] => ([], used0)
		                 | (variant_name, binders, e0) :: rest =>
		                     let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
		                     let '(binders', ρ_branch, used1) :=
		                       alpha_rename_idents ρ binder_seed binders in
		                     let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
		                     let (rest', used3) := go used2 rest in
		                     ((variant_name, binders', e0') :: rest', used3)
		                 end) used0 l).
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
  - destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used l0).
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
		  - destruct ((fix go (used0 : list ident) (payloads0 : list expr)
		                : list expr * list ident :=
		                 match payloads0 with
		                 | [] => ([], used0)
		                 | e0 :: rest =>
		                     let (e0', used1) := alpha_rename_expr ρ used0 e0 in
		                     let (rest', used2) := go used1 rest in
		                     (e0' :: rest', used2)
		                 end) used l1).
		    injection Hrename as <- _. reflexivity.
		  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
		    destruct ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
		                : list (string * list ident * expr) * list ident :=
		                 match branches0 with
		                 | [] => ([], used0)
		                 | (variant_name, binders, e0) :: rest =>
		                     let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
		                     let '(binders', ρ_branch, used1) :=
		                       alpha_rename_idents ρ binder_seed binders in
		                     let (e0', used2) := alpha_rename_expr ρ_branch used1 e0 in
		                     let (rest', used3) := go used2 rest in
		                     ((variant_name, binders', e0') :: rest', used3)
		                 end) used0 l).
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
		      + injection Hrename as <- <-.
		        exists Σr. split.
		        * eapply TES_MakeClosure; eauto.
		          eapply check_make_closure_captures_sctx_with_env_alpha_forward; eauto.
		        * exact Hctx.
		      + injection Hrename as <- <-.
		        exists Σr. split.
		        * eapply TES_MakeClosure_Static; eauto.
		          eapply check_make_closure_captures_sctx_alpha_forward; eauto.
		        * exact Hctx.
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
      + destruct ((fix go (used0 : list ident) (args0 : list expr)
                    : list expr * list ident :=
                    match args0 with
                    | [] => ([], used0)
                    | arg :: rest =>
                        let (arg', used1) := alpha_rename_expr ρ used0 arg in
                        let (rest', used2) := go used1 rest in
                        (arg' :: rest', used2)
                    end) used payloads) as [payloadsr used_payloads] eqn:Hpayloads.
        injection Hrename as <- <-.
        destruct (alpha_rename_typed_args_env_structural_forward
          env Ω n ρ Σ Σr payloads payloadsr used used_payloads
          (params_of_tys
            (map (instantiate_enum_variant_field_ty lts args)
              (enum_variant_fields vdef)))
          (params_of_tys
            (map (instantiate_enum_variant_field_ty lts args)
              (enum_variant_fields vdef))) Σ') as [Σr' [Hpayloads_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used1 T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_enum_payload_lt enum_name variant_name lts args
               payloads e0 Hin) as Hpayload_lt.
             eapply Nat.lt_le_trans.
             ++ exact Hpayload_lt.
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
        * exact Hpayloads.
        * exact H4.
        * exists Σr'. split.
          -- eapply TES_Enum; eauto.
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
      + destruct (disjoint_names_app_l (free_vars_expr scrut)
          ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
              match branches0 with
              | [] => []
              | (_, _, e) :: rest => free_vars_expr e ++ go rest
              end) branches) (rename_range ρ) Hdisj)
          as [Hdisj_scrut Hdisj_branches].
        destruct (alpha_rename_expr ρ used scrut) as [scrutr used_scrut]
          eqn:Hscrut.
        destruct ((fix go (used0 : list ident)
                    (branches0 : list (string * list ident * expr))
                    : list (string * list ident * expr) * list ident :=
                    match branches0 with
                    | [] => ([], used0)
                    | (variant_name, binders, e) :: rest =>
                        let binder_seed := binders ++ free_vars_expr e ++ used0 in
                        let '(binders', ρ_branch, used1) :=
                          alpha_rename_idents ρ binder_seed binders in
                        let (e', used2) := alpha_rename_expr ρ_branch used1 e in
                        let (rest', used3) := go used2 rest in
                        ((variant_name, binders', e') :: rest', used3)
                    end) used_scrut branches) as [branchesr used_branches]
          eqn:Hbranches.
        injection Hrename as <- <-.
        destruct (IH env Ω n ρ Σ Σr scrut scrutr used used_scrut
          T_scrut Σ1) as [Σr1 [Hscrut_r Hctx1_r]];
          try solve [simpl in Hlt; lia | eauto].
        assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used_scrut).
        { intros y Hy.
          eapply alpha_rename_expr_used_extends.
          - exact Hscrut.
          - apply Hctx_used.
            rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
            + exact Hy.
            + eapply typed_env_structural_same_bindings. exact Hscrut_r. }
        assert (Hrange_used1 : forall y, In y (rename_range ρ) -> In y used_scrut).
        { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
	        destruct (alpha_rename_match_branches_lookup_payload_forward
	          ρ used_scrut branches branchesr used_branches
	          (enum_variant_name v_head) binders_head e_head Hbranches H6 H10)
	          as [binders_head_r [ρ_head [e_headr
	            [used_head_pre [used_head [used_head_out
	              [Hbinders_head_r [Hlookup_head_r [Hrename_head_binders
	                [Hrename_head Hused_head_pre]]]]]]]]]].
	        pose proof (lookup_expr_branch_binders_expr_in_alpha _ _ _ _ H6 H10)
	          as Hhead_in.
	        unfold match_payload_params in H7.
	        destruct (match_binder_params_alpha_rename_idents
	          ρ (binders_head ++ free_vars_expr e_head ++ used_head_pre)
	          binders_head binders_head_r ρ_head used_head
	          (instantiate_enum_variant_field_tys lts args v_head) ps_head
	          Hrename_head_binders H7)
	          as [ps_head_r [Hparams_head_r [Hparams_head_alpha
	            Hrename_head_params]]].
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
          - intros y Hy. apply Hused_head_pre. apply Hctx_used1. exact Hy.
          - rewrite (match_binder_params_names _ _ _ Hparams_head_r).
            eapply Forall_fresh_weaken.
            + intros y Hy.
              apply in_or_app. right. apply in_or_app. right. exact Hy.
            + eapply alpha_rename_idents_fresh_used.
              exact Hrename_head_binders. }
        assert (Hctx_head_payload :
          ctx_alpha ρ_head
            (sctx_add_params ps_head Σ1)
            (sctx_add_params ps_head_r Σr1)).
        { unfold sctx_add_params, ctx_add_params.
          eapply alpha_rename_params_ctx_alpha_extend_tail.
          - exact Hrename_head_params.
          - exact Hctx1_r.
          - intros y Hy. apply in_or_app. right. apply in_or_app. right.
            apply Hused_head_pre. apply Hctx_used1. exact Hy.
          - intros y Hy. apply in_or_app. right. apply in_or_app. right.
            apply Hused_head_pre. apply Hrange_used1. exact Hy. }
        assert (Hhead_size : expr_size e_head < fuel).
        { pose proof (expr_size_match_branch_lt scrut branches
            (enum_variant_name v_head) binders_head e_head Hhead_in)
            as Hbranch_lt.
          lia. }
        assert (Hhead_ctx_used :
          forall y,
            In y (ctx_names (sctx_add_params ps_head_r Σr1)) ->
            In y used_head).
        { intros y Hy.
          unfold sctx_add_params, ctx_add_params in Hy.
          rewrite ctx_names_app in Hy.
          apply in_app_or in Hy as [Hy_params | Hy_tail].
          - eapply alpha_rename_params_names_in_used.
            + exact Hrename_head_params.
            + exact Hy_params.
          - eapply alpha_rename_params_used_extends.
            + exact Hrename_head_params.
            + apply in_or_app. right. apply in_or_app. right.
              apply Hused_head_pre. apply Hctx_used1. exact Hy_tail. }
        assert (Hhead_range_used :
          forall y, In y (rename_range ρ_head) -> In y used_head).
        { intros y Hy.
          destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _
            Hrename_head_params _ Hy) as [Hy_params | Hy_range].
          - eapply alpha_rename_params_names_in_used.
            + exact Hrename_head_params.
            + exact Hy_params.
          - eapply alpha_rename_params_used_extends.
            + exact Hrename_head_params.
            + apply in_or_app. right. apply in_or_app. right.
              apply Hused_head_pre. apply Hrange_used1. exact Hy_range. }
        assert (Hhead_disj :
          disjoint_names (free_vars_expr e_head) (rename_range ρ_head)).
        { intros y Hfree Hrange.
          destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _
            Hrename_head_params _ Hrange) as [Hy_params | Hy_range].
          - eapply alpha_rename_params_names_fresh_used.
            + exact Hrename_head_params.
            + exact Hy_params.
            + apply in_or_app. right. apply in_or_app. left. exact Hfree.
	          - eapply lookup_expr_branch_disjoint_alpha.
	            + exact H10.
	            + exact Hdisj_branches.
	            + exact Hfree.
	            + exact Hy_range. }
        destruct (IH env Ω n ρ_head
          (sctx_add_params ps_head Σ1)
          (sctx_add_params ps_head_r Σr1)
          e_head e_headr used_head used_head_out T_head
          Σ_head_payload Hhead_size Hctx_head_payload Hhead_ctx_used
          Hhead_range_used Hhead_disj Hrename_head Htyped2)
          as [Σ_head_payload_r [Hhead_r Hctx_head_payload_r]].
        assert (Hparams_head_ok_r :
            params_ok_sctx_b env ps_head_r Σ_head_payload_r = true).
          { eapply alpha_rename_params_params_ok_sctx_b_forward_gen.
	            - exact Hrename_head_params.
	            - rewrite <- params_ctx_names_param_names.
	              eapply params_names_nodup_b_sound. exact H8.
	            - intros y Hy.
	              rewrite <- params_ctx_names_param_names in Hy.
	              rewrite (match_binder_params_names _ _ _ H7) in Hy.
	              apply in_or_app. left. exact Hy.
            - intros y Hy.
              apply in_or_app. right. apply in_or_app. right.
	              apply Hused_head_pre. apply Hrange_used1. exact Hy.
	            - exact Hctx_head_payload_r.
	            - exact H11. }
          assert (Hctx_head_r :
            ctx_alpha ρ Σ_head
              (sctx_remove_params ps_head_r Σ_head_payload_r)).
          { subst Σ_head.
            eapply alpha_rename_params_ctx_alpha_remove.
            - exact Hrename_head_params.
            - exact Hctx_head_payload_r. }
        destruct (alpha_rename_typed_match_tail_env_structural_forward
            env Ω n ρ lts args Σ1 Σr1 branches branchesr used_scrut used_branches
            v_tail (ty_core T_head) Σ_tail Ts_tail)
            as [Σ_tailr [Htail_r Hctx_tail_r]].
          -- intros ρ0 Σa Σb used0 variant binders e0 er0 used1 T0 Σa'
               Hin Halpha Hcu Hru Hd Hr Ht.
             eapply IH.
             ++ pose proof (expr_size_match_branch_lt scrut branches
                  variant binders e0 Hin) as Hbranch_lt.
                eapply Nat.lt_le_trans.
                ** exact Hbranch_lt.
                ** apply Nat.lt_succ_r. exact Hlt.
             ++ exact Halpha.
             ++ exact Hcu.
             ++ exact Hru.
             ++ exact Hd.
             ++ exact Hr.
             ++ exact Ht.
          -- exact Hctx1_r.
          -- exact Hctx_used1.
          -- exact Hrange_used1.
	          -- exact Hdisj_branches.
	          -- exact Hbranches.
	          -- exact H13.
	          -- destruct (ctx_alpha_merge_many_forward ρ
	               Σ_head (sctx_remove_params ps_head_r Σ_head_payload_r)
	               Σ_tail Σ_tailr Γ_out)
               as [Γ_outr [Hmerge_r Hctx_merge_r]].
	             ++ exact Hctx_head_r.
	             ++ exact Hctx_tail_r.
	             ++ exact H14.
	             ++ exists (sctx_of_ctx Γ_outr). split.
	                ** { eapply TES_Match; eauto;
	                     try solve
	                       [ eapply alpha_rename_match_branches_first_unknown_variant_branch; eauto
	                       | exact Hbinders_head_r
	                       | unfold match_payload_params; exact Hparams_head_r
                       | exact Hparams_head_nodup_r
                       | exact Hctx_head_none_r
                       | exact Hlookup_head_r
                       | exact Hhead_r
                       | exact Hparams_head_ok_r
                       | reflexivity ]. }
                ** unfold sctx_of_ctx. exact Hctx_merge_r.
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
        * exact H3.
        * exists Σr'. split; [econstructor; eauto | exact Hctx_r].
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
          (apply_lt_params σ (apply_type_params type_args (fn_params fdef)))
          (apply_lt_params σ (apply_type_params type_args (fn_params fdef)))
          Σ') as [Σr' [Hargs_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used1 T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_call_generic_arg_lt fname type_args args e0 Hin)
               as Harg_lt.
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
        * exact H4.
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
          (MkTy u (TClosure env_lt param_tys ret)) Σ1) as [Σr1 [Hcallee_r Hctx1_r]];
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
        * exists Σr'. split; [eapply TES_CallExpr_Closure; eauto | exact Hctx_r].
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
		        * exists Σr'. split; [eapply TES_CallExpr_Forall_Closure; eauto | exact Hctx_r].
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
		          (MkTy u (TForall m bounds
		            (MkTy u_body
		              (TTypeForall type_params type_bounds body)))) Σ1)
		          as [Σr1 [Hcallee_r Hctx1_r]];
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
		          (params_of_tys
		            (map (open_bound_ty σ)
		              (map (subst_type_params_ty type_args) param_tys)))
		          (params_of_tys
		            (map (open_bound_ty σ)
		              (map (subst_type_params_ty type_args) param_tys))) Σ')
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
		        * exists Σr'. split; [eapply TES_CallExpr_MixedForall; eauto | exact Hctx_r].
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
		          (MkTy u (TTypeForall m bounds body)) Σ1) as [Σr1 [Hcallee_r Hctx1_r]];
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
		          (params_of_tys (map (subst_type_params_ty type_args) param_tys))
		          (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ')
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
		        * exists Σr'. split; [eapply TES_CallExpr_TypeForall; eauto | exact Hctx_r].
		      + destruct (disjoint_names_app_l (free_vars_expr (EMakeClosure fname captures))
          ((fix go (args0 : list expr) : list ident :=
              match args0 with
              | [] => []
              | arg :: rest => free_vars_expr arg ++ go rest
              end) args) (rename_range ρ) Hdisj) as [Hdisj_callee Hdisj_args].
        simpl in Hdisj_callee.
        destruct ((fix go (used0 : list ident) (args0 : list expr)
                    : list expr * list ident :=
                    match args0 with
                    | [] => ([], used0)
                    | arg :: rest =>
                        let (arg', used1') := alpha_rename_expr ρ used0 arg in
                        let (rest', used2) := go used1' rest in
                        (arg' :: rest', used2)
                    end) used args) as [argsr used_args] eqn:Hargs.
        injection Hrename as <- <-.
        destruct (alpha_rename_typed_args_env_structural_forward
          env Ω n ρ Σ Σr args argsr used used_args
          (apply_lt_params σ (fn_params fdef))
          (apply_lt_params σ (fn_params fdef)) Σ')
          as [Σr' [Hargs_r Hctx_r]].
        * intros Σa Σb used0 e0 er0 used_tail T0 Σa' Hin Halpha Hcu Hru Hd Hr Ht.
          eapply IH.
          -- pose proof (expr_size_callexpr_arg_lt
               (EMakeClosure fname captures) args e0 Hin) as Harg_lt.
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
        * exact Hdisj_args.
        * apply params_alpha_refl.
        * exact Hargs.
        * assumption.
        * exists Σr'. split.
          -- eapply TES_CallExpr_MakeClosure with (σ := σ); eauto.
             eapply check_make_closure_captures_sctx_with_env_alpha_forward;
               eauto.
          -- exact Hctx_r.
	  }
  intros env Ω n ρ Σ Σr e er used used' T Σ'
    Hctx Hctx_used Hrange_used Hdisj Hrename Htyped.
  eapply (Hsize (S (expr_size e))); eauto.
Qed.

Lemma root_env_equiv_rename_lookup_forward :
  forall rho R Rr x roots,
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    root_env_lookup x R = Some roots ->
    exists rootsr,
      root_env_lookup (lookup_rename x rho) Rr = Some rootsr /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros rho R Rr x roots Heq Hnocoll Hlookup.
  assert (Hlookup_ren :
    root_env_lookup (lookup_rename x rho) (root_env_rename rho R) =
      Some (root_set_rename rho roots)).
  { eapply root_env_lookup_rename.
    - apply Hnocoll.
      eapply root_env_lookup_some_in_names. exact Hlookup.
    - exact Hlookup. }
  destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R)
    (lookup_rename x rho) (root_set_rename rho roots) Heq Hlookup_ren)
    as [rootsr [Hlookup_r Hroots]].
  exists rootsr. split.
  - exact Hlookup_r.
  - exact Hroots.
Qed.

Lemma root_env_equiv_rename_lookup_none_forward :
  forall rho R Rr x,
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_lookup x R = None ->
    root_env_lookup (lookup_rename x rho) Rr = None.
Proof.
  intros rho R Rr x Heq Hnocoll Hlookup.
  apply root_env_equiv_lookup_none_r with (R' := root_env_rename rho R).
  - exact Heq.
  - apply root_env_lookup_rename_none; assumption.
Qed.

Lemma root_env_rename_no_shadow_collision_on :
  forall rho R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R).
Proof.
  unfold root_env_no_shadow, rename_no_collision_on, rename_no_collision_for.
  intros rho R Hnodup Hnodup_r.
  rewrite root_env_rename_names in Hnodup_r.
  remember (root_env_names R) as names.
  clear Heqnames R.
  induction names as [| a rest IH]; intros x Hx y Hy Hneq Heq.
  - contradiction.
  - simpl in Hnodup, Hnodup_r, Hx, Hy.
    inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]; subst.
    inversion Hnodup_r as [| ? ? Hfa_notin Hnodup_r_tail]; subst.
    destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
    + subst. contradiction.
    + subst x.
      apply Hfa_notin.
      rewrite <- Heq.
      apply (in_map (fun z => lookup_rename z rho)). exact Hy.
    + subst y.
      apply Hfa_notin.
      rewrite Heq.
      apply (in_map (fun z => lookup_rename z rho)). exact Hx.
    + eapply IH.
      * exact Hnodup_tail.
      * exact Hnodup_r_tail.
      * exact Hx.
      * exact Hy.
      * exact Hneq.
      * exact Heq.
Qed.

Lemma root_sets_union_rename_equiv :
  forall rho roots rootsr,
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots) ->
    root_set_equiv (root_sets_union rootsr)
      (root_set_rename rho (root_sets_union roots)).
Proof.
  intros rho roots.
  induction roots as [| roots_hd roots_tl IH]; intros rootsr Hforall.
  - inversion Hforall; subst. apply root_set_equiv_refl.
  - simpl in Hforall |- *.
    destruct rootsr as [| rootsr_hd rootsr_tl].
    { inversion Hforall. }
    inversion Hforall; subst.
    eapply root_set_equiv_trans.
    + apply root_set_union_equiv.
      * match goal with
        | H : root_set_equiv rootsr_hd (root_set_rename rho roots_hd) |- _ =>
            exact H
        end.
      * apply IH.
        match goal with
        | H : Forall2 root_set_equiv rootsr_tl
              (map (root_set_rename rho) roots_tl) |- _ =>
            exact H
        end.
    + apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma root_env_equiv_update_rename_union :
  forall rho R Rr x roots_old roots_new roots_oldr roots_newr,
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv roots_oldr (root_set_rename rho roots_old) ->
    root_set_equiv roots_newr (root_set_rename rho roots_new) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_equiv
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr)
      (root_env_rename rho
        (root_env_update x (root_set_union roots_old roots_new) R)).
Proof.
  intros rho R Rr x roots_old roots_new roots_oldr roots_newr
    HRr Hroots_old Hroots_new Hnocoll.
  rewrite root_env_rename_update.
  - apply root_env_equiv_update.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_union_rename_equiv.
    + exact HRr.
  - exact Hnocoll.
Qed.

Lemma root_env_equiv_remove_rename :
  forall rho R Rr x,
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_equiv
      (root_env_remove (lookup_rename x rho) Rr)
      (root_env_rename rho (root_env_remove x R)).
Proof.
  intros rho R Rr x HnsR HnsRr HRr Hnocoll_on Hnocoll.
  rewrite root_env_rename_remove.
  - apply root_env_equiv_remove.
    + exact HnsRr.
    + apply root_env_rename_no_shadow.
      * exact HnsR.
      * exact Hnocoll_on.
    + exact HRr.
  - exact Hnocoll.
Qed.

Inductive typed_env_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERS_Unit : forall R Σ,
      typed_env_roots_shadow_safe env Ω n R Σ EUnit
        (MkTy UUnrestricted TUnits) Σ R []
  | TERS_LitInt : forall R Σ i,
      typed_env_roots_shadow_safe env Ω n R Σ (ELit (LInt i))
        (MkTy UUnrestricted TIntegers) Σ R []
  | TERS_LitFloat : forall R Σ f,
      typed_env_roots_shadow_safe env Ω n R Σ (ELit (LFloat f))
        (MkTy UUnrestricted TFloats) Σ R []
  | TERS_LitBool : forall R Σ b,
      typed_env_roots_shadow_safe env Ω n R Σ (ELit (LBool b))
        (MkTy UUnrestricted TBooleans) Σ R []
  | TERS_Var_Copy : forall R Σ x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ R roots
  | TERS_Var_Move : forall R Σ Σ' x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R roots
  | TERS_Place_Copy : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ R roots
  | TERS_Place_Move : forall R Σ Σ' p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ' R roots
  | TERS_Call : forall R R' Σ Σ' fname fdef args σ arg_roots,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_roots_shadow_safe env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => Lifetime.outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECall fname args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TERS_CallGeneric :
      forall R R' Σ Σ' fname fdef (type_args : list Ty) args σ arg_roots,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_roots_shadow_safe env Ω n R Σ args
        (apply_lt_params σ
          (apply_type_params type_args (fn_params fdef))) Σ' R' arg_roots ->
      Forall (fun '(a, b) => Lifetime.outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallGeneric fname type_args args)
        (apply_lt_ty σ (subst_type_params_ty type_args (fn_ret fdef)))
        Σ' R' (root_sets_union arg_roots)
  | TERS_Fn : forall R Σ fname fdef,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_env_roots_shadow_safe env Ω n R Σ (EFn fname)
        (fn_value_ty fdef) Σ R []
  | TERS_MakeClosure : forall R Σ fname fdef captures env_lt captured_tys,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) =
        infer_ok (env_lt, captured_tys) ->
      typed_env_roots_shadow_safe env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty_at env_lt fdef captured_tys) Σ R []
  | TERS_MakeClosure_Static : forall R Σ fname fdef captures captured_tys,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx env Ω Σ captures (fn_captures fdef) =
        infer_ok captured_tys ->
      typed_env_roots_shadow_safe env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty fdef captured_tys) Σ R []
  | TERS_CallExpr_MakeClosure : forall R R' Σ Σ' fname fdef captures
      env_lt captured_tys args σ arg_roots,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_roots_shadow_safe env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => Lifetime.outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TERS_Struct : forall R R' Σ Σ' sname lts args fields sdef roots,
      Program.lookup_struct sname env = Some sdef ->
      Datatypes.length lts = Program.struct_lifetimes sdef ->
      Datatypes.length args = Program.struct_type_params sdef ->
      check_struct_bounds env (Program.struct_bounds sdef) args = None ->
      typed_fields_roots_shadow_safe env Ω n lts args R Σ fields
        (Program.struct_fields sdef) Σ' R' roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ' R' roots
  | TERS_Enum : forall R R' Σ Σ' enum_name variant_name lts args payloads
      edef vdef payload_roots,
      Program.lookup_enum enum_name env = Some edef ->
      Program.lookup_enum_variant variant_name (Program.enum_variants edef) =
        Some vdef ->
      Datatypes.length lts = Program.enum_lifetimes edef ->
      Datatypes.length args = Program.enum_type_params edef ->
      check_struct_bounds env (Program.enum_bounds edef) args = None ->
      typed_args_roots_shadow_safe env Ω n R Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args)
            (Program.enum_variant_fields vdef))) Σ' R' payload_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EEnum enum_name variant_name lts args payloads)
        (instantiate_enum_ty edef lts args) Σ' R'
        (root_sets_union payload_roots)
  | TERS_Match : forall R R1 R_payload R_head_payload R_out
        Σ Σ1 Σ_head_payload Σ_head Σ_tail Γ_out scrut branches
        enum_name lts args edef v_head v_tail e_head T_scrut T_head Ts_tail
        binders_head ps_head roots_scrut roots_head roots_tail,
      typed_env_roots_shadow_safe env Ω n R Σ scrut T_scrut Σ1 R1 roots_scrut ->
      ty_core T_scrut = TEnum enum_name lts args ->
      Program.lookup_enum enum_name env = Some edef ->
      Datatypes.length lts = Program.enum_lifetimes edef ->
      Datatypes.length args = Program.enum_type_params edef ->
	      check_struct_bounds env (Program.enum_bounds edef) args = None ->
	      first_unknown_variant_branch branches (Program.enum_variants edef) = None ->
	      Program.enum_variants edef = v_head :: v_tail ->
	      lookup_expr_branch_binders (Program.enum_variant_name v_head) branches = Some binders_head ->
	      match_payload_params binders_head lts args v_head = infer_ok ps_head ->
      params_names_nodup_b ps_head = true ->
      ctx_lookup_params_none_b ps_head Σ1 = true ->
      root_env_lookup_params_none_b ps_head R1 = true ->
      lookup_expr_branch (Program.enum_variant_name v_head) branches = Some e_head ->
      R_payload = root_env_add_params_roots_same ps_head roots_scrut R1 ->
      typed_env_roots_shadow_safe env Ω n R_payload (sctx_add_params ps_head Σ1)
        e_head T_head Σ_head_payload R_head_payload roots_head ->
      params_ok_sctx_b env ps_head Σ_head_payload = true ->
      roots_exclude_params ps_head roots_head ->
      R_out = root_env_remove_match_params ps_head R_head_payload ->
      root_env_excludes_params ps_head R_out ->
      Σ_head = sctx_remove_params ps_head Σ_head_payload ->
      typed_match_tail_roots_shadow_safe env Ω n lts args R1 roots_scrut Σ1 branches v_tail
        (ty_core T_head) R_out Σ_tail Ts_tail roots_tail ->
      ctx_merge_many (ctx_of_sctx Σ_head) (map ctx_of_sctx Σ_tail) =
        Some Γ_out ->
      typed_env_roots_shadow_safe env Ω n R Σ (EMatch scrut branches)
        (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head))
        (sctx_of_ctx Γ_out) R_out (root_sets_union (roots_head :: roots_tail))
  | TERS_Let : forall R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2
      roots1 roots2,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      ty_compatible_b Ω T1 T = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots_shadow_safe env Ω n R Σ (ELet m x T e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TERS_LetInfer : forall R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2
      roots1 roots2,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots_shadow_safe env Ω n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TERS_Drop : forall R R' Σ Σ' e T roots,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EDrop e)
        (MkTy UUnrestricted TUnits) Σ' R' []
  | TERS_Replace_Path : forall R R1 Σ Σ1 Σ2 p e_new T_old T_new
      x path roots_result roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      root_env_lookup x R = Some roots_result ->
      typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new) T_old Σ2
        (root_env_update x (root_set_union roots_old roots_new) R1)
        roots_result
  | TERS_Assign_Path : forall R R1 Σ Σ' p e_new T_old T_new
      x path roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
        (MkTy UUnrestricted TUnits) Σ'
        (root_env_update x (root_set_union roots_old roots_new) R1) []
  | TERS_BorrowShared : forall R Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_roots_shadow_safe env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (Lifetime.LVar n) RShared T)) Σ R
        (root_of_place p)
  | TERS_BorrowUnique : forall R Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_roots_shadow_safe env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (Lifetime.LVar n) RUnique T)) Σ R [RStore x]
  | TERS_DerefBorrowShared : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EDeref (EBorrow RShared p)) T Σ R roots
  | TERS_DerefBorrowUnique : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EDeref (EBorrow RUnique p)) T Σ R roots
  | TERS_If : forall R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3
      T_cond T2 T3 roots_cond roots2 roots3,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond ->
      ty_core T_cond = TBooleans ->
      typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
      typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      root_env_equiv R2 R3 ->
      typed_env_roots_shadow_safe env Ω n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        Σ4 R2 (root_set_union roots2 roots3)
with typed_args_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param -> sctx -> root_env ->
      list root_set -> Prop :=
  | TERSArgs_Nil : forall R Σ,
      typed_args_roots_shadow_safe env Ω n R Σ [] [] Σ R []
  | TERSArgs_Cons : forall R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots
      roots_rest,
      typed_env_roots_shadow_safe env Ω n R Σ e T_e Σ1 R1 roots ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 es ps Σ2 R2 roots_rest ->
      typed_args_roots_shadow_safe env Ω n R Σ (e :: es) (p :: ps)
        Σ2 R2 (roots :: roots_rest)
with typed_fields_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : list Lifetime.lifetime -> list Ty -> root_env -> sctx ->
      list (string * expr) -> list Program.field_def -> sctx -> root_env ->
      root_set -> Prop :=
  | TERSFields_Nil : forall lts args R Σ fields,
      typed_fields_roots_shadow_safe env Ω n lts args R Σ fields []
        Σ R []
  | TERSFields_Cons : forall lts args R R1 R2 Σ Σ1 Σ2 fields f rest
      e_field T_field roots_field roots_rest,
      lookup_field_b (Program.field_name f) fields = Some e_field ->
      typed_env_roots_shadow_safe env Ω n R Σ e_field T_field Σ1 R1
        roots_field ->
      ty_compatible_b Ω T_field (Program.instantiate_struct_field_ty lts args f) =
        true ->
      typed_fields_roots_shadow_safe env Ω n lts args R1 Σ1 fields rest
        Σ2 R2 roots_rest ->
      typed_fields_roots_shadow_safe env Ω n lts args R Σ fields (f :: rest)
        Σ2 R2 (root_set_union roots_field roots_rest)
with typed_match_tail_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : list Lifetime.lifetime -> list Ty -> root_env -> root_set -> sctx ->
      list (string * list ident * expr) -> list Program.enum_variant_def ->
      TypeCore Ty -> root_env -> list sctx -> list Ty -> list root_set -> Prop :=
  | TERSMatchTail_Nil : forall lts args R roots_scrut Σ branches expected_core R_out,
      typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches []
        expected_core R_out [] [] []
	  | TERSMatchTail_Cons : forall R R_payload Rv_payload Rv Σ branches v rest e T
	      Σv_payload Σv R_out roots Σs Ts rootss expected_core
	      binders ps lts args roots_scrut,
	      lookup_expr_branch_binders (Program.enum_variant_name v) branches = Some binders ->
	      match_payload_params binders lts args v = infer_ok ps ->
      params_names_nodup_b ps = true ->
      ctx_lookup_params_none_b ps Σ = true ->
      root_env_lookup_params_none_b ps R = true ->
      lookup_expr_branch (Program.enum_variant_name v) branches = Some e ->
      R_payload = root_env_add_params_roots_same ps roots_scrut R ->
      typed_env_roots_shadow_safe env Ω n R_payload (sctx_add_params ps Σ)
        e T Σv_payload Rv_payload roots ->
      params_ok_sctx_b env ps Σv_payload = true ->
      roots_exclude_params ps roots ->
      Rv = root_env_remove_match_params ps Rv_payload ->
      root_env_excludes_params ps Rv ->
      Σv = sctx_remove_params ps Σv_payload ->
      ty_core T = expected_core ->
      root_env_equiv Rv R_out ->
      typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches rest
        expected_core R_out Σs Ts rootss ->
      typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches (v :: rest)
        expected_core R_out (Σv :: Σs) (T :: Ts) (roots :: rootss).

Scheme typed_env_roots_shadow_safe_ind' :=
  Induction for typed_env_roots_shadow_safe Sort Prop
with typed_args_roots_shadow_safe_ind' :=
  Induction for typed_args_roots_shadow_safe Sort Prop
with typed_fields_roots_shadow_safe_ind' :=
  Induction for typed_fields_roots_shadow_safe Sort Prop
with typed_match_tail_roots_shadow_safe_ind' :=
  Induction for typed_match_tail_roots_shadow_safe Sort Prop.
Combined Scheme typed_roots_shadow_safe_ind
  from typed_env_roots_shadow_safe_ind',
    typed_args_roots_shadow_safe_ind',
    typed_fields_roots_shadow_safe_ind',
    typed_match_tail_roots_shadow_safe_ind'.

Lemma typed_roots_shadow_safe_roots :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss).
Proof.
  intros env Ω n.
  apply typed_roots_shadow_safe_ind; intros; subst; try solve [econstructor; eauto].
  all: try (econstructor; eauto).
Qed.

Lemma typed_env_roots_shadow_safe_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots H.
  exact (proj1 (typed_roots_shadow_safe_roots env Ω n)
    R Σ e T Σ' R' roots H).
Qed.

Lemma typed_args_roots_shadow_safe_roots :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots H.
  exact (proj1 (proj2 (typed_roots_shadow_safe_roots env Ω n))
    R Σ args ps Σ' R' roots H).
Qed.

Lemma typed_fields_roots_shadow_safe_roots :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots H.
  exact (proj1 (proj2 (proj2 (typed_roots_shadow_safe_roots env Ω n)))
    lts args R Σ fields defs Σ' R' roots H).
Qed.

Lemma typed_match_tail_roots_shadow_safe_roots :
  forall env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss.
Proof.
  intros env Ω n lts args R roots_scrut Σ branches variants expected_core
    R_out Σs Ts rootss H.
  exact (proj2 (proj2 (proj2 (typed_roots_shadow_safe_roots env Ω n)))
    lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts
    rootss H).
Qed.

Theorem typed_roots_shadow_safe_instantiate_fresh_mutual :
  forall env Ω n rho,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_env_roots_shadow_safe env Ω n R0 Σ e T Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_args_roots_shadow_safe env Ω n R0 Σ args ps Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        Forall2 root_set_equiv roots0
          (map (root_set_instantiate rho) roots)) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_fields_roots_shadow_safe env Ω n lts args R0 Σ fields defs
          Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_subst_images_exclude_names (match_branches_local_store_names branches) rho ->
    forall roots_scrut0 R0 R0_out,
      root_set_equiv roots_scrut0 (root_set_instantiate rho roots_scrut) ->
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0_out ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      root_env_equiv R0_out (root_env_instantiate rho R_out) ->
      exists rootss0,
        typed_match_tail_roots_shadow_safe env Ω n lts args R0 roots_scrut0 Σ branches variants
          expected_core R0_out Σs Ts rootss0 /\
        Forall2 root_set_equiv rootss0
          (map (root_set_instantiate rho) rootss)).
Proof.
  intros env Ω n rho.
  apply typed_roots_shadow_safe_ind.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ i Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ f Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ b Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ x T roots Hplace Husage Hlookup Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Var_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' x T roots Hplace Husage Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Var_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Place_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' p T x path roots Hplace Husage Hpath Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Place_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R' Σ Σ' fname fdef args σ arg_roots Hin Hfname Hcaps
      Htypeparams Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TERS_Call; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R' Σ Σ' fname fdef type_args args σ arg_roots Hin Hfname
      Hcaps Hlen Hbounds Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_generic in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TERS_CallGeneric; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R Σ fname fdef Hin Hfname Hcaps Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TERS_Fn; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures env_lt captured_tys Hin Hfname Hcheck Hfresh
      R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TERS_MakeClosure; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures captured_tys Hin Hfname Hcheck Hfresh
      R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TERS_MakeClosure_Static; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R R' Σ Σ' fname fdef captures env_lt captured_tys args σ
      arg_roots Hin Hfname Hcheck Hargs IHargs Hout Hfresh R0 HnsR HnsR0
      HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [_ Hfresh_args].
    destruct (IHargs Hfresh_args R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TERS_CallExpr_MakeClosure; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R' Σ Σ' sname lts args fields sdef roots Hlookup Hlen_lts
      Hlen_args Hbounds Hfields IHfields Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_struct in Hfresh.
    destruct (IHfields Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [Hfields0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', roots0. split; [| split; [| split]].
    + eapply TERS_Struct; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + exact Hroots0.
  - intros R R' Σ Σ' enum_name variant_name lts args payloads edef vdef
      payload_roots Hlookup Hvariant Hlen_lts Hlen_args Hbounds Hpayloads
      IHpayloads Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_enum in Hfresh.
    destruct (IHpayloads Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [payload_roots0 [Hpayloads0 [HnsR0' [HR0' Hpayload_roots0]]]]].
    exists R0', (root_sets_union payload_roots0). split; [| split; [| split]].
    + eapply TERS_Enum; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Hpayload_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R1 R_payload R_head_payload R_out Σ Σ1 Σ_head_payload
	      Σ_head Σ_tail Γ_out scrut branches enum_name lts args edef v_head
	      v_tail e_head T_scrut T_head Ts_tail binders_head ps_head roots_scrut
	      roots_head roots_tail Hscrut IHscrut Hcore Hlookup Hlen_lts Hlen_args
	      Hbounds Hunknown Hvariants
	      Hbinders_head Hpayload_head Hnodup_head Hctx_fresh_head Hroot_fresh_head
	      Hlookup_head HRpayload Hhead IHhead
      Hparams_ok_head Hroots_excl_head HRout Henv_excl_head HΣhead Htail
      IHtail Hmerge Hfresh R0 HnsR HnsR0 HR0.
    simpl in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_scrut Hfresh_branches].
    destruct (IHscrut Hfresh_scrut R0 HnsR HnsR0 HR0)
      as [R10 [roots_scrut0 [Hscrut0 [HnsR10 [HR10 Hroots_scrut0]]]]].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hscrut.
      - exact HnsR. }
    assert (Hfresh_R10 :
      root_env_lookup_params_none_b ps_head R10 = true).
    { eapply root_env_lookup_params_none_b_instantiate_equiv; eassumption. }
    assert (Hfresh_ps_head :
      root_subst_images_exclude_names (ctx_names (params_ctx ps_head)) rho).
    {
      rewrite (match_payload_params_names binders_head lts args v_head ps_head
        Hpayload_head).
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh_branches.
      - eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
    }
    assert (Hfresh_head :
      root_subst_images_exclude_names (expr_local_store_names e_head) rho).
    {
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh_branches.
      - eapply lookup_expr_branch_local_store_names_in; eassumption.
    }
    assert (HnsRpayload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    pose (Rpayload0 := root_env_add_params_roots_same ps_head roots_scrut0 R10).
    assert (HnsRpayload0 : root_env_no_shadow Rpayload0).
    { unfold Rpayload0. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (HRpayload0 :
      root_env_equiv Rpayload0 (root_env_instantiate rho R_payload)).
    { subst R_payload. unfold Rpayload0.
      eapply root_env_add_params_roots_same_instantiate_equiv; eauto. }
    destruct (IHhead Hfresh_head Rpayload0 HnsRpayload HnsRpayload0 HRpayload0)
      as [Rhead0 [roots_head0 [Hhead0 [HnsRhead0 [HRhead0 Hroots_head0]]]]].
    assert (HnsRhead_payload : root_env_no_shadow R_head_payload).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hhead.
      - exact HnsRpayload. }
    pose (Rout0 := root_env_remove_match_params ps_head Rhead0).
    assert (HnsRout0 : root_env_no_shadow Rout0).
    { unfold Rout0. apply root_env_remove_match_params_no_shadow. exact HnsRhead0. }
    assert (HRout0 : root_env_equiv Rout0 (root_env_instantiate rho R_out)).
    { subst R_out. unfold Rout0.
      eapply root_env_remove_match_params_instantiate_equiv; eauto. }
    destruct (IHtail Hfresh_branches roots_scrut0 R10 Rout0 Hroots_scrut0
      HnsR1 HnsR10 HnsRout0 HR10 HRout0)
      as [roots_tail0 [Htail0 Hroots_tail0]].
    exists Rout0, (root_sets_union (roots_head0 :: roots_tail0)).
    split; [| split; [| split]].
    + eapply TERS_Match; eauto.
      * eapply roots_exclude_params_equiv_local.
        -- apply root_set_equiv_sym. exact Hroots_head0.
        -- eapply roots_exclude_params_instantiate_local; eassumption.
      * eapply root_env_excludes_params_equiv_local.
        -- apply root_env_equiv_sym. exact HRout0.
        -- eapply root_env_excludes_params_instantiate_local; eassumption.
    + exact HnsRout0.
    + exact HRout0.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv.
        simpl. constructor.
        -- exact Hroots_head0.
        -- exact Hroots_tail0.
      * apply root_set_equiv_sym.
        apply root_sets_instantiate_union_equiv.
  - intros R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hcompat Hlookup_none Hexcl_roots1 Hexcl_env1
      He2 IHe2 Hcheck Hexcl_roots2 Hexcl_env2 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TERS_Let.
      * exact He10.
      * exact Hcompat.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hlookup_none Hexcl_roots1 Hexcl_env1
      He2 IHe2 Hcheck Hexcl_roots2 Hexcl_env2 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TERS_LetInfer.
      * exact He10.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R' Σ Σ' e T roots He IHe Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [He0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', []. split; [| split; [| split]].
    + apply TERS_Drop with (T := T) (roots := roots0). exact He0.
    + exact HnsR0'.
    + exact HR0'.
    + apply root_set_equiv_refl.
  - intros R R1 Σ Σ1 Σ2 p e_new T_old T_new x path roots_result
      roots_old roots_new Hplace Hpath Hwritable Hlookup_result He_new IHe_new
      Hlookup_old Hcompat Havailable Hrestore Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_result_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots_result)).
    { apply root_env_lookup_instantiate. exact Hlookup_result. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots_result) HR0 Hlookup_result_inst)
      as [roots_result0 [Hlookup_result0 Hroots_result0]].
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      roots_result0.
    split; [| split; [| split]].
    + eapply TERS_Replace_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + exact Hroots_result0.
  - intros R R1 Σ Σ' p e_new T_old T_new x path roots_old roots_new
      Hplace Husage Hpath Hwritable He_new IHe_new Hlookup_old Hcompat
      Havailable Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      [].
    split; [| split; [| split]].
    + eapply TERS_Assign_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + apply root_set_equiv_refl.
  - intros R Σ p T Hplace Hfresh R0 HnsR HnsR0 HR0.
    exists R0, (root_of_place p). split; [| split; [| split]].
    + constructor. exact Hplace.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_root_of_place_equiv.
  - intros R Σ p T x path Hplace Hpath Hmut Hfresh R0 HnsR HnsR0 HR0.
    exists R0, [RStore x]. split; [| split; [| split]].
    + eapply TERS_BorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_store_singleton_equiv.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_DerefBorrowShared; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hmut Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_DerefBorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3
      roots_cond roots2 roots3 He1 IHe1 Hcond He2 IHe2 He3 IHe3 Hcore
      Hmerge HR23 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1)
      (expr_local_store_names e2 ++ expr_local_store_names e3) rho
      Hfresh) as [Hfresh1 Hfresh23].
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e2) (expr_local_store_names e3) rho
      Hfresh23) as [Hfresh2 Hfresh3].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots_cond0 [He10 [HnsR10 [HR10 Hroots_cond0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He1.
      - exact HnsR. }
    destruct (IHe2 Hfresh2 R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    destruct (IHe3 Hfresh3 R10 Hns_R1 HnsR10 HR10)
      as [R30 [roots30 [He30 [HnsR30 [HR30 Hroots30]]]]].
    exists R20, (root_set_union roots20 roots30). split; [| split; [| split]].
    + eapply TERS_If; eauto.
      eapply root_env_equiv_trans.
      * exact HR20.
      * eapply root_env_equiv_trans.
        -- apply root_env_equiv_instantiate. exact HR23.
        -- apply root_env_equiv_sym. exact HR30.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + constructor.
  - intros R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest
      He IHe Hcompat Hes IHes Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_args_cons_inv
      e es rho Hfresh) as [Hfresh_e Hfresh_es].
    destruct (IHe Hfresh_e R0 HnsR HnsR0 HR0)
      as [R10 [roots0 [He0 [HnsR10 [HR10 Hroots0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He.
      - exact HnsR. }
    destruct (IHes Hfresh_es R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hes0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (roots0 :: roots_rest0). split; [| split; [| split]].
    + eapply TERSArgs_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + constructor; assumption.
  - intros lts args R Σ fields Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros lts args R R1 R2 Σ Σ1 Σ2 fields f rest e_field T_field
      roots_field roots_rest Hlookup He_field IHe_field Hcompat Hfields IHfields
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hfresh_field :
      root_subst_images_exclude_names (expr_local_store_names e_field) rho).
    { unfold lookup_field_b in Hlookup.
      clear Hfields IHfields.
      induction fields as [| [field_name0 e0] fields IH]; simpl in *;
        try discriminate.
      destruct (String.eqb (Program.field_name f) field_name0) eqn:Hfield.
      - inversion Hlookup. subst e0.
        apply root_subst_images_exclude_names_app_inv in Hfresh.
        exact (proj1 Hfresh).
      - apply IH.
        + exact Hlookup.
        + apply root_subst_images_exclude_names_app_inv in Hfresh.
          exact (proj2 Hfresh). }
    destruct (IHe_field Hfresh_field R0 HnsR HnsR0 HR0)
      as [R10 [roots_field0 [He_field0 [HnsR10 [HR10 Hroots_field0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He_field.
      - exact HnsR. }
    destruct (IHfields Hfresh R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hfields0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (root_set_union roots_field0 roots_rest0). split; [| split; [| split]].
    + eapply TERSFields_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros lts args R roots_scrut Σ branches expected_core R_out Hfresh
      roots_scrut0 R0 R0_out Hroots_scrut0 HnsR HnsR0 HnsR0_out HR0
      HR0_out.
    exists []. split.
    + constructor.
    + constructor.
	  - intros R R_payload Rv_payload Rv Σ branches v rest e T
	      Σv_payload Σv R_out roots Σs Ts rootss expected_core binders ps
	      lts args roots_scrut Hbinders Hpayload Hnodup
	      Hctx_fresh Hroot_fresh Hlookup HRpayload Htyped IHtyped Hparams_ok Hroots_excl HRv
      Henv_excl HΣv Hcore Heq_tail Htail IHtail Hfresh roots_scrut0
      R0 R0_out Hroots_scrut0 HnsR HnsR0 HnsR0_out HR0 HR0_out.
    assert (Hfresh_R0 : root_env_lookup_params_none_b ps R0 = true).
    { eapply root_env_lookup_params_none_b_instantiate_equiv; eassumption. }
    assert (Hfresh_ps :
      root_subst_images_exclude_names (ctx_names (params_ctx ps)) rho).
    {
      rewrite (match_payload_params_names binders lts args v ps Hpayload).
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh.
      - eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
    }
    assert (Hfresh_e :
      root_subst_images_exclude_names (expr_local_store_names e) rho).
    {
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh.
      - eapply lookup_expr_branch_local_store_names_in; eassumption.
    }
    assert (HnsRpayload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    pose (Rpayload0 := root_env_add_params_roots_same ps roots_scrut0 R0).
    assert (HnsRpayload0 : root_env_no_shadow Rpayload0).
    { unfold Rpayload0. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (HRpayload0 :
      root_env_equiv Rpayload0 (root_env_instantiate rho R_payload)).
    { subst R_payload. unfold Rpayload0.
      eapply root_env_add_params_roots_same_instantiate_equiv; eauto. }
    destruct (IHtyped Hfresh_e Rpayload0 HnsRpayload HnsRpayload0 HRpayload0)
      as [Rv_payload0 [roots0 [Htyped0 [Hns_payload0 [HR_payload0 Hroots0]]]]].
    assert (HnsRv_payload : root_env_no_shadow Rv_payload).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped.
      - exact HnsRpayload. }
    pose (Rv0 := root_env_remove_match_params ps Rv_payload0).
    assert (HnsRv0 : root_env_no_shadow Rv0).
    { unfold Rv0. apply root_env_remove_match_params_no_shadow. exact Hns_payload0. }
    assert (HRv0 : root_env_equiv Rv0 (root_env_instantiate rho Rv)).
    { subst Rv. unfold Rv0.
      eapply root_env_remove_match_params_instantiate_equiv; eauto. }
    destruct (IHtail Hfresh roots_scrut0 R0 R0_out Hroots_scrut0
      HnsR HnsR0 HnsR0_out HR0 HR0_out)
      as [rootss0 [Htail0 Hrootss0]].
    exists (roots0 :: rootss0). split.
    + eapply TERSMatchTail_Cons; eauto.
      * eapply roots_exclude_params_equiv_local.
        -- apply root_set_equiv_sym. exact Hroots0.
        -- eapply roots_exclude_params_instantiate_local; eassumption.
      * eapply root_env_excludes_params_equiv_local.
        -- apply root_env_equiv_sym. exact HRv0.
        -- eapply root_env_excludes_params_instantiate_local; eassumption.
      * eapply root_env_equiv_trans.
        -- exact HRv0.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_instantiate. exact Heq_tail.
           ++ apply root_env_equiv_sym. exact HR0_out.
    + simpl. constructor; assumption.
Qed.

Lemma typed_env_roots_shadow_safe_instantiate_fresh :
  forall env Ω n rho R Σ e T Σ' R' roots R0,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σ e T Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho R Σ e T Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (typed_roots_shadow_safe_instantiate_fresh_mutual env Ω n rho)
    R Σ e T Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_args_roots_shadow_safe_instantiate_fresh :
  forall env Ω n rho R Σ args ps Σ' R' roots R0,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_args_roots_shadow_safe env Ω n R0 Σ args ps Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      Forall2 root_set_equiv roots0 (map (root_set_instantiate rho) roots).
Proof.
  intros env Ω n rho R Σ args ps Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (typed_roots_shadow_safe_instantiate_fresh_mutual env Ω n rho))
    R Σ args ps Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_fields_roots_shadow_safe_instantiate_fresh :
  forall env Ω n rho lts args R Σ fields defs Σ' R' roots R0,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_fields_roots_shadow_safe env Ω n lts args R0 Σ fields defs
        Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho lts args R Σ fields defs Σ' R' roots R0
    Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (proj2 (typed_roots_shadow_safe_instantiate_fresh_mutual env Ω n rho)))
    lts args R Σ fields defs Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

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
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
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
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
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
  - match goal with
    | Htyped1 : typed_env_roots_shadow_safe env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      Hexpr : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ1,
      Hargs : root_env_no_shadow ?R1 ->
        root_env_sctx_keys_named ?R1 ?Σ1 ->
        root_env_sctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hexpr Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped1
              | exact Hrn]);
        exact (Hargs Hrn1 Hkeys1)
    end.
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
  - match goal with
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
  - match goal with
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
  - match goal with
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
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        root_set_sctx_roots_named ?roots ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
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
    eapply root_store_single_sctx_roots_named_of_place_path; eassumption.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
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

Lemma alpha_rename_typed_env_roots_call_expr_make_closure_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname captures args er used used'
    T Σ' R' roots,
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
  typed_env_roots_shadow_safe env Ω n R Σ
    (ECallExpr (EMakeClosure fname captures) args) T Σ' R' roots ->
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
  disjoint_names (free_vars_expr (ECallExpr (EMakeClosure fname captures) args))
    (rename_range rho) ->
  alpha_rename_expr rho used (ECallExpr (EMakeClosure fname captures) args) =
    (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname captures args er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l captures
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args) (rename_range rho) Hdisj) as [Hdisj_caps Hdisj_args].
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
  - exact Hdisj_args.
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_CallExpr_MakeClosure; eauto.
      eapply check_make_closure_captures_sctx_with_env_alpha_forward; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
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
	      + destruct e; try solve [inversion Htyped].
	        eapply alpha_rename_typed_env_roots_call_expr_make_closure_shadow_safe_support_forward.
        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_callexpr_arg_lt (EMakeClosure i l0) l e0 Hin)
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
          | Hlookup : root_env_lookup x ?R0 = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_ren :
                root_env_lookup (lookup_rename x rho)
                  (root_env_rename rho R0) =
                Some (root_set_rename rho roots));
              [ apply root_env_lookup_rename;
                [ apply HnocollR;
                  eapply root_env_lookup_some_in_names; exact Hlookup
                | exact Hlookup ]
              | destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R0)
                  (lookup_rename x rho) (root_set_rename rho roots)
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
          | Hlookup : root_env_lookup x ?R0 = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_ren :
                root_env_lookup (lookup_rename x rho)
                  (root_env_rename rho R0) =
                Some (root_set_rename rho roots));
              [ apply root_env_lookup_rename;
                [ apply HnocollR;
                  eapply root_env_lookup_some_in_names; exact Hlookup
                | exact Hlookup ]
              | destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R0)
                  (lookup_rename x rho) (root_set_rename rho roots)
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
                ** rewrite <- (place_path_root p x path ltac:(eassumption)).
                   exact Hsafe_root.
                ** eassumption.
             ++ exact Hlookup_r.
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
