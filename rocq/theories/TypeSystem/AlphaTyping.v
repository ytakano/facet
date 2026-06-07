From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Typing alpha-renaming facts                                         *)
(* ------------------------------------------------------------------ *)

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
  - destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used0 l0).
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
                 end) used l2).
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
  - destruct (alpha_rename_expr ρ used e) as [er0 used0].
    destruct ((fix go (used0 : list ident) (args0 : list expr)
                : list expr * list ident :=
                 match args0 with
                 | [] => ([], used0)
                 | arg :: rest =>
                     let (arg', used1) := alpha_rename_expr ρ used0 arg in
                     let (rest', used2) := go used1 rest in
                     (arg' :: rest', used2)
                 end) used0 l0).
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
                 end) used l2).
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

