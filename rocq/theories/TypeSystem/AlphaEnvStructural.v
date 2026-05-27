From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Environment structural alpha-renaming proofs                        *)
(* ------------------------------------------------------------------ *)

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

