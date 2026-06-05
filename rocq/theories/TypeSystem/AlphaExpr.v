From Facet.TypeSystem Require Import Types Syntax Renaming ExprFacts.
From Facet.TypeSystem Require Import AlphaCore AlphaPlace.
From Stdlib Require Import List String Bool Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Expression alpha-renaming relations                                 *)
(* ------------------------------------------------------------------ *)

Inductive binders_alpha :
    rename_env -> list ident -> list ident -> rename_env -> Prop :=
  | BA_Nil : forall ρ,
      binders_alpha ρ [] [] ρ
  | BA_Cons : forall ρ x xr xs xsr ρ_branch,
      ~ In xr xsr ->
      binders_alpha ρ xs xsr ρ_branch ->
      binders_alpha ρ (x :: xs) (xr :: xsr) ((x, xr) :: ρ_branch).

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
  | EA_CallExprGeneric : forall ρ callee calleer type_args args argsr,
      expr_alpha ρ callee calleer ->
      exprs_alpha ρ args argsr ->
      expr_alpha ρ
        (ECallExprGeneric callee type_args args)
        (ECallExprGeneric calleer type_args argsr)
  | EA_Struct : forall ρ name lts args fields fieldsr,
      fields_alpha ρ fields fieldsr ->
      expr_alpha ρ (EStruct name lts args fields) (EStruct name lts args fieldsr)
  | EA_Enum : forall ρ enum_name variant_name lts args payloads payloadsr,
      exprs_alpha ρ payloads payloadsr ->
      expr_alpha ρ
        (EEnum enum_name variant_name lts args payloads)
        (EEnum enum_name variant_name lts args payloadsr)
  | EA_Match : forall ρ scrut scrutr branches branchesr,
      expr_alpha ρ scrut scrutr ->
      branches_alpha ρ branches branchesr ->
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
      exprs_alpha ρ (e :: es) (er :: esr)
with fields_alpha : rename_env -> list (string * expr) -> list (string * expr) -> Prop :=
  | FAs_Nil : forall ρ,
      fields_alpha ρ [] []
  | FAs_Cons : forall ρ name e er fields fieldsr,
      expr_alpha ρ e er ->
      fields_alpha ρ fields fieldsr ->
      fields_alpha ρ ((name, e) :: fields) ((name, er) :: fieldsr)
with branches_alpha : rename_env ->
    list (string * list ident * expr) ->
    list (string * list ident * expr) -> Prop :=
  | BrA_Nil : forall ρ,
      branches_alpha ρ [] []
  | BrA_Cons : forall ρ variant binders bindersr body bodyr rest restr ρ_branch,
      binders_alpha ρ binders bindersr ρ_branch ->
      expr_alpha ρ_branch body bodyr ->
      branches_alpha ρ rest restr ->
      branches_alpha ρ
        ((variant, binders, body) :: rest)
        ((variant, bindersr, bodyr) :: restr).

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

Lemma alpha_rename_struct_fields_sound : forall ρ used fields fieldsr used' ,
  (forall used0 fname e er used1,
      In (fname, e) fields ->
      disjoint_names (free_vars_expr e) (rename_range ρ) ->
      alpha_rename_expr ρ used0 e = (er, used1) ->
      expr_alpha ρ e er) ->
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
  fields_alpha ρ fields fieldsr.
Proof.
  intros ρ used fields.
  revert used.
  induction fields as [| [fname e] rest IH];
    intros used fieldsr used' Hexpr Hdisj Hrename; simpl in Hrename.
  - injection Hrename as <- _. constructor.
  - destruct (disjoint_names_app_l (free_vars_expr e)
      ((fix go (fields0 : list (string * expr)) : list ident :=
          match fields0 with
          | [] => []
          | (_, e0) :: rest0 => free_vars_expr e0 ++ go rest0
          end) rest) (rename_range ρ) Hdisj) as [Hdisj_e Hdisj_rest].
    destruct (alpha_rename_expr ρ used e) as [er used1] eqn:He.
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
    constructor.
    + eapply Hexpr.
      * left. reflexivity.
      * exact Hdisj_e.
      * exact He.
    + eapply IH.
      * intros used0 fname0 e0 er0 used_tail Hin Hdisj0 Hrename0.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Hdisj0.
        -- exact Hrename0.
      * exact Hdisj_rest.
      * exact Hrest.
Qed.


Lemma alpha_rename_idents_binders_alpha :
  forall ρ used binders bindersr ρ' used',
    alpha_rename_idents ρ used binders = (bindersr, ρ', used') ->
    binders_alpha ρ binders bindersr ρ'.
Proof.
  intros ρ used binders.
  revert ρ used.
  induction binders as [| x xs IH]; intros ρ used bindersr ρ' used' Hrename;
    simpl in Hrename.
  - injection Hrename as <- <- _. constructor.
  - destruct (alpha_rename_idents ρ (fresh_ident x used :: used) xs)
      as [[xsr ρ_tail] used_tail] eqn:Htail.
    injection Hrename as <- <- _.
    constructor.
    + pose proof (alpha_rename_idents_fresh_used _ _ _ _ _ _ Htail)
        as Hfresh.
      rewrite Forall_forall in Hfresh.
      intros Hin.
      specialize (Hfresh (fresh_ident x used) Hin).
      apply Hfresh. left. reflexivity.
    + eapply IH. exact Htail.
Qed.

Lemma alpha_rename_idents_range :
  forall ρ used binders bindersr ρ' used',
    alpha_rename_idents ρ used binders = (bindersr, ρ', used') ->
    forall x, In x (rename_range ρ') -> In x bindersr \/ In x (rename_range ρ).
Proof.
  intros ρ used binders.
  revert ρ used.
  induction binders as [| b bs IH]; intros ρ used bindersr ρ' used' Hrename x Hin;
    simpl in Hrename.
  - injection Hrename as <- <- _. right. exact Hin.
  - destruct (alpha_rename_idents ρ (fresh_ident b used :: used) bs)
      as [[bsr ρ_tail] used_tail] eqn:Htail.
    injection Hrename as <- <- _.
    simpl in Hin. destruct Hin as [Hx | Hin].
    + subst x. left. left. reflexivity.
    + destruct (IH _ _ _ _ _ Htail x Hin) as [Hbs | Hrange].
      * left. right. exact Hbs.
      * right. exact Hrange.
Qed.

Lemma alpha_rename_idents_branch_body_disjoint :
  forall ρ used binders bindersr ρ_branch used' e,
    alpha_rename_idents ρ (binders ++ free_vars_expr e ++ used) binders =
      (bindersr, ρ_branch, used') ->
    disjoint_names (free_vars_expr e) (rename_range ρ) ->
    disjoint_names (free_vars_expr e) (rename_range ρ_branch).
Proof.
  intros ρ used binders bindersr ρ_branch used' e Hrename Hdisj x Hin Hrange.
  destruct (alpha_rename_idents_range _ _ _ _ _ _ Hrename x Hrange)
    as [Hin_bindersr | Hin_range].
  - pose proof (alpha_rename_idents_fresh_used _ _ _ _ _ _ Hrename)
      as Hfresh.
    rewrite Forall_forall in Hfresh.
    specialize (Hfresh x Hin_bindersr).
    apply Hfresh.
    apply in_or_app. right. apply in_or_app. left. exact Hin.
  - exact (Hdisj x Hin Hin_range).
Qed.

Lemma alpha_rename_match_branches_sound :
  forall ρ used branches branchesr used',
  (forall ρ0 used0 name binders e er used1,
      In (name, binders, e) branches ->
      disjoint_names (free_vars_expr e) (rename_range ρ0) ->
      alpha_rename_expr ρ0 used0 e = (er, used1) ->
      expr_alpha ρ0 e er) ->
  disjoint_names
    ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
        match branches0 with
        | [] => []
        | (_, _, e) :: rest => free_vars_expr e ++ go rest
        end) branches)
    (rename_range ρ) ->
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
  branches_alpha ρ branches branchesr.
Proof.
  intros ρ used branches.
  revert used.
  induction branches as [| [[name binders] e] rest IH];
    intros used branchesr used' Hexpr Hdisj Hrename; simpl in Hrename.
  - injection Hrename as <- _. constructor.
  - destruct (disjoint_names_app_l (free_vars_expr e)
      ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
          match branches0 with
          | [] => []
          | (_, _, e0) :: rest0 => free_vars_expr e0 ++ go rest0
          end) rest) (rename_range ρ) Hdisj) as [Hdisj_e Hdisj_rest].
    set (binder_seed := binders ++ free_vars_expr e ++ used).
    destruct (alpha_rename_idents ρ binder_seed binders)
      as [[bindersr ρ_branch] used1] eqn:Hbinders.
    destruct (alpha_rename_expr ρ_branch used1 e) as [er used2] eqn:He.
    subst binder_seed.
    simpl in Hrename. rewrite Hbinders in Hrename. rewrite He in Hrename.
    destruct ((fix go (used0 : list ident)
          (branches0 : list (string * list ident * expr))
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used0)
          | (name0, binders0, e0) :: rest0 =>
              let binder_seed0 := binders0 ++ free_vars_expr e0 ++ used0 in
              let '(binders0', ρ_branch0, used3) :=
                alpha_rename_idents ρ binder_seed0 binders0 in
              let (e0', used4) := alpha_rename_expr ρ_branch0 used3 e0 in
              let (rest', used5) := go used4 rest0 in
              ((name0, binders0', e0') :: rest', used5)
          end) used2 rest) as [restr used3] eqn:Hrest.
    injection Hrename as <- _.
    eapply BrA_Cons with (ρ_branch := ρ_branch).
    + eapply alpha_rename_idents_binders_alpha. exact Hbinders.
    + eapply Hexpr.
      * left. reflexivity.
      * eapply alpha_rename_idents_branch_body_disjoint.
        -- exact Hbinders.
        -- exact Hdisj_e.
      * exact He.
    + eapply IH.
      * intros ρ0 used0 name0 binders0 e0 er0 used_tail Hin Hdisj0 Hrename0.
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
  + destruct (disjoint_names_app_l (free_vars_expr e)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg :: rest => free_vars_expr arg ++ go rest
          end) l0) (rename_range ρ) Hdisj) as [Hdisj_callee Hdisj_args].
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
          end) used0 l0) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as <- _.
    constructor.
    * eapply IH.
      -- pose proof (expr_size_callexpr_generic_callee_lt e l l0) as Hcallee_lt.
         assert (expr_size e < n) as Hlt_callee by lia.
         exact Hlt_callee.
      -- exact Hdisj_callee.
      -- exact Hcallee.
    * eapply alpha_rename_call_args_sound.
      -- intros used_arg earg er0 used_tail Hin_arg Hdisj0 Hrename0.
         eapply IH.
         ++ pose proof (expr_size_callexpr_generic_arg_lt e l l0 earg Hin_arg) as Harg_lt.
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
		    eapply alpha_rename_struct_fields_sound.
		    * intros used0 fname field_expr er0 used1 Hin Hdisj0 Hrename0.
		      eapply IH.
		      -- pose proof (expr_size_struct_field_lt s l l0 l1 fname field_expr Hin)
		           as Hfield_lt.
		         assert (expr_size field_expr < n) as Hlt_field by lia.
		         exact Hlt_field.
		      -- exact Hdisj0.
		      -- exact Hrename0.
		    * exact Hdisj.
		    * symmetry. exact Hfields.
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
			    * eapply IH.
			      -- pose proof (expr_size_match_scrutinee_lt e l) as Hscrut_lt.
			         assert (expr_size e < n) as Hlt_scrut by lia.
			         exact Hlt_scrut.
			      -- destruct (disjoint_names_app_l (free_vars_expr e)
			           ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
			               match branches0 with
			               | [] => []
			               | (_, _, e0) :: rest => free_vars_expr e0 ++ go rest
			               end) l) (rename_range ρ) Hdisj) as [Hdisj_scrut _].
			         exact Hdisj_scrut.
			      -- exact Hscrut.
			    * eapply alpha_rename_match_branches_sound.
			      -- intros ρ0 used_branch variant binders branch branchr used_tail
			           Hin Hdisj_branch Hrename_branch.
			         eapply IH.
			         ++ pose proof (expr_size_match_branch_lt e l variant binders branch Hin)
			              as Hbranch_lt.
			            assert (expr_size branch < n) as Hlt_branch by lia.
			            exact Hlt_branch.
			         ++ exact Hdisj_branch.
			         ++ exact Hrename_branch.
			      -- destruct (disjoint_names_app_l (free_vars_expr e)
			           ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
			               match branches0 with
			               | [] => []
			               | (_, _, e0) :: rest => free_vars_expr e0 ++ go rest
			               end) l) (rename_range ρ) Hdisj) as [_ Hdisj_branches].
			         exact Hdisj_branches.
			      -- symmetry. exact Hbranches.
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


Lemma params_alpha_length :
  forall ps psr,
    params_alpha ps psr ->
    List.length ps = List.length psr.
Proof.
  intros ps psr Halpha.
  induction Halpha; simpl; congruence.
Qed.

