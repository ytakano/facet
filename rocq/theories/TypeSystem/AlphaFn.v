From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Function environment alpha-renaming relations                       *)
(* ------------------------------------------------------------------ *)

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
          end) used0 l0) as r eqn:Hargs.
    destruct r as [argsr used_args].
    injection Hrename as _ <-.
    eapply alpha_rename_call_args_used_extends.
    * intros used_arg earg er0 used_tail Hin_arg Hrename0.
      eapply IH.
      -- pose proof (expr_size_callexpr_generic_arg_lt e l l0 earg Hin_arg)
          as Harg_lt.
        assert (expr_size earg < n) as Hlt_arg by lia.
        exact Hlt_arg.
      -- exact Hrename0.
    * symmetry. exact Hargs.
    * eapply IH.
      -- pose proof (expr_size_callexpr_generic_callee_lt e l l0) as Hcallee_lt.
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
          end) used l2) as r eqn:Hpayloads.
    destruct r as [payloadsr used_payloads].
    injection Hrename as _ <-.
    eapply alpha_rename_call_args_used_extends.
    * intros used_arg epayload er0 used_tail Hin_payload Hrename0.
      eapply IH.
      -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 l2 epayload Hin_payload)
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
            end) used0 l0) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_call_expr_generic in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply alpha_rename_call_args_used_extends.
        -- intros used_arg earg er0 used_tail Hin_arg Hrename0.
           eapply alpha_rename_expr_used_extends. exact Hrename0.
        -- symmetry. exact Hargs.
        -- eapply IH.
           ++ pose proof (expr_size_callexpr_generic_callee_lt e l l0) as Hcallee_lt.
              assert (expr_size e < n) as Hlt_callee by lia. exact Hlt_callee.
           ++ exact Hcallee.
           ++ exact Hin.
      * eapply alpha_rename_call_args_local_store_names_in_used.
        -- intros used_arg earg er0 used_tail Hin_arg Hrename0.
           eapply IH.
           ++ pose proof (expr_size_callexpr_generic_arg_lt e l l0 earg Hin_arg) as Harg_lt.
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
            end) used l2) as r eqn:Hpayloads.
      destruct r as [payloadsr used_payloads].
      injection Hrename as <- <-.
      rewrite expr_local_store_names_enum in Hin.
      eapply alpha_rename_call_args_local_store_names_in_used.
      * intros used_arg epayload er0 used_tail Hin_payload Hrename0.
        eapply IH.
        -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 l2 epayload Hin_payload)
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
            end) used0 l0) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call_expr_generic.
      apply Forall_app. split.
      * eapply IH.
        -- pose proof (expr_size_callexpr_generic_callee_lt e l l0) as Hcallee_lt.
           assert (expr_size e < n) as Hlt_callee by lia.
           exact Hlt_callee.
        -- exact Hcallee.
      * eapply Forall_fresh_weaken.
        -- intros x Hin.
           eapply alpha_rename_expr_used_extends; eauto.
        -- eapply alpha_rename_call_args_local_store_names_fresh_used.
           ++ intros used_arg earg er0 used_tail Hin_arg Hrename0.
              eapply IH.
              ** pose proof (expr_size_callexpr_generic_arg_lt e l l0 earg Hin_arg)
                    as Harg_lt.
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
            end) used l2) as r eqn:Hpayloads.
      destruct r as [payloadsr used_payloads].
      injection Hrename as <- _.
      rewrite expr_local_store_names_enum.
      eapply alpha_rename_call_args_local_store_names_fresh_used.
      * intros used0 epayload er0 used1 Hin_payload Hrename0.
        eapply IH.
        -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 l2 epayload Hin_payload)
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
            end) used0 l0) as r eqn:Hargs.
      destruct r as [argsr used_args].
      injection Hrename as <- _.
      rewrite expr_local_store_names_call_expr_generic.
      eapply NoDup_app_from_Forall.
      * eapply IH.
        -- pose proof (expr_size_callexpr_generic_callee_lt e l l0) as Hcallee_lt.
           assert (expr_size e < n) as Hlt_callee by lia. exact Hlt_callee.
        -- exact Hcallee.
      * eapply alpha_rename_call_args_local_store_names_nodup.
        -- intros used_arg earg er0 used_tail Hin_arg Hrename0.
           eapply IH.
           ++ pose proof (expr_size_callexpr_generic_arg_lt e l l0 earg Hin_arg) as Harg_lt.
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
            end) used l2) as r eqn:Hpayloads.
      destruct r as [payloadsr used_payloads].
      injection Hrename as <- _.
      rewrite expr_local_store_names_enum.
      eapply alpha_rename_call_args_local_store_names_nodup.
      * intros used0 epayload er0 used1 Hin_payload Hrename0.
        eapply IH.
        -- pose proof (expr_size_enum_payload_lt s s0 l l0 l1 l2 epayload Hin_payload)
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

