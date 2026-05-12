From Facet.TypeSystem Require Import Lifetime Types Syntax TypingRules TypeChecker AlphaRenaming.
From Stdlib Require Import List String Bool Lia PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Auxiliary: bs_eqb ↔ equality                                         *)
(* ------------------------------------------------------------------ *)

Lemma bs_eqb_eq : forall bs1 bs2,
  bs_eqb bs1 bs2 = true <-> bs1 = bs2.
Proof.
  induction bs1 as [| e1 t1 IH]; intros bs2.
  - destruct bs2; simpl; split; intros H;
      [reflexivity | reflexivity | discriminate | discriminate].
  - destruct bs2 as [| e2 t2]; simpl; split; intros H; try discriminate.
    + apply andb_prop in H as [He Ht].
      destruct e1, e2; simpl in He;
        try discriminate;
        apply ident_eqb_eq in He; subst;
        apply IH in Ht; subst; reflexivity.
    + injection H as <- <-.
      apply andb_true_intro. split.
      * destruct e1; simpl; apply ident_eqb_refl.
      * apply IH. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Helper: inline go in ECall equals borrow_check_args                  *)
(* ------------------------------------------------------------------ *)

Lemma borrow_check_call_go : forall fenv Γ args BS BS',
  (fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
    match as_ with
    | [] => infer_ok BS0
    | a :: rest =>
        match borrow_check fenv BS0 Γ a with
        | infer_err err => infer_err err
        | infer_ok BS1  => go BS1 rest
        end
    end) BS args = infer_ok BS' <->
  borrow_check_args fenv BS Γ args = infer_ok BS'.
Proof.
  intros fenv Γ args.
  induction args as [| a rest IHargs]; intros BS BS'.
  - simpl. split; intros H; exact H.
  - simpl. split; intros H.
    + destruct (borrow_check fenv BS Γ a) as [BS1|] eqn:Ha; [|discriminate].
      apply IHargs. exact H.
    + destruct (borrow_check fenv BS Γ a) as [BS1|] eqn:Ha; [|discriminate].
      apply IHargs. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Soundness: borrow_check sound w.r.t. borrow_ok                       *)
(* ------------------------------------------------------------------ *)

Theorem borrow_check_sound : forall fenv BS Γ e BS',
  borrow_check fenv BS Γ e = infer_ok BS' ->
  borrow_ok fenv BS Γ e BS'.
Proof.
  assert (Hsize : forall n fenv BS Γ e BS',
    expr_size e < n ->
    borrow_check fenv BS Γ e = infer_ok BS' ->
    borrow_ok fenv BS Γ e BS').
  {
  induction n as [| n IH]; intros fenv BS Γ e BS' Hlt Hcheck.
  - lia.
  - destruct e; simpl in Hcheck.

  (* EUnit *)
  + injection Hcheck as <-. constructor.

  (* ELit *)
  + injection Hcheck as <-. constructor.

  (* EVar *)
  + injection Hcheck as <-. constructor.

  (* ELet *)
  + destruct (borrow_check fenv BS Γ e1) as [BS1|] eqn:He1; [|discriminate].
    destruct (borrow_check fenv BS1 (ctx_add_b i t m Γ) e2) as [BS2|] eqn:He2;
      [|discriminate].
    injection Hcheck as <-.
    apply BO_Let.
    * apply IH with (e := e1). simpl in Hlt; lia. exact He1.
    * apply IH with (e := e2). simpl in Hlt; lia.
      unfold ctx_add_b in He2. exact He2.

  (* ELetInfer *)
  + destruct (borrow_check fenv BS Γ e1) as [BS1|] eqn:He1; [|discriminate].
    destruct (borrow_check fenv BS1 Γ e2) as [BS2|] eqn:He2; [|discriminate].
    injection Hcheck as <-.
    apply BO_LetInfer.
    * apply IH with (e := e1). simpl in Hlt; lia. exact He1.
    * apply IH with (e := e2). simpl in Hlt; lia. exact He2.

  (* ECall *)
  + apply BO_Call.
    apply borrow_check_call_go in Hcheck.
    revert BS BS' Hcheck.
    induction l as [| a rest IHargs]; intros BS BS' Hcheck.
    * simpl in Hcheck. injection Hcheck as <-. constructor.
    * simpl in Hcheck.
      destruct (borrow_check fenv BS Γ a) as [BS1|] eqn:Ha; [|discriminate].
      apply BO_Args_Cons with (BS1 := BS1).
      -- apply IH with (e := a).
         pose proof (expr_size_call_arg_lt i (a :: rest) a (or_introl eq_refl)) as Harg_lt.
         simpl in Hlt. lia.
         exact Ha.
      -- apply IHargs; [simpl; simpl in Hlt; lia | exact Hcheck].
  (* EReplace *)
  + destruct p as [x | q].
    * apply BO_Replace.
      apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.
    * destruct q as [rv | q2].
      -- (* EReplace (PDeref (PVar rv)) e: new freeze check *)
         simpl in Hcheck.
         destruct (bs_has_any rv BS) eqn:Hany; [discriminate|].
         apply BO_Replace_Deref.
         ** unfold bs_can_mut. exact Hany.
         ** apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.
      -- discriminate.

  (* EAssign *)
  + destruct p as [x | q].
    * apply BO_Assign.
      apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.
    * destruct q as [rv | q2].
      -- (* EAssign (PDeref (PVar rv)) e: new freeze check *)
         simpl in Hcheck.
         destruct (bs_has_any rv BS) eqn:Hany; [discriminate|].
         apply BO_Assign_Deref.
         ** unfold bs_can_mut. exact Hany.
         ** apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.
      -- discriminate.

  (* EBorrow *)
  + destruct r; destruct p as [x | q].
    * (* RShared, PVar → BO_BorrowShared *)
      destruct (bs_has_mut x BS) eqn:Hmut; [discriminate|].
      injection Hcheck as <-.
      apply BO_BorrowShared. unfold bs_can_shared. exact Hmut.
    * (* RShared, PDeref q *)
      destruct q as [rv | q2].
      -- (* RShared, PDeref (PVar rv) → BO_ReBorrowShared *)
         destruct (bs_has_mut rv BS) eqn:Hmut; [discriminate|].
         injection Hcheck as <-.
         apply BO_ReBorrowShared. unfold bs_can_shared. exact Hmut.
      -- discriminate.
    * (* RUnique, PVar → BO_BorrowMut *)
      destruct (bs_has_any x BS) eqn:Hany; [discriminate|].
      injection Hcheck as <-.
      apply BO_BorrowMut. unfold bs_can_mut. exact Hany.
    * (* RUnique, PDeref q *)
      destruct q as [rv | q2].
      -- (* RUnique, PDeref (PVar rv) → BO_ReBorrowMut *)
         destruct (bs_has_any rv BS) eqn:Hany; [discriminate|].
         injection Hcheck as <-.
         apply BO_ReBorrowMut. unfold bs_can_mut. exact Hany.
      -- discriminate.

  (* EDeref *)
  + destruct e as [| | r | | | | | | | | |].
    (* goal 3 = EVar r: need freeze check *)
    3: { simpl in Hcheck.
         destruct (bs_has_mut r BS) eqn:Hmut; [discriminate|].
         injection Hcheck as <-.
         apply BO_Deref.
         - unfold borrow_ok_deref_check, bs_can_shared. exact Hmut.
         - apply BO_Var. }
    (* all non-EVar cases: borrow_ok_deref_check = True, recurse *)
    all: (simpl in Hcheck;
          apply BO_Deref; [ exact I
                          | apply IH; [ simpl in Hlt |- *; lia | exact Hcheck ] ]).

  (* EDrop *)
  + apply BO_Drop.
    apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.

  (* EIf *)
  + destruct (borrow_check fenv BS Γ e1) as [BS1|] eqn:He1; [|discriminate].
    destruct (borrow_check fenv BS1 Γ e2) as [BS2|] eqn:He2; [|discriminate].
    destruct (borrow_check fenv BS1 Γ e3) as [BS3|] eqn:He3; [|discriminate].
    destruct (bs_eqb BS2 BS3) eqn:Heqb; [|discriminate].
    injection Hcheck as <-.
    apply bs_eqb_eq in Heqb.
    eapply BO_If.
    * apply IH with (e := e1). simpl in Hlt; lia. exact He1.
    * apply IH with (e := e2). simpl in Hlt; lia. exact He2.
    * apply IH with (e := e3). simpl in Hlt; lia. exact He3.
    * exact Heqb.

  }
  intros fenv BS Γ e BS' Hcheck.
  apply Hsize with (n := S (expr_size e)); [lia | exact Hcheck].
Qed.

(* ------------------------------------------------------------------ *)
(* Completeness: borrow_ok implies borrow_check returns infer_ok        *)
(* ------------------------------------------------------------------ *)

Scheme borrow_ok_mut := Induction for borrow_ok Sort Prop
  with borrow_ok_args_mut := Induction for borrow_ok_args Sort Prop.

Theorem borrow_check_complete : forall fenv BS Γ e BS',
  borrow_ok fenv BS Γ e BS' ->
  borrow_check fenv BS Γ e = infer_ok BS'.
Proof.
  intro fenv.
  apply (borrow_ok_mut fenv
    (fun BS Γ e BS' _ =>
       borrow_check fenv BS Γ e = infer_ok BS')
    (fun BS Γ args BS' _ =>
       borrow_check_args fenv BS Γ args = infer_ok BS')).

  (* BO_Unit *)
  - intros. reflexivity.

  (* BO_Lit *)
  - intros. reflexivity.

  (* BO_Var *)
  - intros. reflexivity.

  (* BO_BorrowShared *)
  - intros BS Γ x Hcan.
    simpl. unfold bs_can_shared in Hcan. rewrite Hcan. reflexivity.

  (* BO_BorrowMut *)
  - intros BS Γ x Hcan.
    simpl. unfold bs_can_mut in Hcan. rewrite Hcan. reflexivity.

  (* BO_Deref *)
  - intros BS BS' Γ e Hfreeze _ IH.
    (* destruct inner expr: EVar r vs all others *)
    destruct e as [| | r | | | | | | | | |].
    all: try (simpl; exact IH).
    (* EVar r case: borrow_check returns infer_ok BS, need to show rewrite works *)
    simpl.
    unfold borrow_ok_deref_check, bs_can_shared in Hfreeze.
    rewrite Hfreeze. exact IH.

  (* BO_Drop *)
  - intros BS BS' Γ e _ IH.
    simpl. exact IH.

  (* BO_Replace *)
  - intros BS BS' Γ x e_new _ IH.
    simpl. exact IH.

  (* BO_Assign *)
  - intros BS BS' Γ x e_new _ IH.
    simpl. exact IH.

  (* BO_Replace_Deref *)
  - intros BS BS' Γ r e_new Hcanmut _ IH.
    simpl. unfold bs_can_mut in Hcanmut. rewrite Hcanmut. exact IH.

  (* BO_Assign_Deref *)
  - intros BS BS' Γ r e_new Hcanmut _ IH.
    simpl. unfold bs_can_mut in Hcanmut. rewrite Hcanmut. exact IH.

  (* BO_ReBorrowShared *)
  - intros BS Γ r Hcan.
    simpl. unfold bs_can_shared in Hcan. rewrite Hcan. reflexivity.

  (* BO_ReBorrowMut *)
  - intros BS Γ r Hcan.
    simpl. unfold bs_can_mut in Hcan. rewrite Hcan. reflexivity.

  (* BO_Let *)
  - intros BS BS1 BS2 Γ m x T e1 e2 _ IH1 _ IH2.
    simpl. rewrite IH1.
    change (ctx_add_b x T m Γ) with (ctx_add x T m Γ).
    rewrite IH2. reflexivity.

  (* BO_LetInfer *)
  - intros BS BS1 BS2 Γ m x e1 e2 _ IH1 _ IH2.
    simpl. rewrite IH1. rewrite IH2. reflexivity.

  (* BO_If *)
  - intros BS BS1 BS2 BS3 Γ e1 e2 e3 _ IH1 _ IH2 _ IH3 Heq.
    subst BS3.
    simpl. rewrite IH1. rewrite IH2. rewrite IH3.
    rewrite (proj2 (bs_eqb_eq BS2 BS2) eq_refl). reflexivity.

  (* BO_Call *)
  - intros BS BS' Γ fname args _ IHargs.
    simpl.
    apply borrow_check_call_go.
    exact IHargs.

  (* BO_Args_Nil *)
  - intros. reflexivity.

  (* BO_Args_Cons *)
  - intros BS BS1 BS2 Γ a rest _ IHa _ IHrest.
    simpl. rewrite IHa. exact IHrest.
Qed.

