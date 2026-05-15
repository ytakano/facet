From Facet.TypeSystem Require Import Lifetime Types Syntax PathState TypingRules
  TypeChecker EnvStructuralRules AlphaRenaming.
From Stdlib Require Import List String Bool Lia PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Auxiliary: path-borrow equality checks                               *)
(* ------------------------------------------------------------------ *)

Lemma path_eqb_eq : forall p q,
  path_eqb p q = true <-> p = q.
Proof.
  induction p as [| x xs IH]; intros q.
  - destruct q as [| y ys]; simpl; split; intros H;
      [reflexivity | reflexivity | discriminate | discriminate].
  - destruct q as [| y ys]; simpl; split; intros H; try discriminate.
    + apply andb_prop in H as [Hxy Hxs].
      unfold path_segment_eqb in Hxy.
      apply String.eqb_eq in Hxy.
      apply IH in Hxs.
      subst. reflexivity.
    + injection H as <- <-.
      apply andb_true_intro. split.
      * unfold path_segment_eqb. apply String.eqb_refl.
      * apply IH. reflexivity.
Qed.

Lemma path_borrow_entry_eqb_eq : forall a b,
  path_borrow_entry_eqb a b = true <-> a = b.
Proof.
  intros a b.
  destruct a as [x p | x p], b as [y q | y q]; simpl; split; intros H;
    try discriminate.
  - apply andb_prop in H as [Hxy Hpq].
    apply ident_eqb_eq in Hxy.
    apply path_eqb_eq in Hpq.
    subst. reflexivity.
  - injection H as <- <-.
    apply andb_true_intro. split.
    + apply ident_eqb_refl.
    + apply path_eqb_eq. reflexivity.
  - apply andb_prop in H as [Hxy Hpq].
    apply ident_eqb_eq in Hxy.
    apply path_eqb_eq in Hpq.
    subst. reflexivity.
  - injection H as <- <-.
    apply andb_true_intro. split.
    + apply ident_eqb_refl.
    + apply path_eqb_eq. reflexivity.
Qed.

Lemma pbs_eqb_eq : forall PBS1 PBS2,
  pbs_eqb PBS1 PBS2 = true <-> PBS1 = PBS2.
Proof.
  induction PBS1 as [| e1 rest1 IH]; intros PBS2.
  - destruct PBS2 as [| e2 rest2]; simpl; split; intros H;
      [reflexivity | reflexivity | discriminate | discriminate].
  - destruct PBS2 as [| e2 rest2]; simpl; split; intros H; try discriminate.
    + apply andb_prop in H as [He Hrest].
      apply path_borrow_entry_eqb_eq in He.
      apply IH in Hrest.
      subst. reflexivity.
    + injection H as <- <-.
      apply andb_true_intro. split.
      * apply path_borrow_entry_eqb_eq. reflexivity.
      * apply IH. reflexivity.
Qed.

Lemma pbs_has_mut_false_no_conflict : forall x p PBS y q,
  pbs_has_mut x p PBS = false ->
  In (PBMut y q) PBS ->
  ident_eqb x y && path_conflict_b p q = false.
Proof.
  intros x p PBS.
  induction PBS as [| e rest IH]; intros y q Hhas Hin.
  - contradiction.
  - simpl in Hhas. destruct e as [z r | z r].
    + destruct Hin as [Hin | Hin]; [discriminate |].
      apply IH; exact Hhas || exact Hin.
    + apply orb_false_iff in Hhas as [Hhead Hrest].
      destruct Hin as [Hin | Hin].
      * injection Hin as <- <-. exact Hhead.
      * apply IH; assumption.
Qed.

Lemma pbs_has_any_false_no_shared_conflict : forall x p PBS y q,
  pbs_has_any x p PBS = false ->
  In (PBShared y q) PBS ->
  ident_eqb x y && path_conflict_b p q = false.
Proof.
  intros x p PBS.
  induction PBS as [| e rest IH]; intros y q Hhas Hin.
  - contradiction.
  - simpl in Hhas. apply orb_false_iff in Hhas as [Hhead Hrest].
    destruct e as [z r | z r]; destruct Hin as [Hin | Hin].
    + injection Hin as <- <-. exact Hhead.
    + apply IH; assumption.
    + discriminate.
    + apply IH; assumption.
Qed.

Lemma pbs_has_any_false_no_mut_conflict : forall x p PBS y q,
  pbs_has_any x p PBS = false ->
  In (PBMut y q) PBS ->
  ident_eqb x y && path_conflict_b p q = false.
Proof.
  intros x p PBS.
  induction PBS as [| e rest IH]; intros y q Hhas Hin.
  - contradiction.
  - simpl in Hhas. apply orb_false_iff in Hhas as [Hhead Hrest].
    destruct e as [z r | z r]; destruct Hin as [Hin | Hin].
    + discriminate.
    + apply IH; assumption.
    + injection Hin as <- <-. exact Hhead.
    + apply IH; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Soundness: borrow_check_env agrees with structural borrow rules       *)
(* ------------------------------------------------------------------ *)

Theorem borrow_check_env_structural_sound : forall env PBS Γ e PBS',
  borrow_check_env env PBS Γ e = infer_ok PBS' ->
  borrow_ok_env_structural env PBS Γ e PBS'.
Proof.
  assert (Hsize : forall n env PBS Γ e PBS',
    expr_size e < n ->
    borrow_check_env env PBS Γ e = infer_ok PBS' ->
    borrow_ok_env_structural env PBS Γ e PBS').
  {
  induction n as [| n IH]; intros env PBS Γ e PBS' Hlt Hcheck.
  - lia.
  - destruct e; simpl in Hcheck.

  (* EUnit *)
  + injection Hcheck as <-. constructor.

  (* ELit *)
  + injection Hcheck as <-. constructor.

  (* EVar *)
  + destruct (borrow_check_place_access env PBS Γ (PVar i)) as [[] | err] eqn:Haccess;
      try discriminate.
    injection Hcheck as <-. constructor. exact Haccess.

  (* ELet *)
  + destruct (borrow_check_env env PBS Γ e1) as [PBS1|] eqn:He1; [|discriminate].
    destruct (borrow_check_env env PBS1 (ctx_add_b i t m Γ) e2) as [PBS2|] eqn:He2;
      [|discriminate].
    injection Hcheck as <-.
    apply BOES_Let.
    * apply IH with (e := e1). simpl in Hlt; lia. exact He1.
    * apply IH with (e := e2). simpl in Hlt; lia. exact He2.

  (* ELetInfer *)
  + destruct (borrow_check_env env PBS Γ e1) as [PBS1|] eqn:He1; [|discriminate].
    destruct (borrow_check_env env PBS1 Γ e2) as [PBS2|] eqn:He2; [|discriminate].
    injection Hcheck as <-.
    apply BOES_LetInfer.
    * apply IH with (e := e1). simpl in Hlt; lia. exact He1.
    * apply IH with (e := e2). simpl in Hlt; lia. exact He2.

  (* EFn *)
  + injection Hcheck as <-. constructor.

  (* EPlace *)
  + destruct (borrow_check_place_access env PBS Γ p) as [[] | err] eqn:Haccess;
      try discriminate.
    injection Hcheck as <-. constructor. exact Haccess.

  (* ECall *)
  + apply BOES_Call.
    revert PBS PBS' Hcheck.
    induction l as [| a rest IHargs]; intros PBS PBS' Hcheck.
    * simpl in Hcheck. injection Hcheck as <-. constructor.
    * simpl in Hcheck.
      destruct (borrow_check_env env PBS Γ a) as [PBS1|] eqn:Ha; [|discriminate].
      apply BOESArgs_Cons with (PBS1 := PBS1).
      -- apply IH with (e := a).
         pose proof (expr_size_call_arg_lt i (a :: rest) a (or_introl eq_refl)).
         simpl in Hlt. lia.
         exact Ha.
      -- apply IHargs; [simpl in *; lia | exact Hcheck].

  (* ECallExpr *)
  + destruct (borrow_check_env env PBS Γ e) as [PBScallee|] eqn:Hcallee; [|discriminate].
    apply BOES_CallExpr with (PBS1 := PBScallee).
    * apply IH with (e := e).
      -- pose proof (expr_size_callexpr_callee_lt e l). lia.
      -- exact Hcallee.
    * clear Hcallee. revert PBScallee PBS' Hcheck.
      induction l as [| a rest IHargs]; intros PBScallee PBS' Hcheck.
      -- simpl in Hcheck. injection Hcheck as <-. constructor.
      -- simpl in Hcheck.
         destruct (borrow_check_env env PBScallee Γ a) as [PBS1|] eqn:Ha; [|discriminate].
         apply BOESArgs_Cons with (PBS1 := PBS1).
         ++ apply IH with (e := a).
            pose proof (expr_size_callexpr_arg_lt e (a :: rest) a (or_introl eq_refl)).
            simpl in Hlt. lia.
            exact Ha.
         ++ apply IHargs; [simpl in *; lia | exact Hcheck].

  (* EStruct *)
  + apply BOES_Struct.
    revert PBS PBS' Hcheck.
    induction l1 as [| [fname field] rest IHfields]; intros PBS PBS' Hcheck.
    * simpl in Hcheck. injection Hcheck as <-. constructor.
    * simpl in Hcheck.
      destruct (borrow_check_env env PBS Γ field) as [PBS1|] eqn:Hfield; [|discriminate].
      apply BOESFields_Cons with (PBS1 := PBS1).
      -- apply IH with (e := field).
         pose proof (expr_size_struct_field_lt s l l0 ((fname, field) :: rest)
           fname field (or_introl eq_refl)).
         simpl in Hlt. lia.
         exact Hfield.
      -- apply IHfields; [simpl in *; lia | exact Hcheck].

  (* EReplace *)
  + destruct (pbs_has_any (place_root p) (place_suffix_path p) PBS) eqn:Hany.
    * discriminate Hcheck.
    * apply BOES_Write with (x := place_root p) (path := place_suffix_path p).
      -- unfold borrow_target_of_place. reflexivity.
      -- exact Hany.
      -- apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.

  (* EAssign *)
  + destruct (pbs_has_any (place_root p) (place_suffix_path p) PBS) eqn:Hany.
    * discriminate Hcheck.
    * apply BOES_Assign with (x := place_root p) (path := place_suffix_path p).
      -- unfold borrow_target_of_place. reflexivity.
      -- exact Hany.
      -- apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.

  (* EBorrow *)
  + destruct r.
    * destruct (pbs_has_mut (place_root p) (place_suffix_path p) PBS) eqn:Hmut.
      -- discriminate Hcheck.
      -- injection Hcheck as <-.
         apply BOES_BorrowShared with (x := place_root p) (path := place_suffix_path p).
         ++ unfold borrow_target_of_place. reflexivity.
         ++ exact Hmut.
    * destruct (pbs_has_any (place_root p) (place_suffix_path p) PBS) eqn:Hany.
      -- discriminate Hcheck.
      -- injection Hcheck as <-.
         apply BOES_BorrowUnique with (x := place_root p) (path := place_suffix_path p).
         ++ unfold borrow_target_of_place. reflexivity.
         ++ exact Hany.

  (* EDeref *)
  + destruct (expr_ref_root e) as [r |] eqn:Hroot.
    * destruct (pbs_has_mut r [] PBS) eqn:Hmut.
      -- discriminate Hcheck.
      -- apply BOES_Deref.
         ++ rewrite Hroot. exact Hmut.
         ++ apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.
    * apply BOES_Deref.
      -- rewrite Hroot. exact I.
      -- apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.

  (* EDrop *)
  + apply BOES_Drop.
    apply IH with (e := e). simpl in Hlt; lia. exact Hcheck.

  (* EIf *)
  + destruct (borrow_check_env env PBS Γ e1) as [PBS1|] eqn:He1; [|discriminate].
    destruct (borrow_check_env env PBS1 Γ e2) as [PBS2|] eqn:He2; [|discriminate].
    destruct (borrow_check_env env PBS1 Γ e3) as [PBS3|] eqn:He3; [|discriminate].
    destruct (pbs_eqb PBS2 PBS3) eqn:Heqb; [|discriminate Hcheck].
    injection Hcheck as <-.
    apply pbs_eqb_eq in Heqb.
    eapply BOES_If.
    * apply IH with (e := e1). simpl in Hlt; lia. exact He1.
    * apply IH with (e := e2). simpl in Hlt; lia. exact He2.
    * apply IH with (e := e3). simpl in Hlt; lia. exact He3.
    * exact Heqb.
  }
  intros env PBS Γ e PBS' Hcheck.
  apply Hsize with (n := S (expr_size e)); [lia | exact Hcheck].
Qed.
