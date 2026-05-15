From Facet.TypeSystem Require Import Lifetime Types Syntax PathState TypingRules
  TypeChecker EnvStructuralRules EnvBorrowSoundness EnvRootSoundness.
From Stdlib Require Import List Bool.
Import ListNotations.

Fixpoint pbs_no_conflicts (PBS : path_borrow_state) : Prop :=
  match PBS with
  | [] => True
  | PBShared x p :: rest =>
      pbs_has_mut x p rest = false /\ pbs_no_conflicts rest
  | PBMut x p :: rest =>
      pbs_has_any x p rest = false /\ pbs_no_conflicts rest
  end.

Lemma pbs_no_conflicts_nil : pbs_no_conflicts [].
Proof.
  exact I.
Qed.

Lemma pbs_has_mut_remove_one_false : forall x p e PBS,
  pbs_has_mut x p PBS = false ->
  pbs_has_mut x p (pbs_remove_one e PBS) = false.
Proof.
  intros x p e PBS.
  induction PBS as [| h rest IH]; intros Hhas.
  - reflexivity.
  - simpl in Hhas.
    simpl.
    destruct (path_borrow_entry_eqb e h) eqn:Heq.
    + destruct h as [y q | y q].
      * exact Hhas.
      * apply orb_false_iff in Hhas as [_ Hrest].
        exact Hrest.
    + destruct h as [y q | y q].
      * apply IH. exact Hhas.
      * apply orb_false_iff in Hhas as [Hhead Hrest].
        simpl.
        rewrite Hhead.
        apply IH. exact Hrest.
Qed.

Lemma pbs_has_any_remove_one_false : forall x p e PBS,
  pbs_has_any x p PBS = false ->
  pbs_has_any x p (pbs_remove_one e PBS) = false.
Proof.
  intros x p e PBS.
  induction PBS as [| h rest IH]; intros Hhas.
  - reflexivity.
  - simpl in Hhas.
    apply orb_false_iff in Hhas as [Hhead Hrest].
    simpl.
    destruct (path_borrow_entry_eqb e h) eqn:Heq.
    + exact Hrest.
    + destruct h as [y q | y q]; simpl in Hhead; simpl;
        rewrite Hhead; apply IH; exact Hrest.
Qed.

Lemma pbs_no_conflicts_remove_one : forall e PBS,
  pbs_no_conflicts PBS ->
  pbs_no_conflicts (pbs_remove_one e PBS).
Proof.
  intros e PBS.
  induction PBS as [| h rest IH]; intros Hnc.
  - exact I.
  - simpl in Hnc.
    simpl.
    destruct (path_borrow_entry_eqb e h) eqn:Heq.
    + destruct h as [x p | x p]; destruct Hnc as [_ Hrest]; exact Hrest.
    + destruct h as [x p | x p]; destruct Hnc as [Hhead Hrest]; simpl.
      * split.
        -- apply pbs_has_mut_remove_one_false. exact Hhead.
        -- apply IH. exact Hrest.
      * split.
        -- apply pbs_has_any_remove_one_false. exact Hhead.
        -- apply IH. exact Hrest.
Qed.

Lemma pbs_no_conflicts_remove_all : forall to_remove PBS,
  pbs_no_conflicts PBS ->
  pbs_no_conflicts (pbs_remove_all to_remove PBS).
Proof.
  unfold pbs_remove_all.
  induction to_remove as [| e rest IH]; intros PBS Hnc.
  - exact Hnc.
  - simpl.
    apply IH.
    apply pbs_no_conflicts_remove_one.
    exact Hnc.
Qed.

Scheme borrow_ok_env_structural_ind' :=
  Induction for borrow_ok_env_structural Sort Prop
with borrow_ok_args_env_structural_ind' :=
  Induction for borrow_ok_args_env_structural Sort Prop
with borrow_ok_fields_env_structural_ind' :=
  Induction for borrow_ok_fields_env_structural Sort Prop.

Combined Scheme borrow_ok_env_structural_mutind
  from borrow_ok_env_structural_ind',
       borrow_ok_args_env_structural_ind',
       borrow_ok_fields_env_structural_ind'.

Theorem borrow_ok_env_structural_preserves_pbs_no_conflicts :
  (forall env PBS Γ e PBS',
    borrow_ok_env_structural env PBS Γ e PBS' ->
    pbs_no_conflicts PBS ->
    pbs_no_conflicts PBS') /\
  (forall env PBS Γ args PBS',
    borrow_ok_args_env_structural env PBS Γ args PBS' ->
    pbs_no_conflicts PBS ->
    pbs_no_conflicts PBS') /\
  (forall env PBS Γ fields PBS',
    borrow_ok_fields_env_structural env PBS Γ fields PBS' ->
    pbs_no_conflicts PBS ->
    pbs_no_conflicts PBS').
Proof.
  assert (Hmut : forall env,
    (forall PBS Γ e PBS',
      borrow_ok_env_structural env PBS Γ e PBS' ->
      pbs_no_conflicts PBS ->
      pbs_no_conflicts PBS') /\
    (forall PBS Γ args PBS',
      borrow_ok_args_env_structural env PBS Γ args PBS' ->
      pbs_no_conflicts PBS ->
      pbs_no_conflicts PBS') /\
    (forall PBS Γ fields PBS',
      borrow_ok_fields_env_structural env PBS Γ fields PBS' ->
      pbs_no_conflicts PBS ->
      pbs_no_conflicts PBS')).
  {
    intro env.
    apply borrow_ok_env_structural_mutind; intros; simpl;
      eauto using pbs_no_conflicts_remove_all.
  }
  repeat split; intros env.
  - destruct (Hmut env) as [Hpreserve _].
    eapply Hpreserve.
  - destruct (Hmut env) as [_ [Hpreserve _]].
    eapply Hpreserve.
  - destruct (Hmut env) as [_ [_ Hpreserve]].
    eapply Hpreserve.
Qed.

Corollary borrow_check_env_preserves_pbs_no_conflicts :
  forall env PBS Γ e PBS',
    borrow_check_env env PBS Γ e = infer_ok PBS' ->
    pbs_no_conflicts PBS ->
    pbs_no_conflicts PBS'.
Proof.
  intros env PBS Γ e PBS' Hcheck Hnc.
  destruct borrow_ok_env_structural_preserves_pbs_no_conflicts
    as [Hpreserve _].
  eapply Hpreserve.
  - eapply borrow_check_env_structural_sound. exact Hcheck.
  - exact Hnc.
Qed.

Corollary checked_fn_env_roots_borrow_state_no_conflicts :
  forall env f R0 R_out roots,
    checked_fn_env_roots env f R0 R_out roots ->
    exists PBS',
      borrow_ok_env_structural env [] (params_ctx (fn_params f)) (fn_body f) PBS' /\
      pbs_no_conflicts PBS'.
Proof.
  intros env f R0 R_out roots Hchecked.
  destruct Hchecked as [_ [PBS' Hborrow]].
  exists PBS'.
  split.
  - exact Hborrow.
  - destruct borrow_ok_env_structural_preserves_pbs_no_conflicts
      as [Hpreserve _].
    eapply Hpreserve.
    + exact Hborrow.
    + apply pbs_no_conflicts_nil.
Qed.
