From Facet.TypeSystem Require Import Types Syntax Renaming.
From Stdlib Require Import List String Bool Lia PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Core alpha-renaming facts                                           *)
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

