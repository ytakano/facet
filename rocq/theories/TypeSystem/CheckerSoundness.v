From Facet.TypeSystem Require Import Types Syntax TypingRules TypeChecker.
From Stdlib Require Import List String Bool.
Import ListNotations.

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

(* ------------------------------------------------------------------ *)
(* Auxiliary: _b helpers agree with TypingRules definitions              *)
(* ------------------------------------------------------------------ *)

Lemma ctx_lookup_b_eq : forall x Γ,
  ctx_lookup_b x Γ = ctx_lookup x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (String.eqb x n); [reflexivity | apply IH].
Qed.

Lemma ctx_consume_b_eq : forall x Γ,
  ctx_consume_b x Γ = ctx_consume x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (String.eqb x n).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma ctx_remove_b_eq : forall x Γ,
  ctx_remove_b x Γ = ctx_remove x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (String.eqb x n); [reflexivity | rewrite IH; reflexivity].
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
(* Main theorem: infer_core is sound w.r.t. typed                             *)
(* ------------------------------------------------------------------ *)

Theorem infer_sound : forall fenv Γ e T Γ',
  infer_core fenv Γ e = Some (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
  intros fenv Γ e. revert Γ.
  induction e; intros Γ T Γ' Hinfer; simpl in Hinfer.

  (* EUnit *)
  - injection Hinfer as <- <-. constructor.

  (* ELit *)
  - destruct l.
    + injection Hinfer as <- <-. constructor.
    + injection Hinfer as <- <-. constructor.

  (* EVar i *)
  - rename i into x.
    destruct (ctx_lookup_b x Γ) as [[Tv b] |] eqn:Hlookup_b.
    2: discriminate.
    destruct (usage_eqb (ty_usage Tv) UUnrestricted) eqn:Hunr.
    + (* unrestricted: copy, no consumption *)
      injection Hinfer as <- <-.
      apply T_Var_Copy with (b := b).
      * rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      * destruct (ty_usage Tv); simpl in Hunr; try discriminate; reflexivity.
    + (* linear/affine: consume on read *)
      destruct b; [discriminate |].
      destruct (ctx_consume_b x Γ) as [Γ'' |] eqn:Hcons_b.
      2: discriminate.
      injection Hinfer as <- <-.
      apply T_Var_Consume.
      * rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      * intro Heq. rewrite Heq in Hunr. simpl in Hunr. discriminate.
      * rewrite <- ctx_consume_b_eq. exact Hcons_b.

  (* ELet m i t e1 e2 *)
  - rename i into x.
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
    + apply IHe1. exact He1.
    + apply ty_core_eqb_true. exact Hcore.
    + apply usage_sub_bool_sound. exact Hsub.
    + apply IHe2. exact He2.
    + apply ctx_check_ok_sound. exact Hok.

  (* ELetInfer: out of scope *)
  - discriminate.

  (* ECall: admitted — the inline 'go' fixpoint inside infer_core is not
     directly accessible for inversion in this proof.
     A complete proof would require an auxiliary lemma relating 'go'
     to typed_args. *)
  - admit.

  (* EReplace (PVar px) e *)
  - destruct p as [px].
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
    + rewrite <- ctx_lookup_b_eq. exact Hlx_b.
    + apply IHe. exact He.
    + apply ty_core_eqb_true. exact Hcore.
    + apply usage_sub_bool_sound. exact Hsub.

  (* EDrop e *)
  - destruct (infer_core fenv Γ e) as [[Te Γ1] |] eqn:He.
    2: discriminate.
    injection Hinfer as <- <-.
    eapply T_Drop. apply IHe. exact He.
Admitted.

(* Public infer runs alpha-renaming before infer_core. The proof requires
   alpha-renaming preservation for typing; keep it isolated from the
   infer_core soundness argument above. *)
Theorem infer_public_sound : forall fenv Γ e T Γ',
  infer fenv Γ e = Some (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
Admitted.
