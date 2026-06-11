From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase
  AlphaTyping AssocCoreShapeHelpers.

(* Prop-level expression typing that stores only the lightweight checked
   associated-projection core-shape witness. *)
Inductive typed_core_shape_assoc_checked
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    (Γ : ctx) (e : expr) (expected_core : TypeCore Ty) (Γ' : ctx) : Prop :=
  | TCoreShapeAssocChecked : forall actual,
      typed fenv Ω n Γ e actual Γ' ->
      ty_core_assoc_matches_b env actual expected_core = true ->
      typed_core_shape_assoc_checked
        env fenv Ω n Γ e expected_core Γ'.

Lemma typed_core_shape_assoc_checked_inv :
  forall env fenv Ω n Γ e expected_core Γ',
    typed_core_shape_assoc_checked env fenv Ω n Γ e expected_core Γ' ->
    exists actual,
      typed fenv Ω n Γ e actual Γ' /\
      ty_core_assoc_matches_b env actual expected_core = true.
Proof.
  intros env fenv Ω n Γ e expected_core Γ' Hshape.
  inversion Hshape as [actual Htyped Hcore]; subst.
  exists actual. split; assumption.
Qed.

Lemma typed_core_shape_assoc_checked_same_bindings :
  forall env fenv Ω n Γ e expected_core Γ',
    typed_core_shape_assoc_checked env fenv Ω n Γ e expected_core Γ' ->
    ctx_same_bindings Γ Γ'.
Proof.
  intros env fenv Ω n Γ e expected_core Γ' Hshape.
  destruct (typed_core_shape_assoc_checked_inv _ _ _ _ _ _ _ _ Hshape)
    as [actual [Htyped _]].
  destruct typed_same_bindings as [Htyped_same _].
  eapply Htyped_same. exact Htyped.
Qed.

Lemma typed_core_shape_assoc_checked_intro :
  forall env fenv Ω n Γ e actual Γ' expected_core,
    typed fenv Ω n Γ e actual Γ' ->
    ty_core_assoc_matches_b env actual expected_core = true ->
    typed_core_shape_assoc_checked
      env fenv Ω n Γ e expected_core Γ'.
Proof.
  intros env fenv Ω n Γ e actual Γ' expected_core Htyped Hcore.
  econstructor; eauto.
Qed.

Lemma typed_core_shape_assoc_checked_core :
  forall env fenv Ω n Γ e expected_core Γ',
    typed_core_shape_assoc_checked env fenv Ω n Γ e expected_core Γ' ->
    exists actual,
      typed fenv Ω n Γ e actual Γ' /\
      ty_core (normalize_assoc_ty env actual) = expected_core.
Proof.
  intros env fenv Ω n Γ e expected_core Γ' Hshape.
  destruct (typed_core_shape_assoc_checked_inv _ _ _ _ _ _ _ _ Hshape)
    as [actual [Htyped Hcore]].
  exists actual. split; [exact Htyped |].
  apply ty_core_assoc_matches_b_true. exact Hcore.
Qed.
