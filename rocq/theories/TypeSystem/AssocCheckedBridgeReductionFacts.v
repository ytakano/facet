From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase AssocCompatibility.
From Stdlib Require Import List.

Definition ty_compatible_assoc_checked_reduces_to_plain
    (env : global_env) (Ω : outlives_ctx) : Prop :=
  forall actual expected,
    ty_compatible_assoc_checked env Ω actual expected ->
    ty_compatible Ω actual expected.

Definition ty_compatible_assoc_checked_reduces_to_bool
    (env : global_env) (Ω : outlives_ctx) : Prop :=
  forall actual expected,
    ty_compatible_assoc_checked env Ω actual expected ->
    ty_compatible_b Ω actual expected = true.

Definition ty_compatible_assoc_checked_reduces_to_assoc
    (env : global_env) (Ω : outlives_ctx) : Prop :=
  forall actual expected,
    ty_compatible_assoc_checked env Ω actual expected ->
    ty_compatible_assoc env Ω actual expected.

Lemma typed_args_assoc_checked_reduces_to_assoc :
  forall env fenv Ω n Γ args ps Γ',
    ty_compatible_assoc_checked_reduces_to_assoc env Ω ->
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    typed_args_assoc env fenv Ω n Γ args ps Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_args_assoc_checked_reduces_to_plain :
  forall env fenv Ω n Γ args ps Γ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    typed_args fenv Ω n Γ args ps Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_args_assoc_checked_reduces_to_bool :
  forall env fenv Ω n Γ args ps Γ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    Forall2
      (fun e p =>
        exists actual Γin Γout,
          typed fenv Ω n Γin e actual Γout /\
          ty_compatible_b Ω actual (param_ty p) = true)
      args ps.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - constructor.
    + exists T_e, Γ, Γ1. split; eauto.
    + exact IHHargs.
Qed.
