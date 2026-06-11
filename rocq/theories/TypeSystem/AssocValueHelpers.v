From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules RootProvenance CheckerBase TypeChecker
  AssocCompatibility
  EnvStructuralRules AssocEnvStructural.
From Stdlib Require Import List.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Single-value associated-projection compatibility helpers              *)
(* ------------------------------------------------------------------ *)

Definition check_value_assoc
    (env : global_env) (Ω : outlives_ctx)
    (actual expected : Ty) : option infer_error :=
  if ty_compatible_assoc_b env Ω actual expected
  then None
  else Some (compatible_error actual expected).

Lemma check_value_assoc_true :
  forall env Ω actual expected,
    check_value_assoc env Ω actual expected = None ->
    ty_compatible_assoc_checked env Ω actual expected.
Proof.
  intros env Ω actual expected Hcheck.
  unfold check_value_assoc in Hcheck.
  destruct (ty_compatible_assoc_b env Ω actual expected) eqn:Hcompat;
    try discriminate.
  exact Hcompat.
Qed.

Lemma check_value_env_structural_assoc_sound :
  forall env Ω n Σ e actual Σ' expected,
    typed_env_structural env Ω n Σ e actual Σ' ->
    check_value_assoc env Ω actual expected = None ->
    typed_value_env_structural_assoc env Ω n Σ e expected Σ'.
Proof.
  intros env Ω n Σ e actual Σ' expected Htyped Hcheck.
  econstructor.
  - exact Htyped.
  - apply check_value_assoc_true. exact Hcheck.
Qed.

Lemma check_value_roots_assoc_sound :
  forall env Ω n R Σ e actual Σ' R' roots expected,
    typed_env_roots env Ω n R Σ e actual Σ' R' roots ->
    check_value_assoc env Ω actual expected = None ->
    typed_value_roots_assoc env Ω n R Σ e expected Σ' R' roots.
Proof.
  intros env Ω n R Σ e actual Σ' R' roots expected Htyped Hcheck.
  econstructor.
  - exact Htyped.
  - apply check_value_assoc_true. exact Hcheck.
Qed.

Definition infer_env_value_assoc
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (e : expr) (expected : Ty) : infer_result sctx :=
  match infer_core_env_state_fuel fuel env Ω n Σ e with
  | infer_err err => infer_err err
  | infer_ok (actual, Σ') =>
      match check_value_assoc env Ω actual expected with
      | None => infer_ok Σ'
      | Some err => infer_err err
      end
  end.

Lemma infer_env_value_assoc_checked_sound :
  forall fuel env Ω n Σ e expected Σ',
    infer_env_value_assoc fuel env Ω n Σ e expected = infer_ok Σ' ->
    (forall actual Σ0,
        infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (actual, Σ0) ->
        typed_env_structural env Ω n Σ e actual Σ0) ->
    typed_value_env_structural_assoc env Ω n Σ e expected Σ'.
Proof.
  intros fuel env Ω n Σ e expected Σ' Hchecked Hexpr.
  unfold infer_env_value_assoc in Hchecked.
  destruct (infer_core_env_state_fuel fuel env Ω n Σ e)
    as [[actual Σ0] | err] eqn:Hinfer; try discriminate.
  destruct (check_value_assoc env Ω actual expected) as [err' |] eqn:Hcheck;
    try discriminate.
  inversion Hchecked; subst.
  eapply check_value_env_structural_assoc_sound.
  - eapply Hexpr. reflexivity.
  - exact Hcheck.
Qed.

Definition infer_env_value_roots_assoc
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) (expected : Ty)
    : infer_result (sctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots fuel env Ω n R Σ e with
  | infer_err err => infer_err err
  | infer_ok (actual, Σ', R', roots) =>
      match check_value_assoc env Ω actual expected with
      | None => infer_ok (Σ', R', roots)
      | Some err => infer_err err
      end
  end.

Lemma infer_env_value_roots_assoc_checked_sound :
  forall fuel env Ω n R Σ e expected Σ' R' roots,
    infer_env_value_roots_assoc fuel env Ω n R Σ e expected =
      infer_ok (Σ', R', roots) ->
    (forall actual Σ0 R0 roots0,
        infer_core_env_state_fuel_roots fuel env Ω n R Σ e =
          infer_ok (actual, Σ0, R0, roots0) ->
        typed_env_roots env Ω n R Σ e actual Σ0 R0 roots0) ->
    typed_value_roots_assoc env Ω n R Σ e expected Σ' R' roots.
Proof.
  intros fuel env Ω n R Σ e expected Σ' R' roots Hchecked Hexpr.
  unfold infer_env_value_roots_assoc in Hchecked.
  destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e)
    as [[[[actual Σ0] R0] roots0] | err] eqn:Hinfer; try discriminate.
  destruct (check_value_assoc env Ω actual expected) as [err' |] eqn:Hcheck;
    try discriminate.
  inversion Hchecked; subst.
  eapply check_value_roots_assoc_sound.
  - eapply Hexpr. reflexivity.
  - exact Hcheck.
Qed.
