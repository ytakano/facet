From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase AssocCompatibility
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
