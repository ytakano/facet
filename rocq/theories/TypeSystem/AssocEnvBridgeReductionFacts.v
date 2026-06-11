From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker EnvStructuralRules AssocCompatibility
  AssocEnvStructural.

Definition ty_compatible_assoc_checked_reduces_to_bool
    (env : global_env) (Ω : outlives_ctx) : Prop :=
  forall actual expected,
    ty_compatible_assoc_checked env Ω actual expected ->
    ty_compatible_b Ω actual expected = true.

Lemma typed_args_env_structural_assoc_reduces_to_env_structural :
  forall env Ω n Σ args ps Σ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    typed_args_env_structural env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_args_roots_assoc_reduces_to_roots :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.
