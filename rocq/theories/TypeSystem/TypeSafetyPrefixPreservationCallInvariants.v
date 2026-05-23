From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyPrefixPreservationPrefix.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Theorem eval_preserves_typing_ready_with_call_invariants_mutual_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  (forall env s e s' v,
    eval env s e s' v ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  intro Hpreservation.
  split.
  - intros env s e s' v Heval _ _ Ω n Σ T Σ' Hready Hstore Htyped.
    exact (proj1 Hpreservation env s e s' v Heval
      Ω n Σ T Σ' Hready Hstore Htyped).
  - split.
    + intros env s args s' vs Heval _ _ Ω n Σ ps Σ' Hready Hstore Htyped.
      exact (proj1 (proj2 Hpreservation)
        env s args s' vs Heval Ω n Σ ps Σ' Hready Hstore Htyped).
    + intros env s fields defs s' values Heval _ _ Ω n lts args Σ Σ'
        Hready Hstore Htyped.
      exact (proj2 (proj2 Hpreservation)
        env s fields defs s' values Heval Ω n lts args Σ Σ'
        Hready Hstore Htyped).
Qed.
