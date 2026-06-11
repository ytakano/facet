From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker
  EnvStructuralRules EnvRootSoundness
  AssocCheckedBridgeReductionFacts
  AssocEnvBridgeReductionFacts AssocEnvFnDefTypingFacts
  AssocEnvRootFnDefTypingFacts.

Lemma typed_fn_env_structural_assoc_checked_reduces_to_structural :
  forall env f,
    ty_compatible_assoc_checked_reduces_to_bool
      (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f) ->
    typed_fn_env_structural_assoc_checked env f ->
    typed_fn_env_structural env f.
Proof.
  intros env f Hcompat Htyped.
  destruct (typed_fn_env_structural_assoc_checked_inv env f Htyped)
    as (T_body & Gamma_out & Hbody & Hassoc & Hparams).
  unfold typed_fn_env_structural.
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.

Lemma typed_fn_env_roots_assoc_checked_reduces_to_roots :
  forall env f R0 R_out roots,
    ty_compatible_assoc_checked_reduces_to_bool
      (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f) ->
    typed_fn_env_roots_assoc_checked env f R0 R_out roots ->
    typed_fn_env_roots env f R0 R_out roots.
Proof.
  intros env f R0 R_out roots Hcompat Htyped.
  destruct (typed_fn_env_roots_assoc_checked_inv env f R0 R_out roots Htyped)
    as (T_body & Gamma_out & Hbody & Hassoc & Hparams).
  unfold typed_fn_env_roots.
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.

Lemma typed_fn_env_roots_checked_assoc_checked_reduces_to_roots_checked :
  forall env f R0 R_out roots,
    ty_compatible_assoc_checked_reduces_to_bool
      (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f) ->
    typed_fn_env_roots_checked_assoc_checked env f R0 R_out roots ->
    typed_fn_env_roots_checked env f R0 R_out roots.
Proof.
  intros env f R0 R_out roots Hcompat Htyped.
  destruct (typed_fn_env_roots_checked_assoc_checked_inv env f R0 R_out roots Htyped)
    as (T_body & Gamma_out & Hbody & Hassoc & Hparams).
  unfold typed_fn_env_roots_checked.
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.
