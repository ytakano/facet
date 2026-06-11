From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker
  EnvStructuralRules TypeSafetyCheckedRoots EnvRootSoundness
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

Lemma typed_fn_env_structural_assoc_checked_reduces_to_plain_witness :
  forall env f,
    ty_compatible_assoc_checked_reduces_to_plain
      (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f) ->
    typed_fn_env_structural_assoc_checked env f ->
    exists T_body Gamma_out,
      typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) /\
      params_ok_env_b env (fn_params f) Gamma_out = true /\
      ty_compatible (fn_outlives f) T_body (fn_ret f).
Proof.
  intros env f Hcompat Htyped.
  destruct (typed_fn_env_structural_assoc_checked_inv env f Htyped)
    as (T_body & Gamma_out & Hbody & Hassoc & Hparams).
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.

Lemma typed_fn_env_roots_assoc_checked_reduces_to_plain_witness :
  forall env f R0 R_out roots,
    ty_compatible_assoc_checked_reduces_to_plain
      (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f) ->
    typed_fn_env_roots_assoc_checked env f R0 R_out roots ->
    exists T_body Gamma_out,
      typed_env_roots (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        R0 (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
      params_ok_env_b env (fn_params f) Gamma_out = true /\
      ty_compatible (fn_outlives f) T_body (fn_ret f).
Proof.
  intros env f R0 R_out roots Hcompat Htyped.
  destruct (typed_fn_env_roots_assoc_checked_inv env f R0 R_out roots Htyped)
    as (T_body & Gamma_out & Hbody & Hassoc & Hparams).
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.

Lemma typed_fn_env_roots_checked_assoc_checked_reduces_to_plain_witness :
  forall env f R0 R_out roots,
    ty_compatible_assoc_checked_reduces_to_plain
      (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f) ->
    typed_fn_env_roots_checked_assoc_checked env f R0 R_out roots ->
    exists T_body Gamma_out,
      typed_env_roots_checked (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        R0 (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
      params_ok_env_b env (fn_params f) Gamma_out = true /\
      ty_compatible (fn_outlives f) T_body (fn_ret f).
Proof.
  intros env f R0 R_out roots Hcompat Htyped.
  destruct (typed_fn_env_roots_checked_assoc_checked_inv env f R0 R_out roots Htyped)
    as (T_body & Gamma_out & Hbody & Hassoc & Hparams).
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.
