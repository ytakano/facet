From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker RootProvenance EnvStructuralRules TypeSafetyCheckedRoots EnvRootSoundness
  AssocCompatibility.

(* Roots-level function-body typing with lightweight checked
   associated-projection compatibility witnesses for return types. The
   compatibility environment includes function-local trait bounds, matching the
   body environment used by the roots checkers.
*)
Definition typed_fn_env_roots_assoc_checked (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Gamma_out,
    typed_env_roots (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
    ty_compatible_assoc_checked
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) T_body (fn_ret f) /\
    params_ok_env_b env (fn_params f) Gamma_out = true.

Definition typed_fn_env_roots_checked_assoc_checked
    (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Gamma_out,
    typed_env_roots_checked (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
    ty_compatible_assoc_checked
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) T_body (fn_ret f) /\
    params_ok_env_b env (fn_params f) Gamma_out = true.

Lemma typed_fn_env_roots_assoc_checked_inv :
  forall env f R0 R_out roots,
    typed_fn_env_roots_assoc_checked env f R0 R_out roots ->
    exists T_body Gamma_out,
      typed_env_roots (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        R0 (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
      ty_compatible_assoc_checked
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots Hfn.
  exact Hfn.
Qed.

Lemma typed_fn_env_roots_checked_assoc_checked_inv :
  forall env f R0 R_out roots,
    typed_fn_env_roots_checked_assoc_checked env f R0 R_out roots ->
    exists T_body Gamma_out,
      typed_env_roots_checked (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        R0 (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
      ty_compatible_assoc_checked
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots Hfn.
  exact Hfn.
Qed.
