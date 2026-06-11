From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase
  EnvStructuralRules TypeChecker AssocCompatibility.

(* Env-structural function-body typing with a lightweight checked
   associated-projection compatibility witness for the return type. The
   compatibility environment includes the function-local trait bounds, matching
   the body environment used by infer_env.
*)
Inductive typed_fn_env_structural_assoc_checked
    (env : global_env) (f : fn_def) : Prop :=
  | TFnEnvStructuralAssocChecked : forall T_body Gamma_out,
      typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) ->
      ty_compatible_assoc_checked
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) ->
      params_ok_env_b env (fn_params f) Gamma_out = true ->
      typed_fn_env_structural_assoc_checked env f.

Lemma typed_fn_env_structural_assoc_checked_inv :
  forall env f,
    typed_fn_env_structural_assoc_checked env f ->
    exists T_body Gamma_out,
      typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Gamma_out) /\
      ty_compatible_assoc_checked
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) T_body (fn_ret f) /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f Hfn.
  inversion Hfn; subst.
  exists T_body, Gamma_out. repeat split; assumption.
Qed.

Lemma typed_fn_env_structural_assoc_checked_intro :
  forall env f T_body Gamma_out,
    typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) ->
    ty_compatible_assoc_checked
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) T_body (fn_ret f) ->
    params_ok_env_b env (fn_params f) Gamma_out = true ->
    typed_fn_env_structural_assoc_checked env f.
Proof.
  intros env f T_body Gamma_out Htyped Hcompat Hparams.
  econstructor; eauto.
Qed.
