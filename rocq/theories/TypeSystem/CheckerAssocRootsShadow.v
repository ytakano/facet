From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary
  CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore
  CheckerElabCore CheckerRootsCore CheckerRootsShadow
  AssocFnValueCallHelpers AssocHrtHelpers.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Definition infer_fn_value_call_expr_assoc_shadow_safe
    (fuel : nat) (env : global_env) (Omega : outlives_ctx) (n : nat)
    (R : root_env) (Sigma : sctx) (callee : expr) (args : list expr)
    : infer_result (Ty * sctx * root_env * root_set) :=
  match fuel with
  | 0 => infer_err ErrNotImplemented
  | S fuel' =>
      match infer_core_env_state_fuel_roots_shadow_safe
              fuel' env Omega n R Sigma callee with
      | infer_err err => infer_err err
      | infer_ok (callee_ty, Sigma1, R1, roots_callee) =>
          match infer_env_args_collect_roots
                  fuel' env Omega n R1 Sigma1 args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Sigma', R', arg_roots) =>
              let roots :=
                root_set_union roots_callee (root_sets_union arg_roots) in
              match ty_core callee_ty with
              | TFn _ _ | TClosure _ _ _ =>
                  match infer_fn_value_call_assoc
                          env Omega callee_ty arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Sigma', R', roots)
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env_assoc
                          env Omega type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Sigma', R', roots)
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env_assoc
                              env Omega n m bounds type_params type_bounds
                              type_body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret => infer_ok (ret, Sigma', R', roots)
                      end
                  | TFn _ _ | TClosure _ _ _ =>
                      match infer_hrt_call_env_assoc
                              env Omega n m bounds body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret => infer_ok (ret, Sigma', R', roots)
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | _ => infer_err ErrNotImplemented
              end
          end
      end
  end.

Definition infer_core_env_state_fuel_roots_shadow_safe_checked_assoc
    (fuel : nat) (env : global_env) (Omega : outlives_ctx) (n : nat)
    (R : root_env) (Sigma : sctx) (e : expr)
    : infer_result (Ty * sctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots_shadow_safe_checked
          fuel env Omega n R Sigma e with
  | infer_ok res => infer_ok res
  | infer_err err =>
      match e with
      | ECallExpr callee args =>
          infer_fn_value_call_expr_assoc_shadow_safe
            fuel env Omega n R Sigma callee args
      | _ => infer_err err
      end
  end.

Definition infer_core_env_roots_shadow_safe_checked_assoc
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    (R : root_env) (Gamma : ctx) (e : expr)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots_shadow_safe_checked_assoc
          10000 env Omega n R (sctx_of_ctx Gamma) e with
  | infer_ok (T, Sigma, R', roots) => infer_ok (T, ctx_of_sctx Sigma, R', roots)
  | infer_err err => infer_err err
  end.
