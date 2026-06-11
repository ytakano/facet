From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt CheckerEnvHelpers AssocCompatibility.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* Assoc-aware variant of post-collection plain function-value call logic. *)

Definition infer_fn_value_call_assoc
    (env : global_env) (Ω : outlives_ctx)
    (callee_ty : Ty) (arg_tys : list Ty) : infer_result Ty :=
  match ty_core callee_ty with
  | TFn param_tys ret =>
      match check_arg_tys_assoc env Ω arg_tys param_tys with
      | Some err => infer_err err
      | None => infer_ok ret
      end
  | TClosure _ param_tys ret =>
      match check_arg_tys_assoc env Ω arg_tys param_tys with
      | Some err => infer_err err
      | None => infer_ok ret
      end
  | c => infer_err (ErrNotAFunction c)
  end.

Definition infer_fn_value_call_generic_assoc
    (env : global_env) (Ω : outlives_ctx)
    (callee_ty : Ty) (type_args arg_tys : list Ty) : infer_result Ty :=
  match ty_core callee_ty with
  | TTypeForall _ bounds body =>
      match ty_core body with
      | TFn param_tys ret =>
          match check_type_forall_bounds env bounds type_args with
          | Some err => infer_err err
          | None =>
              match check_arg_tys_assoc env Ω arg_tys
                (map (subst_type_params_ty type_args) param_tys) with
              | Some err => infer_err err
              | None => infer_ok (subst_type_params_ty type_args ret)
              end
          end
      | c => infer_err (ErrMalformedHrtBody c)
      end
  | c => infer_err (ErrNotAFunction c)
  end.
