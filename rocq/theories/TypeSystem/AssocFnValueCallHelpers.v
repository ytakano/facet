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
