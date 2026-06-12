From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram CheckerBorrow.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Combined type + borrow checker                                        *)
(* ------------------------------------------------------------------ *)

(* Legacy checker retained for proof compatibility only.  The OCaml CLI
   and extraction roots use the env/stateful checker below. *)
Definition infer_full (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer fenv f with
  | infer_err err => infer_err err
  | infer_ok res  =>
      let Γ := fn_body_ctx f in
      match borrow_check fenv [] Γ (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _    => infer_ok res
      end
  end.

Definition infer_full_env (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer_env env f with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition infer_full_env_elab (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * fn_def) :=
  match infer_env_elab env f with
  | infer_err err => infer_err err
  | infer_ok (T, Γ, f') =>
      match borrow_check_env env [] (fn_body_ctx f') (fn_body f') with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok (T, Γ, f')
      end
  end.

Definition infer_full_env_roots (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_env_roots env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition infer_full_env_roots_checked (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_env_roots_shadow_safe_checked env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition infer_full_env_roots_checked_assoc
    (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_env_roots_shadow_safe_checked_assoc env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.
