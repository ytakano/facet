From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram CheckerExamplesBasic CheckerBorrow CheckerFull.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.


Definition alpha_normalize_global_env (env : global_env) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    (env_local_bounds env) (alpha_rename_syntax (env_fns env)).

Fixpoint expr_vars_match_params (args : list expr) (ps : list param) : bool :=
  match args, ps with
  | [], [] => true
  | EVar x :: args', p :: ps' =>
      ident_eqb x (param_name p) && expr_vars_match_params args' ps'
  | _, _ => false
  end.

Definition specialize_simple_generic_wrapper_call
    (env : global_env) (fname : ident) (type_args : list Ty)
    (args : list expr) : option (ident * list Ty * list expr) :=
  match lookup_fn_b fname (env_fns env) with
  | None => None
  | Some fdef =>
      if no_captures_b fdef &&
         Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
      then
        match fn_body fdef with
        | ECallGeneric target nested_type_args wrapper_args =>
            if expr_vars_match_params wrapper_args (fn_params fdef)
            then Some (target,
              map (subst_type_params_ty type_args) nested_type_args, args)
            else None
        | _ => None
        end
      else None
  end.

Definition specialize_simple_generic_wrapper_calls_top
    (env : global_env) (e : expr) : expr :=
  match e with
  | ECallGeneric fname type_args args =>
      match specialize_simple_generic_wrapper_call env fname type_args args with
      | Some (target, target_type_args, target_args) =>
          ECallGeneric target target_type_args target_args
      | None => e
      end
  | _ => e
  end.

Definition simplify_local_fn_value_result_let_top (e : expr) : expr :=
  match e with
  | ELet m x T (EFn fname)
      (ELet m_res result T_res (ECallExpr (EVar y) args) (EVar result')) =>
      if ident_eqb x y && ident_eqb result result' &&
         usage_eqb (ty_usage T) UUnrestricted
      then ELet m x T (EFn fname) (ECallExpr (EVar y) args)
      else e
  | ELetInfer m x (EFn fname)
      (ELet m_res result T_res (ECallExpr (EVar y) args) (EVar result')) =>
      if ident_eqb x y && ident_eqb result result'
      then ELetInfer m x (EFn fname) (ECallExpr (EVar y) args)
      else e
  | _ => e
  end.

Definition specialize_simple_generic_wrapper_fn
    (env : global_env) (f : fn_def) : fn_def :=
  fn_with_body f
    (simplify_local_fn_value_result_let_top
      (specialize_simple_generic_wrapper_calls_top env (fn_body f))).

Fixpoint specialize_simple_generic_wrapper_fns
    (env : global_env) (fns : list fn_def) : list fn_def :=
  match fns with
  | [] => []
  | f :: rest =>
      specialize_simple_generic_wrapper_fn env f ::
      specialize_simple_generic_wrapper_fns env rest
  end.

Fixpoint infer_fns_env_elab (env : global_env) (fns : list fn_def)
    : infer_result (list fn_def) :=
  match fns with
  | [] => infer_ok []
  | f :: rest =>
      match infer_full_env_elab env f with
      | infer_err err => infer_err err
      | infer_ok (_, _, f') =>
          match infer_fns_env_elab env rest with
          | infer_err err => infer_err err
          | infer_ok rest' => infer_ok (f' :: rest')
          end
      end
  end.

Definition infer_program_env_alpha_elab (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  match infer_fns_env_elab env_alpha (env_fns env_alpha) with
  | infer_err err => infer_err err
  | infer_ok fns' =>
      let env_elab := MkGlobalEnv (env_structs env_alpha) (env_enums env_alpha)
        (env_traits env_alpha) (env_impls env_alpha)
        (env_local_bounds env_alpha) fns' in
      infer_ok (MkGlobalEnv (env_structs env_elab) (env_enums env_elab)
        (env_traits env_elab) (env_impls env_elab)
        (env_local_bounds env_elab)
        (specialize_simple_generic_wrapper_fns env_elab fns'))
  end.
