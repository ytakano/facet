From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker RootProvenance
  EnvStructuralRules AssocEnvStructural.
From Stdlib Require Import List String.
Import ListNotations.

(* Specification-only call typing boundaries for associated projections.
   These mirror the env/root structural call constructors, but keep associated
   projection compatibility only at the argument-list boundary. They do not
   change the executable checker or the primary typed_env_structural relation. *)
Inductive typed_env_structural_assoc_call_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TESAssocBoundary_Call : forall Sigma Sigma' fname fdef args sigma,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_env_structural_assoc env Omega n Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECall fname args) (apply_lt_ty sigma (fn_ret fdef)) Sigma'
  | TESAssocBoundary_CallGeneric : forall Sigma Sigma' fname fdef
      (type_args : list Ty) args sigma,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma args
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fdef))) Sigma' ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallGeneric fname type_args args)
        (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
        Sigma'
  | TESAssocBoundary_CallExpr_Fn : forall Sigma Sigma1 Sigma' callee args
      u param_tys ret,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TFn param_tys ret)) Sigma1 ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys param_tys) Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) ret Sigma'
  | TESAssocBoundary_CallExpr_Closure : forall Sigma Sigma1 Sigma' callee
      args u env_lt param_tys ret,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TClosure env_lt param_tys ret)) Sigma1 ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys param_tys) Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) ret Sigma'
  | TESAssocBoundary_CallExpr_Forall : forall Sigma Sigma1 Sigma' callee args
      u m bounds body param_tys ret sigma,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TForall m bounds body)) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma'
  | TESAssocBoundary_CallExpr_Forall_Closure : forall Sigma Sigma1 Sigma'
      callee args u m bounds body env_lt param_tys ret sigma,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TForall m bounds body)) Sigma1 ->
      ty_core body = TClosure env_lt param_tys ret ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' ->
      contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma'
  | TESAssocBoundary_CallExpr_MixedForall : forall Sigma Sigma1 Sigma'
      callee args u u_body m bounds type_params type_bounds body param_tys
      ret sigma type_args,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds sigma type_bounds)
        type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys
          (map (open_bound_ty sigma)
            (map (subst_type_params_ty type_args) param_tys))) Sigma' ->
      contains_lbound_ty
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args)
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) Sigma'
  | TESAssocBoundary_CallExpr_TypeForall : forall Sigma Sigma1 Sigma' callee
      args u m bounds body param_tys ret type_args,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TTypeForall m bounds body)) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) (subst_type_params_ty type_args ret) Sigma'
  | TESAssocBoundary_CallExprGeneric_TypeForall : forall Sigma Sigma1 Sigma'
      callee args u m bounds body param_tys ret type_args,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TTypeForall m bounds body)) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExprGeneric callee type_args args)
        (subst_type_params_ty type_args ret) Sigma'
  | TESAssocBoundary_CallExpr_MakeClosure : forall Sigma Sigma' fname fdef
      captures env_lt captured_tys args sigma,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Omega Sigma captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_env_structural_assoc env Omega n Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty sigma (fn_ret fdef)) Sigma'.

Inductive typed_env_roots_assoc_call_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERAssocBoundary_Call : forall R R' Sigma Sigma' fname fdef args sigma
      arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_roots_assoc env Omega n R Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' R' arg_roots ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECall fname args) (apply_lt_ty sigma (fn_ret fdef)) Sigma' R'
        (root_sets_union arg_roots)
  | TERAssocBoundary_CallGeneric : forall R R' Sigma Sigma' fname fdef
      (type_args : list Ty) args sigma arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_roots_assoc env Omega n R Sigma args
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fdef))) Sigma' R'
        arg_roots ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallGeneric fname type_args args)
        (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
        Sigma' R' (root_sets_union arg_roots)
  | TERAssocBoundary_CallExpr_Fn : forall R R1 R' Sigma Sigma1 Sigma'
      callee args u param_tys ret arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TFn param_tys ret)) Sigma1 R1 roots_callee ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys param_tys) Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) ret Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_Closure : forall R R1 R' Sigma Sigma1 Sigma'
      callee args u env_lt param_tys ret arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TClosure env_lt param_tys ret)) Sigma1 R1 roots_callee ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys param_tys) Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) ret Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_TypeForall : forall R R1 R' Sigma Sigma1
      Sigma' callee args u type_params bounds body_ty param_tys ret_inner
      type_args arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Sigma1 R1
        roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) (subst_type_params_ty type_args ret_inner)
        Sigma' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExprGeneric_TypeForall : forall R R1 R' Sigma
      Sigma1 Sigma' callee args u type_params bounds body_ty param_tys
      ret_inner type_args arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Sigma1 R1
        roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExprGeneric callee type_args args)
        (subst_type_params_ty type_args ret_inner) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_MixedForall : forall R R1 R' Sigma Sigma1
      Sigma' callee args u u_body m bounds type_params type_bounds body_ty
      param_tys ret sigma type_args arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body_ty))))
        Sigma1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds sigma type_bounds)
        type_args = None ->
      contains_lbound_ty
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys
          (map (open_bound_ty sigma)
            (map (subst_type_params_ty type_args) param_tys))) Sigma' R'
        arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args)
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_Forall_Fn : forall R R1 R' Sigma Sigma1
      Sigma' callee args u m bounds body_ty param_tys ret sigma arg_roots
      roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R'
        arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_Forall_Closure : forall R R1 R' Sigma Sigma1
      Sigma' callee args u m bounds body_ty env_lt param_tys ret sigma
      arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee ->
      ty_core body_ty = TClosure env_lt param_tys ret ->
      contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R'
        arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_MakeClosure : forall R R' Sigma Sigma' fname
      fdef captures env_lt captured_tys args sigma arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Omega Sigma captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_roots_assoc env Omega n R Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' R' arg_roots ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty sigma (fn_ret fdef)) Sigma' R'
        (root_sets_union arg_roots).
