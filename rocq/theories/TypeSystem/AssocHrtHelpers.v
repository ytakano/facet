From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt CheckerEnvHelpers AssocCompatibility.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* Assoc-aware variants of downstream HRT/type-forall call helpers. *)

Definition infer_hrt_call_env_assoc
    (env : global_env) (Ω : outlives_ctx) (n m : nat)
    (bounds : outlives_ctx) (body : Ty) (arg_tys : list Ty)
    : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match build_bound_sigma (repeat None m) arg_tys param_tys with
      | None => infer_err ErrLifetimeConflict
      | Some σ =>
          match check_arg_tys_assoc env Ω arg_tys
                  (map (open_bound_ty σ) param_tys) with
          | Some err => infer_err err
          | None =>
              if contains_lbound_ty (open_bound_ty σ ret) ||
                 contains_lbound_outlives (open_bound_outlives σ bounds)
              then infer_err ErrHrtUnresolvedBound
              else if outlives_constraints_hold_b Ω (open_bound_outlives σ bounds)
                   then infer_ok (open_bound_ty σ ret)
                   else infer_err ErrHrtBoundUnsatisfied
          end
      end
  | TClosure env_lt param_tys ret =>
      match build_bound_sigma (repeat None m) arg_tys param_tys with
      | None => infer_err ErrLifetimeConflict
      | Some σ0 =>
          let σ := complete_bound_sigma_with_vars n σ0 in
          match check_arg_tys_assoc env Ω arg_tys
                  (map (open_bound_ty σ) param_tys) with
          | Some err => infer_err err
          | None =>
              let env_open := open_bound_lifetime σ env_lt in
              let ret_open := open_bound_ty σ ret in
              let bounds_open := open_bound_outlives σ bounds in
              if contains_lbound_lifetime env_open ||
                 contains_lbound_ty ret_open ||
                 contains_lbound_outlives bounds_open
              then infer_err ErrHrtUnresolvedBound
              else if outlives_constraints_hold_b Ω bounds_open
                   then infer_ok ret_open
                   else infer_err ErrHrtBoundUnsatisfied
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition infer_type_forall_call_env_assoc
    (env : global_env) (Ω : outlives_ctx) (type_params : nat)
    (bounds : list (core_trait_bound Ty)) (body : Ty) (arg_tys : list Ty)
    : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match infer_type_forall_args type_params param_tys arg_tys with
      | None => infer_err ErrTypeArgInferenceFailed
      | Some type_args =>
          match check_type_forall_bounds env bounds type_args with
          | Some err => infer_err err
          | None =>
              match check_arg_tys_assoc env Ω arg_tys
                (map (subst_type_params_ty type_args) param_tys) with
              | Some err => infer_err err
              | None => infer_ok (subst_type_params_ty type_args ret)
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition infer_type_forall_call_env_elab_assoc
    (env : global_env) (Ω : outlives_ctx) (type_params : nat)
    (bounds : list (core_trait_bound Ty)) (body : Ty) (arg_tys : list Ty)
    : infer_result (list Ty * Ty) :=
  match ty_core body with
  | TFn param_tys ret =>
      match infer_type_forall_args type_params param_tys arg_tys with
      | None => infer_err ErrTypeArgInferenceFailed
      | Some type_args =>
          match check_type_forall_bounds env bounds type_args with
          | Some err => infer_err err
          | None =>
              match check_arg_tys_assoc env Ω arg_tys
                (map (subst_type_params_ty type_args) param_tys) with
              | Some err => infer_err err
              | None => infer_ok (type_args, subst_type_params_ty type_args ret)
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition infer_mixed_forall_call_env_assoc
    (env : global_env) (Ω : outlives_ctx) (n m : nat)
    (lt_bounds : outlives_ctx) (type_params : nat)
    (type_bounds : list (core_trait_bound Ty)) (body : Ty)
    (arg_tys : list Ty) : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match infer_type_forall_args type_params param_tys arg_tys with
      | None => infer_err ErrTypeArgInferenceFailed
      | Some type_args =>
          let param_tys_t := map (subst_type_params_ty type_args) param_tys in
          match build_bound_sigma (repeat None m) arg_tys param_tys_t with
          | None => infer_err ErrLifetimeConflict
          | Some σ0 =>
              let σ := complete_bound_sigma_with_vars n σ0 in
              let param_tys_open := map (open_bound_ty σ) param_tys_t in
              match check_arg_tys_assoc env Ω arg_tys param_tys_open with
              | Some err => infer_err err
              | None =>
                  let ret_open := open_bound_ty σ
                    (subst_type_params_ty type_args ret) in
                  let lt_bounds_open := open_bound_outlives σ lt_bounds in
                  let type_bounds_open := open_core_trait_bounds σ type_bounds in
                  if contains_lbound_ty ret_open ||
                     contains_lbound_outlives lt_bounds_open ||
                     existsb
                       (fun b =>
                         existsb
                           (fun tr =>
                             existsb contains_lbound_ty (core_trait_ref_args Ty tr))
                           (core_bound_traits Ty b))
                       type_bounds_open
                  then infer_err ErrHrtUnresolvedBound
                  else if outlives_constraints_hold_b Ω lt_bounds_open
                  then
                    match check_type_forall_bounds env type_bounds_open type_args with
                    | Some err => infer_err err
                    | None => infer_ok ret_open
                    end
                  else infer_err ErrHrtBoundUnsatisfied
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition infer_mixed_forall_call_env_elab_assoc
    (env : global_env) (Ω : outlives_ctx) (n m : nat)
    (lt_bounds : outlives_ctx) (type_params : nat)
    (type_bounds : list (core_trait_bound Ty)) (body : Ty)
    (arg_tys : list Ty) : infer_result (list Ty * Ty) :=
  match ty_core body with
  | TFn param_tys ret =>
      match infer_type_forall_args type_params param_tys arg_tys with
      | None => infer_err ErrTypeArgInferenceFailed
      | Some type_args =>
          let param_tys_t := map (subst_type_params_ty type_args) param_tys in
          match build_bound_sigma (repeat None m) arg_tys param_tys_t with
          | None => infer_err ErrLifetimeConflict
          | Some σ0 =>
              let σ := complete_bound_sigma_with_vars n σ0 in
              let param_tys_open := map (open_bound_ty σ) param_tys_t in
              match check_arg_tys_assoc env Ω arg_tys param_tys_open with
              | Some err => infer_err err
              | None =>
                  let ret_open := open_bound_ty σ
                    (subst_type_params_ty type_args ret) in
                  let lt_bounds_open := open_bound_outlives σ lt_bounds in
                  let type_bounds_open := open_core_trait_bounds σ type_bounds in
                  if contains_lbound_ty ret_open ||
                     contains_lbound_outlives lt_bounds_open ||
                     existsb
                       (fun b =>
                         existsb
                           (fun tr =>
                             existsb contains_lbound_ty (core_trait_ref_args Ty tr))
                           (core_bound_traits Ty b))
                       type_bounds_open
                  then infer_err ErrHrtUnresolvedBound
                  else if outlives_constraints_hold_b Ω lt_bounds_open
                  then
                    match check_type_forall_bounds env type_bounds_open type_args with
                    | Some err => infer_err err
                    | None => infer_ok (type_args, ret_open)
                    end
                  else infer_err ErrHrtBoundUnsatisfied
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.
