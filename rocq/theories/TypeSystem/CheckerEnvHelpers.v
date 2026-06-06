From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Fixpoint infer_place_env (env : global_env) (Γ : ctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T, false) => infer_ok T
      end
  | PDeref q =>
      match infer_place_env env Γ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      end
  | PField q field =>
      match infer_place_env env Γ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TStruct sname lts args =>
              match lookup_struct sname env with
              | None => infer_err (ErrStructNotFound sname)
              | Some s =>
                  match lookup_field field (struct_fields s) with
                  | None => infer_err (ErrFieldNotFound field)
                  | Some f => infer_ok (instantiate_struct_field_ty lts args f)
                  end
              end
          | c => infer_err (ErrTypeMismatch c (TStruct "" [] []))
          end
      end
  end.

Definition wf_outlives_b (Δ : region_ctx) (Ω : outlives_ctx) : bool :=
  wf_outlives_at_b 0 Δ Ω.

Definition outlives_constraints_hold_b (Ω : outlives_ctx) (constraints : outlives_ctx) : bool :=
  forallb (fun '(a, b) => outlives_b Ω a b) constraints.

(* Infer the return type for a HRT (for<'a,...> fn(&...) -> ...) call.
   Used by the roots checker to handle TForall callee types. *)
Definition infer_hrt_call_env
    (Ω : outlives_ctx) (n m : nat) (bounds : outlives_ctx) (body : Ty) (arg_tys : list Ty)
    : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match build_bound_sigma (repeat None m) arg_tys param_tys with
      | None => infer_err ErrLifetimeConflict
      | Some σ =>
          match check_arg_tys Ω arg_tys (map (open_bound_ty σ) param_tys) with
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
          match check_arg_tys Ω arg_tys (map (open_bound_ty σ) param_tys) with
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

Definition open_core_trait_bounds
    (σ : list (option lifetime)) (bounds : list (core_trait_bound Ty))
    : list (core_trait_bound Ty) :=
  map (map_core_trait_bound (open_bound_ty σ)) bounds.

Definition infer_mixed_forall_call_env
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
              match check_arg_tys Ω arg_tys param_tys_open with
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

Definition infer_mixed_forall_call_env_elab
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
              match check_arg_tys Ω arg_tys param_tys_open with
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

