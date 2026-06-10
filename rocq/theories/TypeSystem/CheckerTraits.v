From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Definition trait_impl_error_with_args
    (env : global_env) (trait_name : string) (trait_args : list Ty)
    (for_ty : Ty) : option infer_error :=
  match lookup_trait trait_name env with
  | None => Some (ErrTraitImplNotFound trait_name for_ty)
  | Some t =>
      if negb (Nat.eqb (List.length trait_args) (trait_type_params t))
      then Some ErrArityMismatch
      else
      match matching_impls trait_name trait_args for_ty (env_impls env) with
      | [] => Some (ErrTraitImplNotFound trait_name for_ty)
      | [_] => None
      | _ :: _ :: _ => Some (ErrTraitImplAmbiguous trait_name for_ty)
      end
  end.

Fixpoint find_trait_method_sig (method_name : string)
    (methods : list trait_method_sig) : option trait_method_sig :=
  match methods with
  | [] => None
  | m :: rest =>
      if String.eqb (trait_method_name m) method_name
      then Some m
      else find_trait_method_sig method_name rest
  end.

Fixpoint find_impl_method_def (method_name : string)
    (methods : list fn_def) : option fn_def :=
  match methods with
  | [] => None
  | m :: rest =>
      if String.eqb (fst (fn_name m)) method_name
      then Some m
      else find_impl_method_def method_name rest
  end.

Definition resolve_trait_method_impl
    (env : global_env) (trait_name : string) (trait_args : list Ty)
    (for_ty : Ty) (method_name : string) : option impl_def :=
  match lookup_trait trait_name env with
  | None => None
  | Some t =>
      if negb (Nat.eqb (List.length trait_args) (trait_type_params t))
      then None
      else
      match find_trait_method_sig method_name (trait_methods t),
            matching_impls trait_name trait_args for_ty (env_impls env) with
      | Some _, [impl] =>
          match find_impl_method_def method_name (impl_methods impl) with
          | Some _ => Some impl
          | None => None
          end
      | _, _ => None
      end
  end.

Definition resolve_trait_method_def
    (env : global_env) (trait_name : string) (trait_args : list Ty)
    (for_ty : Ty) (method_name : string) : option fn_def :=
  match resolve_trait_method_impl env trait_name trait_args for_ty method_name with
  | Some impl => find_impl_method_def method_name (impl_methods impl)
  | None => None
  end.

Definition instantiate_trait_ref (args : list Ty) (tr : trait_ref) : trait_ref :=
  MkTraitRef (trait_ref_name tr)
    (map (subst_type_params_ty args) (trait_ref_args tr)).

Definition subst_type_params_trait_ref
    (args : list Ty) (tr : trait_ref) : trait_ref :=
  MkTraitRef (trait_ref_name tr)
    (map (subst_type_params_ty args) (trait_ref_args tr)).

Definition subst_type_params_trait_bound
    (args : list Ty) (b : trait_bound) : trait_bound :=
  MkTraitBound (bound_type_index b)
    (map (subst_type_params_trait_ref args) (bound_traits b)).

Definition subst_type_params_trait_bounds
    (args : list Ty) (bounds : list trait_bound) : list trait_bound :=
  map (subst_type_params_trait_bound args) bounds.

Fixpoint ty_list_eqb (xs ys : list Ty) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => ty_eqb x y && ty_list_eqb xs' ys'
  | _, _ => false
  end.

Definition trait_ref_eqb (a b : trait_ref) : bool :=
  String.eqb (trait_ref_name a) (trait_ref_name b) &&
  ty_list_eqb (trait_ref_args a) (trait_ref_args b).

Definition local_bound_satisfies_trait
    (bounds : list trait_bound) (type_index : nat) (tr : trait_ref) : bool :=
  existsb
    (fun b =>
      Nat.eqb (bound_type_index b) type_index &&
      existsb (trait_ref_eqb tr) (bound_traits b))
    bounds.

Definition local_bounds_satisfy_trait_ref_for_ty
    (bounds : list trait_bound) (tr : trait_ref) (for_ty : Ty) : bool :=
  match ty_core for_ty with
  | TParam i => local_bound_satisfies_trait bounds i tr
  | _ => false
  end.

Definition check_trait_ref_for_ty
    (env : global_env) (tr : trait_ref) (for_ty : Ty) : option infer_error :=
  if local_bounds_satisfy_trait_ref_for_ty (env_local_bounds env) tr for_ty
  then None
  else trait_impl_error_with_args env (trait_ref_name tr) (trait_ref_args tr) for_ty.

Fixpoint check_trait_refs_for_ty
    (env : global_env) (traits : list trait_ref) (for_ty : Ty)
    : option infer_error :=
  match traits with
  | [] => None
  | tr :: rest =>
      match check_trait_ref_for_ty env tr for_ty with
      | Some err => Some err
      | None => check_trait_refs_for_ty env rest for_ty
      end
  end.

Fixpoint type_arg_list_set_nth
    (i : nat) (v : option Ty) (σ : list (option Ty)) : list (option Ty) :=
  match i, σ with
  | O, _ :: rest => v :: rest
  | O, [] => []
  | S i', h :: rest => h :: type_arg_list_set_nth i' v rest
  | S _, [] => []
  end.

Definition type_arg_subst_vec_add
    (σ : list (option Ty)) (i : nat) (T : Ty)
    : option (list (option Ty)) :=
  match nth_error σ i with
  | None => None
  | Some None => Some (type_arg_list_set_nth i (Some T) σ)
  | Some (Some T_old) =>
      if ty_eqb T_old T then Some σ else None
  end.

Fixpoint infer_type_args_from_ty
    (fuel : nat) (formal actual : Ty) (σ : list (option Ty))
    : option (list (option Ty)) :=
  match fuel with
  | O => None
  | S fuel' =>
  match formal, actual with
  | MkTy u_f (TParam i), MkTy _ c_a =>
      type_arg_subst_vec_add σ i (MkTy u_f c_a)
  | MkTy _ (TStruct name_f lts_f args_f), MkTy _ (TStruct name_a lts_a args_a) =>
      if String.eqb name_f name_a && lifetime_list_eqb lts_f lts_a
      then infer_type_args_from_tys fuel' args_f args_a σ
      else None
  | MkTy _ (TEnum name_f lts_f args_f), MkTy _ (TEnum name_a lts_a args_a) =>
      if String.eqb name_f name_a && lifetime_list_eqb lts_f lts_a
      then infer_type_args_from_tys fuel' args_f args_a σ
      else None
  | MkTy _ (TRef _ rk_f inner_f), MkTy _ (TRef _ rk_a inner_a) =>
      if ref_kind_eqb rk_f rk_a
      then infer_type_args_from_ty fuel' inner_f inner_a σ
      else None
  | MkTy _ (TFn ps_f ret_f), MkTy _ (TFn ps_a ret_a) =>
      match infer_type_args_from_tys fuel' ps_f ps_a σ with
      | Some σ' => infer_type_args_from_ty fuel' ret_f ret_a σ'
      | None => None
      end
  | MkTy _ (TClosure _ ps_f ret_f), MkTy _ (TClosure _ ps_a ret_a) =>
      match infer_type_args_from_tys fuel' ps_f ps_a σ with
      | Some σ' => infer_type_args_from_ty fuel' ret_f ret_a σ'
      | None => None
      end
  | MkTy _ (TForall n_f Ω_f body_f), MkTy _ (TForall n_a Ω_a body_a) =>
      if Nat.eqb n_f n_a && outlives_ctx_eqb Ω_f Ω_a
      then infer_type_args_from_ty fuel' body_f body_a σ
      else None
  | MkTy _ (TTypeForall n_f bounds_f body_f),
    MkTy _ (TTypeForall n_a bounds_a body_a) =>
      if Nat.eqb n_f n_a &&
         ty_eqb (MkTy UUnrestricted (TTypeForall n_f bounds_f body_f))
                (MkTy UUnrestricted (TTypeForall n_a bounds_a body_a))
      then Some σ
      else None
  | _, _ =>
      if ty_core_eqb (ty_core formal) (ty_core actual) then Some σ else None
  end
  end

with infer_type_args_from_tys
    (fuel : nat) (formals actuals : list Ty) (σ : list (option Ty))
    : option (list (option Ty)) :=
  match fuel with
  | O => None
  | S fuel' =>
  match formals, actuals with
  | [], [] => Some σ
  | f :: fs, a :: as_ =>
      match infer_type_args_from_ty fuel' f a σ with
      | Some σ' => infer_type_args_from_tys fuel' fs as_ σ'
      | None => None
      end
  | _, _ => None
  end
  end.

Fixpoint infer_type_args_from_params
    (params : list param) (arg_tys : list Ty) (σ : list (option Ty))
    : option (list (option Ty)) :=
  match params, arg_tys with
  | [], [] => Some σ
  | p :: ps, a :: as_ =>
      match infer_type_args_from_ty (ty_depth (param_ty p) + ty_depth a)
              (param_ty p) a σ with
      | Some σ' => infer_type_args_from_params ps as_ σ'
      | None => None
      end
  | _, _ => None
  end.

Fixpoint finalize_type_args (σ : list (option Ty)) : option (list Ty) :=
  match σ with
  | [] => Some []
  | Some T :: rest =>
      match finalize_type_args rest with
      | Some Ts => Some (T :: Ts)
      | None => None
      end
  | None :: _ => None
  end.

Definition infer_call_type_args_expected
    (fdef : fn_def) (arg_tys : list Ty) (expected : option Ty)
    : option (list Ty) :=
  match infer_type_args_from_params
          (fn_params fdef) arg_tys (repeat None (fn_type_params fdef)) with
  | None => None
  | Some σ_args =>
      let σ_expected :=
        match expected with
        | None => Some σ_args
        | Some T_expected =>
            infer_type_args_from_ty
              (ty_depth (fn_ret fdef) + ty_depth T_expected)
              (fn_ret fdef) T_expected σ_args
        end in
      match σ_expected with
      | Some σ => finalize_type_args σ
      | None => None
      end
  end.

Fixpoint check_struct_bounds
    (env : global_env) (bounds : list trait_bound) (args : list Ty)
    : option infer_error :=
  match bounds with
  | [] => None
  | b :: rest =>
      match nth_error args (bound_type_index b) with
      | None => Some ErrArityMismatch
      | Some for_ty =>
          let traits := map (instantiate_trait_ref args) (bound_traits b) in
          match check_trait_refs_for_ty env traits for_ty with
          | Some err => Some err
          | None => check_struct_bounds env rest args
          end
      end
  end.

