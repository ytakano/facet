From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits AssocCompatibility.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Higher-rank lifetime helpers                                          *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* Lifetime substitution helpers for ECall                               *)
(* ------------------------------------------------------------------ *)

Fixpoint list_set_nth {A : Type} (i : nat) (v : A) (l : list A) : list A :=
  match i, l with
  | O, _ :: t => v :: t
  | O, [] => []
  | S i', h :: t => h :: list_set_nth i' v t
  | S _, [] => []
  end.

Definition lt_subst_vec_add
    (σ : list (option lifetime))
    (i : nat)
    (l_a : lifetime)
    : option (list (option lifetime)) :=
  match nth_error σ i with
  | None => None
  | Some None => Some (list_set_nth i (Some l_a) σ)
  | Some (Some l') =>
      if lifetime_eqb l' l_a then Some σ else None
  end.

Fixpoint unify_lt (m : nat) (σ : list (option lifetime))
    (T_param T_e : Ty) {struct T_param} : option (list (option lifetime)) :=
  match T_param with
  | MkTy _ (TForall _ [] body) =>
      if negb (contains_lbound_ty body)
      then unify_lt m σ body T_e
      else if ty_core_eqb (ty_core T_param) (ty_core T_e) then Some σ else None
  | MkTy _ (TRef l_p rk T_p_inner) =>
      match T_e with
      | MkTy _ (TRef l_a rk' T_e_inner) =>
          if negb (ref_kind_eqb rk rk') then None
          else
            match l_p with
            | LVar i =>
                if Nat.ltb i m then
                  match lt_subst_vec_add σ i l_a with
                  | None => None
                  | Some σ' => unify_lt m σ' T_p_inner T_e_inner
                  end
                else if lifetime_eqb (LVar i) l_a
                     then unify_lt m σ T_p_inner T_e_inner
                     else None
            | LStatic =>
                if lifetime_eqb LStatic l_a
                then unify_lt m σ T_p_inner T_e_inner
                else None
            | LBound i =>
                if lifetime_eqb (LBound i) l_a
                then unify_lt m σ T_p_inner T_e_inner
                else None
            end
      | _ => None
      end
  | _ =>
      if ty_core_eqb (ty_core T_param) (ty_core T_e) then Some σ else None
  end.

Fixpoint finalize_subst (σ : list (option lifetime)) : list lifetime :=
  match σ with
  | [] => []
  | None :: rest => LStatic :: finalize_subst rest
  | Some l :: rest => l :: finalize_subst rest
  end.

Fixpoint build_sigma (m : nat) (σ_acc : list (option lifetime))
    (arg_tys : list Ty) (params : list param)
    : option (list (option lifetime)) :=
  match arg_tys, params with
  | [], [] => Some σ_acc
  | t :: ts, p :: ps =>
      match unify_lt m σ_acc (param_ty p) t with
      | None => None
      | Some σ' => build_sigma m σ' ts ps
      end
  | _, _ => None
  end.

Definition bound_subst_vec_add
    (σ : list (option lifetime))
    (i : nat)
    (l_a : lifetime)
    : option (list (option lifetime)) :=
  lt_subst_vec_add σ i l_a.

Fixpoint unify_bound_lt (σ : list (option lifetime))
    (T_param T_e : Ty) {struct T_param} : option (list (option lifetime)) :=
  match T_param with
  | MkTy _ (TRef l_p rk T_p_inner) =>
      match T_e with
      | MkTy _ (TRef l_a rk' T_e_inner) =>
          if negb (ref_kind_eqb rk rk') then None
          else
            match l_p with
            | LBound i =>
                match bound_subst_vec_add σ i l_a with
                | None => None
                | Some σ' => unify_bound_lt σ' T_p_inner T_e_inner
                end
            | _ =>
                if lifetime_eqb l_p l_a
                then unify_bound_lt σ T_p_inner T_e_inner
                else None
            end
      | _ => None
      end
  | MkTy _ (TFn ps pr) =>
      match T_e with
      | MkTy _ (TFn es er) =>
          let fix go (σ0 : list (option lifetime)) ps0 es0 :=
            match ps0, es0 with
            | [], [] => unify_bound_lt σ0 pr er
            | p :: ps', e :: es' =>
                match unify_bound_lt σ0 p e with
                | None => None
                | Some σ' => go σ' ps' es'
                end
            | _, _ => None
            end
          in go σ ps es
      | _ => None
      end
  | _ =>
      if ty_core_eqb (ty_core T_param) (ty_core T_e) then Some σ else None
  end.

Fixpoint build_bound_sigma (σ_acc : list (option lifetime))
    (arg_tys params : list Ty) : option (list (option lifetime)) :=
  match arg_tys, params with
  | [], [] => Some σ_acc
  | t :: ts, p :: ps =>
      match unify_bound_lt σ_acc p t with
      | None => None
      | Some σ' => build_bound_sigma σ' ts ps
      end
  | _, _ => None
  end.

Fixpoint complete_bound_sigma_with_vars_from
    (n i : nat) (σ : list (option lifetime)) : list (option lifetime) :=
  match σ with
  | [] => []
  | Some l :: rest =>
      Some l :: complete_bound_sigma_with_vars_from n (S i) rest
  | None :: rest =>
      (if Nat.ltb i n then Some (LVar i) else None) ::
      complete_bound_sigma_with_vars_from n (S i) rest
  end.

Definition complete_bound_sigma_with_vars
    (n : nat) (σ : list (option lifetime)) : list (option lifetime) :=
  complete_bound_sigma_with_vars_from n 0 σ.

Fixpoint check_args (Ω : outlives_ctx) (arg_tys : list Ty) (params : list param)
    : option infer_error :=
  match arg_tys, params with
  | [], [] => None
  | t :: ts, p :: ps =>
      if ty_compatible_b Ω t (param_ty p)
      then check_args Ω ts ps
      else Some (compatible_error t (param_ty p))
  | _, _ => Some ErrArityMismatch
  end.

Fixpoint check_arg_tys (Ω : outlives_ctx) (arg_tys params : list Ty)
    : option infer_error :=
  match arg_tys, params with
  | [], [] => None
  | t :: ts, p :: ps =>
      if ty_compatible_b Ω t p
      then check_arg_tys Ω ts ps
      else Some (compatible_error t p)
  | _, _ => Some ErrArityMismatch
  end.

Fixpoint check_args_assoc
    (env : global_env) (Ω : outlives_ctx) (arg_tys : list Ty) (params : list param)
    : option infer_error :=
  match arg_tys, params with
  | [], [] => None
  | t :: ts, p :: ps =>
      if ty_compatible_assoc_b env Ω t (param_ty p)
      then check_args_assoc env Ω ts ps
      else Some (compatible_error t (param_ty p))
  | _, _ => Some ErrArityMismatch
  end.

Fixpoint check_arg_tys_assoc
    (env : global_env) (Ω : outlives_ctx) (arg_tys params : list Ty)
    : option infer_error :=
  match arg_tys, params with
  | [], [] => None
  | t :: ts, p :: ps =>
      if ty_compatible_assoc_b env Ω t p
      then check_arg_tys_assoc env Ω ts ps
      else Some (compatible_error t p)
  | _, _ => Some ErrArityMismatch
  end.

Fixpoint tys_depth (ts : list Ty) : nat :=
  match ts with
  | [] => 0
  | t :: ts' => ty_depth t + tys_depth ts'
  end.

Definition infer_type_forall_args
    (type_params : nat) (param_tys arg_tys : list Ty) : option (list Ty) :=
  match infer_type_args_from_tys
          (S (tys_depth param_tys + tys_depth arg_tys))
          param_tys arg_tys (repeat None type_params) with
  | Some σ => finalize_type_args σ
  | None => None
  end.

Definition check_type_forall_bounds
    (env : global_env) (bounds : list (core_trait_bound Ty)) (type_args : list Ty)
    : option infer_error :=
  check_struct_bounds env (trait_bounds_of_core_trait_bounds bounds) type_args.

Definition infer_type_forall_call_env
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
              match check_arg_tys Ω arg_tys (map (subst_type_params_ty type_args) param_tys) with
              | Some err => infer_err err
              | None => infer_ok (subst_type_params_ty type_args ret)
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition infer_type_forall_call_env_elab
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
              match check_arg_tys Ω arg_tys (map (subst_type_params_ty type_args) param_tys) with
              | Some err => infer_err err
              | None => infer_ok (type_args, subst_type_params_ty type_args ret)
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

