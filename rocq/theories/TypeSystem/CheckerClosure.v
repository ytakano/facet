From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Closure capture helpers                                             *)
(* ------------------------------------------------------------------ *)

Definition shared_ref_lifetime_of_ty (T : Ty) : option lifetime :=
  match T with
  | MkTy _ (TRef l RShared _) => Some l
  | _ => None
  end.

Fixpoint collect_shared_ref_lifetimes (captured_tys : list Ty) : list lifetime :=
  match captured_tys with
  | [] => []
  | T :: rest =>
      match shared_ref_lifetime_of_ty T with
      | Some l => l :: collect_shared_ref_lifetimes rest
      | None => collect_shared_ref_lifetimes rest
      end
  end.

Fixpoint all_outlive_b (Ω : outlives_ctx) (lts : list lifetime)
    (env_lt : lifetime) : bool :=
  match lts with
  | [] => true
  | l :: rest => outlives_b Ω l env_lt && all_outlive_b Ω rest env_lt
  end.

Fixpoint find_closure_env_lifetime
    (Ω : outlives_ctx) (lts candidates : list lifetime)
    : option lifetime :=
  match candidates with
  | [] => None
  | l :: rest =>
      if all_outlive_b Ω lts l
      then Some l
      else find_closure_env_lifetime Ω lts rest
  end.

Definition infer_closure_env_lifetime
    (Ω : outlives_ctx) (captured_tys : list Ty) : infer_result lifetime :=
  let lts := collect_shared_ref_lifetimes captured_tys in
  match lts with
  | [] => infer_ok LStatic
  | _ =>
      match find_closure_env_lifetime Ω lts lts with
      | Some env_lt => infer_ok env_lt
      | None => infer_err ErrLifetimeConflict
      end
  end.

Definition closure_capture_allowed_b
    (env : global_env) (Ω : outlives_ctx) (env_lt : lifetime) (T : Ty)
    : bool :=
  capture_ref_free_ty_b env T ||
  match T with
  | MkTy _ (TRef l RShared _) => outlives_b Ω l env_lt
  | _ => false
  end.

Fixpoint closure_captures_allowed_b
    (env : global_env) (Ω : outlives_ctx) (env_lt : lifetime)
    (captured_tys : list Ty) : bool :=
  match captured_tys with
  | [] => true
  | T :: rest =>
      closure_capture_allowed_b env Ω env_lt T &&
      closure_captures_allowed_b env Ω env_lt rest
  end.

Fixpoint check_make_closure_captures_ctx_base
    (env : global_env) (Ω : outlives_ctx) (Γ : ctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      match ctx_lookup_state x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if negb (binding_available_b st [])
          then infer_err (ErrAlreadyConsumed x)
          else
          match ctx_lookup_mut_b x Γ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if ty_compatible_b Ω T (param_ty cap)
                then
                  match check_make_closure_captures_ctx_base env Ω Γ captures' params' with
                  | infer_ok captured_tys => infer_ok (T :: captured_tys)
                  | infer_err err => infer_err err
                  end
                else infer_err (compatible_error T (param_ty cap))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Definition check_make_closure_captures_ctx
    (env : global_env) (Ω : outlives_ctx) (Γ : ctx)
    (captures : list ident) (params : list param)
    : infer_result (lifetime * list Ty) :=
  match check_make_closure_captures_ctx_base env Ω Γ captures params with
  | infer_ok captured_tys =>
      match infer_closure_env_lifetime Ω captured_tys with
      | infer_ok env_lt =>
          if closure_captures_allowed_b env Ω env_lt captured_tys
          then infer_ok (env_lt, captured_tys)
          else infer_err (ErrNotAReference TUnits)
      | infer_err err => infer_err err
      end
  | infer_err err => infer_err err
  end.

Fixpoint check_make_closure_captures_exact_ctx
    (env : global_env) (Ω : outlives_ctx) (Γ : ctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      if match param_mutability cap with MImmutable => false | MMutable => true end
      then infer_err ErrContextCheckFailed
      else
      match ctx_lookup_state (param_name cap) Γ with
      | Some _ => infer_err ErrContextCheckFailed
      | None =>
      match ctx_lookup_state x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if st_consumed st
          then infer_err ErrContextCheckFailed
          else
          match st_moved_paths st with
          | _ :: _ => infer_err ErrContextCheckFailed
          | [] =>
          match ctx_lookup_mut_b x Γ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if capture_ref_free_ty_b env T
                then
                  if ty_eqb T (param_ty cap) &&
                     ty_compatible_b Ω T (param_ty cap)
                  then
                    match check_make_closure_captures_exact_ctx env Ω Γ captures' params' with
                    | infer_ok rest_tys => infer_ok (T :: rest_tys)
                    | infer_err err => infer_err err
                    end
                  else infer_err (compatible_error T (param_ty cap))
                else infer_err (ErrNotAReference (ty_core T))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
          end
      end
      end
  | _, _ => infer_err ErrArityMismatch
  end.
