From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Type inference                                                        *)
(*                                                                      *)
(* infer_core fenv Γ e = Some (T, Γ')                                   *)
(*   Returns the type T and the updated context Γ' after e is typed.      *)
(*   Returns infer_err on any type or usage error.                       *)
(*                                                                      *)
(* The ECall case uses an inline local fixpoint to process the argument  *)
(* list without requiring a mutual fixpoint (which complicates           *)
(* termination checking).                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_core (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match e with

  | EUnit =>
      infer_ok (MkTy UUnrestricted TUnits, Γ)

  | ELit (LInt _) =>
      infer_ok (MkTy UUnrestricted TIntegers, Γ)

  | ELit (LFloat _) =>
      infer_ok (MkTy UUnrestricted TFloats, Γ)

  | ELit (LBool _) =>
      infer_ok (MkTy UUnrestricted TBooleans, Γ)

  | EVar x =>
      match ctx_lookup_b x Γ with
      | None        => infer_err (ErrUnknownVar x)
      | Some (T, b) =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else if b
               then infer_err (ErrAlreadyConsumed x)
               else match ctx_consume_b x Γ with
                    | None    => infer_err (ErrUnknownVar x)
                    | Some Γ' => infer_ok (T, Γ')
                    end
      end

  | EFn fname =>
      match lookup_fn_b fname fenv with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Γ)
          else infer_err ErrNotImplemented
      end

  | EMakeClosure fname captures =>
      match lookup_fn_b fname fenv with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_ctx
                  (empty_global_env fenv) Ω Γ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Γ)
          | infer_err err => infer_err err
          end
      end

  | EPlace _ => infer_err ErrNotImplemented

  | EStruct _ _ _ _ => infer_err ErrNotImplemented
  | EEnum _ _ _ _ _ => infer_err ErrNotImplemented
  | EMatch _ _ => infer_err ErrNotImplemented

  | ELet m x T e1 e2 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err          => infer_err err
      | infer_ok (T1, Γ1) =>
          if ty_compatible_b Ω T1 T then
            match infer_core fenv Ω n (ctx_add_b x T m Γ1) e2 with
            | infer_err err          => infer_err err
            | infer_ok (T2, Γ2) =>
                if ctx_check_ok x T Γ2
                then infer_ok (T2, ctx_remove_b x Γ2)
                else infer_err ErrContextCheckFailed
            end
          else infer_err (compatible_error T1 T)
      end

  | EDrop e1 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err          => infer_err err
      | infer_ok (_, Γ') => infer_ok (MkTy UUnrestricted TUnits, Γ')
      end

  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None              => infer_err (ErrUnknownVar x)
      | Some (_, true)    => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | None => infer_err (ErrUnknownVar x)
          | Some MImmutable => infer_err (ErrNotMutable x)
          | Some MMutable =>
              match infer_core fenv Ω n Γ e_new with
              | infer_err err            => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_x
                  then infer_ok (T_x, Γ')
                  else infer_err (compatible_error T_new T_x)
              end
          end
      end

  (* *p <- e_new where p : &mut T: write through mutable reference, return old T *)
  | EReplace (PDeref p) e_new =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              match infer_core fenv Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_inner
                  then infer_ok (T_inner, Γ')
                  else infer_err (compatible_error T_new T_inner)
              end
          | c => infer_err (ErrNotAReference c)
          end
      end

  | EReplace (PField _ _) _ => infer_err ErrNotImplemented

  | EAssign (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | None => infer_err (ErrUnknownVar x)
          | Some MImmutable => infer_err (ErrNotMutable x)
          | Some MMutable =>
              if usage_eqb (ty_usage T_x) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_x) UAffine)
              else
                match infer_core fenv Ω n Γ e_new with
                | infer_err err => infer_err err
                | infer_ok (T_new, Γ') =>
                    if ty_compatible_b Ω T_new T_x
                    then infer_ok (MkTy UUnrestricted TUnits, Γ')
                    else infer_err (compatible_error T_new T_x)
                end
          end
      end

  (* *p = e_new where p : &mut T (non-linear): assign through mutable reference, return unit *)
  | EAssign (PDeref p) e_new =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              if usage_eqb (ty_usage T_inner) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_inner) UAffine)
              else
                match infer_core fenv Ω n Γ e_new with
                | infer_err err => infer_err err
	                | infer_ok (T_new, Γ') =>
	                    if ty_compatible_b Ω T_new T_inner
	                    then infer_ok (MkTy UUnrestricted TUnits, Γ')
	                    else infer_err (compatible_error T_new T_inner)
	                end
	          | c => infer_err (ErrNotAReference c)
	          end
      end

  | EAssign (PField _ _) _ => infer_err ErrNotImplemented

  | ECall fname args =>
      match lookup_fn_b fname fenv with
      | None      => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | []      => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core fenv Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
	                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
				                          end
			                          end
	            end
		                                  in
          match collect Γ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Γ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end

  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname fenv with
      | None      => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | []      => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core fenv Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)), Γ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrArityMismatch
      end

  | ECallExpr callee args =>
      match infer_core fenv Ω n Γ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Γc) =>
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | []      => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core fenv Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Γ')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Γ')
                  end
	              | TForall m bounds body =>
	                  match ty_core body with
	                  | TFn param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ =>
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_ty ret_open || contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | TClosure env_lt param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ0 =>
                          let σ := complete_bound_sigma_with_vars n σ0 in
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
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
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | c => infer_err (ErrNotAFunction c)
              end
          end
      end

  | ECallExprGeneric _ _ _ => infer_err ErrNotImplemented

  | ELetInfer m x e1 e2 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          match infer_core fenv Ω n (ctx_add_b x T1 m Γ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Γ2) =>
              if ctx_check_ok x T1 Γ2
              then infer_ok (T2, ctx_remove_b x Γ2)
              else infer_err ErrContextCheckFailed
          end
      end

  | EIf e1 e2 e3 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Γ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans then
            match infer_core fenv Ω n Γ1 e2 with
            | infer_err err => infer_err err
            | infer_ok (T2, Γ2) =>
                match infer_core fenv Ω n Γ1 e3 with
                | infer_err err => infer_err err
                | infer_ok (T3, Γ3) =>
                    if ty_core_eqb (ty_core T2) (ty_core T3) then
                      match ctx_merge Γ2 Γ3 with
                      | None    => infer_err ErrContextCheckFailed
                      | Some Γ4 =>
                          infer_ok (MkTy (usage_max (ty_usage T2) (ty_usage T3))
                                         (ty_core T2), Γ4)
                      end
                    else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                end
            end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end

  | EBorrow rk (PVar x) =>
      match ctx_lookup_b x Γ with
      | None              => infer_err (ErrUnknownVar x)
      | Some (_, true)    => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match rk with
          | RUnique =>
              (* &mut requires a mutable binding *)
              match ctx_lookup_mut_b x Γ with
              | Some MMutable =>
                  infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_x), Γ)
              | _ => infer_err (ErrImmutableBorrow x)
              end
          | RShared =>
              infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_x), Γ)
          end
      end

  (* &*p (shared re-borrow): p has &T or &mut T, produce &T *)
  | EBorrow RShared (PDeref p) =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ _ T_inner =>
              infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_inner), Γ)
          | c => infer_err (ErrNotAReference c)
          end
      end

  (* &mut *p (mutable re-borrow): p must have &mut T *)
  | EBorrow RUnique (PDeref p) =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_inner), Γ)
          | c => infer_err (ErrNotAReference c)
          end
      end

  | EBorrow _ (PField _ _) => infer_err ErrNotImplemented

  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place Γ p with
          | infer_err err => infer_err err
          | infer_ok T_r =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core fenv Ω n Γ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Γ') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  (* Move-out through a reference is forbidden;
                     only UUnrestricted inner types may be read via deref *)
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end

  end.
