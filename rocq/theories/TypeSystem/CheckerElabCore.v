From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Fixpoint param_name_in_b (x : ident) (ps : list param) : bool :=
  match ps with
  | [] => false
  | p :: ps' => ident_eqb x (param_name p) || param_name_in_b x ps'
  end.

Fixpoint param_vars_exact_b (ps : list param) (args : list expr) : bool :=
  match ps, args with
  | [], [] => true
  | p :: ps', EVar x :: args' =>
      ident_eqb x (param_name p) && param_vars_exact_b ps' args'
  | _, _ => false
  end.

Fixpoint lookup_call_arg_for_param
    (x : ident) (ps : list param) (args : list expr) : option expr :=
  match ps, args with
  | [], [] => None
  | p :: ps', arg :: args' =>
      if ident_eqb x (param_name p)
      then Some arg
      else lookup_call_arg_for_param x ps' args'
  | _, _ => None
  end.

Fixpoint adapter_call_uses_bound_fn_only
    (x fparam : ident) (ps : list param) (args : list expr) : bool :=
  match ps, args with
  | [], [] => true
  | p :: ps', arg :: args' =>
      if ident_eqb (param_name p) fparam
      then
        match arg with
        | EVar y =>
            ident_eqb x y &&
            adapter_call_uses_bound_fn_only x fparam ps' args'
        | _ => false
        end
      else
        negb (ident_in_b x (free_vars_expr arg)) &&
        negb (ident_in_b x (args_local_store_names [arg])) &&
        adapter_call_uses_bound_fn_only x fparam ps' args'
  | _, _ => false
  end.

Fixpoint adapter_body_actual_args
    (fparam : ident) (ps : list param) (call_args body_args : list expr)
    : option (list expr) :=
  match body_args with
  | [] => Some []
  | EVar y :: rest =>
      if ident_eqb y fparam then None else
      match lookup_call_arg_for_param y ps call_args,
            adapter_body_actual_args fparam ps call_args rest with
      | Some actual, Some actuals => Some (actual :: actuals)
      | _, _ => None
      end
  | _ :: _ => None
  end.

Definition generic_fn_wrapper_target
    (fdef : fn_def) : option (ident * list Ty) :=
  if no_captures_b fdef &&
     Nat.eqb (fn_lifetimes fdef) 0 &&
     Nat.eqb (fn_type_params fdef) 0
  then
    match fn_body fdef with
    | ECallGeneric target type_args args =>
        if param_vars_exact_b (fn_params fdef) args
        then Some (target, type_args)
        else None
    | _ => None
    end
  else None.

Definition adapter_call_target
    (fdef : fn_def) : option (ident * list expr) :=
  if params_names_nodup_b (fn_params fdef)
  then
    match fn_body fdef with
    | ECallExpr (EVar fparam) body_args =>
        if param_name_in_b fparam (fn_params fdef)
        then Some (fparam, body_args)
        else None
    | _ => None
    end
  else None.

Definition direct_generic_call_for_let_wrapper_adapter
    (env : global_env) (x wrapper_name adapter_name : ident)
    (call_args : list expr) : option expr :=
  match lookup_fn_b wrapper_name (env_fns env),
        lookup_fn_b adapter_name (env_fns env) with
  | Some wrapper, Some adapter =>
      match generic_fn_wrapper_target wrapper,
            adapter_call_target adapter with
      | Some (target, type_args), Some (fparam, adapter_body_args) =>
          if adapter_call_uses_bound_fn_only x fparam (fn_params adapter) call_args
          then
            match adapter_body_actual_args fparam (fn_params adapter)
                    call_args adapter_body_args with
            | Some actual_args => Some (ECallGeneric target type_args actual_args)
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint infer_core_env_state_fuel_elab (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx * expr) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ, e)
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ, e)
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ, e)
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ, e)
  | EVar x =>
      match infer_place_sctx env Σ (PVar x) with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ (PVar x) T with
          | infer_ok Σ' => infer_ok (T, Σ', e)
          | infer_err err => infer_err err
          end
      end
  | EPlace p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ p T with
          | infer_ok Σ' => infer_ok (T, Σ', e)
          | infer_err err => infer_err err
          end
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ, e)
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ,
                EMakeClosure fname captures)
          | infer_err err => infer_err err
          end
      end
  | EStruct sname lts args fields =>
      match lookup_struct sname env with
      | None => infer_err (ErrStructNotFound sname)
      | Some s =>
          if negb (Nat.eqb (List.length lts) (struct_lifetimes s))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (struct_type_params s))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (struct_bounds s) args with
          | Some err => infer_err err
          | None =>
              match first_duplicate_field fields with
              | Some name => infer_err (ErrDuplicateField name)
              | None =>
                  match first_unknown_field fields (struct_fields s) with
                  | Some name => infer_err (ErrFieldNotFound name)
                  | None =>
                      match first_missing_field (struct_fields s) fields with
                      | Some name => infer_err (ErrMissingField name)
                      | None =>
                          let fix go (Σ0 : sctx) (defs : list field_def)
                              : infer_result (sctx * list (string * expr)) :=
                            match defs with
                            | [] => infer_ok (Σ0, [])
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1, e_field') =>
                                        let T_expected := instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then match go Σ1 rest with
                                             | infer_err err => infer_err err
                                             | infer_ok (Σ2, fields') =>
                                                 infer_ok (Σ2, (field_name f, e_field') :: fields')
                                             end
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok (Σ', fields') =>
                              infer_ok (instantiate_struct_instance_ty s lts args,
                                        Σ',
                                        EStruct sname lts args fields')
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts args payloads =>
      match lookup_enum enum_name env with
      | None => infer_err (ErrEnumNotFound enum_name)
      | Some edef =>
          if negb (Nat.eqb (List.length lts) (enum_lifetimes edef))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (enum_type_params edef))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (enum_bounds edef) args with
          | Some err => infer_err err
          | None =>
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  let fix go (Σ0 : sctx) (fields : list Ty) (es : list expr)
                      : infer_result (sctx * list expr) :=
                    match fields, es with
                    | [], [] => infer_ok (Σ0, [])
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1, e_payload') =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then match go Σ1 fields' es' with
                                 | infer_err err => infer_err err
                                 | infer_ok (Σ2, payloads') =>
                                     infer_ok (Σ2, e_payload' :: payloads')
                                 end
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok (Σ', payloads') =>
                      infer_ok (instantiate_enum_ty edef lts args, Σ',
                        EEnum enum_name variant_name lts args payloads')
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1, scrut') =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  match first_duplicate_branch branches with
                  | Some name => infer_err (ErrDuplicateVariant name)
                  | None =>
	                      match first_unknown_variant_branch branches (enum_variants edef) with
	                      | Some name => infer_err (ErrVariantNotFound name)
	                      | None =>
	                          match first_missing_variant_branch (enum_variants edef) branches with
                          | Some name => infer_err (ErrMissingVariant name)
                          | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result
                                          (Ty * list sctx * list Ty *
                                           list (string * list ident * expr)) :=
                                    match defs with
                                    | [] => infer_err (ErrMissingVariant "")
                                    | v :: rest =>
                                        let infer_branch :=
                                          fun (v0 : enum_variant_def) =>
                                          match lookup_expr_branch_binders (enum_variant_name v0) branches,
                                                lookup_branch_b (enum_variant_name v0) branches with
                                          | Some binders, Some e_branch =>
                                              match match_payload_params binders lts args v0 with
                                              | infer_err err => infer_err err
                                              | infer_ok ps =>
                                                  if params_names_nodup_b ps &&
                                                     ctx_lookup_params_none_b ps Σ1
                                                  then
                                                  match infer_core_env_state_fuel_elab fuel' env Ω n
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload, e_branch') =>
                                                      if params_ok_sctx_b env ps Σ_branch_payload
                                                      then infer_ok
                                                        (T_branch,
                                                         sctx_remove_params ps Σ_branch_payload,
                                                         e_branch',
                                                         binders)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch, e_branch', binders) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result
                                                        (list sctx * list Ty *
                                                         list (string * list ident * expr)) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0, e0', binders0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_result :=
                                                                  infer_rest T_head rest0 in
                                                                match rest_result with
                                                                | infer_err err => infer_err err
                                                                | infer_ok (Σs, Ts, bs) =>
                                                                    infer_ok
                                                                      (Σ0 :: Σs, T0 :: Ts,
                                                                       (enum_variant_name v0, binders0, e0') :: bs)
                                                                end
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts, bs) =>
                                                    infer_ok
                                                      (T_branch, Σ_branch :: Σs, Ts,
                                                       (enum_variant_name v, binders, e_branch') :: bs)
                                                end
                                            end
                                    end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head :: Σ_tail, Ts_tail, branches') =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
                                                  (ty_core T_head),
                                             sctx_of_ctx Γ_out,
                                             EMatch scrut' branches')
                                      | None => infer_err ErrContextCheckFailed
                                      end
	                                  | infer_ok (_, [], _, _) => infer_err ErrContextCheckFailed
	                                  end
	                          end
	                      end
                  end
              end
          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, e1') =>
          if ty_compatible_b Ω T1 T
          then match infer_core_env_state_fuel_elab fuel' env Ω n (sctx_add x T m Σ1) e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2, e2') =>
                   if sctx_check_ok env x T Σ2
                   then
                     match e1', e2' with
                     | EFn fname, ECallExprGeneric (EVar y) type_args args' =>
                         if ident_eqb x y &&
                            negb (existsb (fun arg => ident_in_b x (free_vars_expr arg)) args') &&
                            negb (ident_in_b x (args_local_store_names args'))
                         then
                           match infer_core_env_state_fuel_elab fuel' env Ω n Σ
                                   (ECallGeneric fname type_args args') with
                           | infer_ok direct => infer_ok direct
                           | infer_err _ => infer_ok (T2, sctx_remove x Σ2,
                               ELet m x T e1' e2')
                           end
                         else infer_ok (T2, sctx_remove x Σ2, ELet m x T e1' e2')
                     | EFn wrapper_name, ECall adapter_name call_args =>
                         if usage_eqb (ty_usage T) UUnrestricted
                         then
                           match direct_generic_call_for_let_wrapper_adapter
                                   env x wrapper_name adapter_name call_args with
                           | Some direct_call =>
                               match infer_core_env_state_fuel_elab fuel' env Ω n Σ
                                       direct_call with
                               | infer_ok direct => infer_ok direct
                               | infer_err _ => infer_ok (T2, sctx_remove x Σ2,
                                   ELet m x T e1' e2')
                               end
                           | None => infer_ok (T2, sctx_remove x Σ2,
                               ELet m x T e1' e2')
                           end
                         else infer_ok (T2, sctx_remove x Σ2,
                             ELet m x T e1' e2')
                     | _, _ => infer_ok (T2, sctx_remove x Σ2, ELet m x T e1' e2')
                     end
                   else infer_err ErrContextCheckFailed
               end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, e1') =>
          match infer_core_env_state_fuel_elab fuel' env Ω n (sctx_add x T1 m Σ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Σ2, e2') =>
              if sctx_check_ok env x T1 Σ2
              then infer_ok (T2, sctx_remove x Σ2, ELet m x T1 e1' e2')
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ', e1') =>
          infer_ok (MkTy UUnrestricted TUnits, Σ', EDrop e1')
      end
  | EReplace p e_new =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_old =>
          let root := place_name p in
          match place_path p with
          | Some (x, path) =>
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1, e_new') =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ =>
                                    match sctx_restore_path Σ1 x path with
                                    | infer_ok Σ2 => infer_ok (T_old, Σ2, EReplace p e_new')
                                    | infer_err err => infer_err err
                                    end
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1, e_new') =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (T_old, Σ1, EReplace p e_new')
                       else infer_err (compatible_error T_new T_old)
                   end
              else infer_err (ErrNotMutable root)
          end
      end
  | EAssign p e_new =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_old =>
          if usage_eqb (ty_usage T_old) ULinear
          then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
          else
          let root := place_name p in
          match place_path p with
          | Some (x, path) =>
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1, e_new') =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ =>
                                    infer_ok (MkTy UUnrestricted TUnits, Σ1, EAssign p e_new')
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1, e_new') =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (MkTy UUnrestricted TUnits, Σ1, EAssign p e_new')
                       else infer_err (compatible_error T_new T_old)
                   end
              else infer_err (ErrNotMutable root)
          end
      end
  | EBorrow rk p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match rk with
          | RShared => infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, e)
          | RUnique =>
              match place_path p with
              | Some (x, _) =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable => infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, e)
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              | None =>
                  if place_under_unique_ref_b env Σ p
                  then infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, e)
                  else infer_err (ErrImmutableBorrow (place_name p))
              end
          end
      end
  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_r =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ, EDeref r)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core_env_state_fuel_elab fuel' env Ω n Σ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Σ', r') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ', EDeref r')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1, e1') =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then match infer_core_env_state_fuel_elab fuel' env Ω n Σ1 e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2, e2') =>
                   match infer_core_env_state_fuel_elab fuel' env Ω n Σ1 e3 with
                   | infer_err err => infer_err err
                   | infer_ok (T3, Σ3, e3') =>
                       if ty_core_eqb (ty_core T2) (ty_core T3)
                       then match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                            | Some Γ4 => infer_ok
                                (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                                 sctx_of_ctx Γ4,
                                 EIf e1' e2' e3')
                            | None => infer_err ErrContextCheckFailed
                            end
                       else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                   end
               end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx * list expr) :=
            match as_ with
            | [] => infer_ok ([], Σ0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, e_elab) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, es_elab) =>
                        infer_ok (T_e :: tys, Σ2, e_elab :: es_elab)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', args') =>
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
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Σ', ECall fname args')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end
  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          match check_struct_bounds env (fn_bounds fdef) type_args with
          | Some err => infer_err err
          | None =>
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx * list expr) :=
            match as_ with
            | [] => infer_ok ([], Σ0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, e_elab) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, es_elab) =>
                        infer_ok (T_e :: tys, Σ2, e_elab :: es_elab)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', args') =>
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
                            (subst_type_params_ty type_args (fn_ret fdef)),
                           Σ',
                           ECallGeneric fname type_args args')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | ECallExpr callee args =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σc, callee') =>
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx * list expr) :=
            match as_ with
            | [] => infer_ok ([], Σ0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, e_elab) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, es_elab) =>
                        infer_ok (T_e :: tys, Σ2, e_elab :: es_elab)
                    end
                end
            end
          in
          match collect Σc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', args') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ', ECallExpr callee' args')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ', ECallExpr callee' args')
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env_elab env Ω type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok (type_args, ret) =>
                      infer_ok (ret, Σ', ECallExprGeneric callee' type_args args')
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env_elab env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok (type_args, ret) =>
                          infer_ok (ret, Σ',
                            ECallExprGeneric callee' type_args args')
                      end
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
                                   then infer_ok (ret_open, Σ', ECallExpr callee' args')
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
                                   then infer_ok (ret_open, Σ', ECallExpr callee' args')
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
  end
  end.

Definition infer_core_env_elab
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx * expr) :=
  match infer_core_env_state_fuel_elab 10000 env Ω n (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ, e') => infer_ok (T, ctx_of_sctx Σ, e')
  | infer_err err => infer_err err
  end.

