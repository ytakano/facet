From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore AssocDirectCallHelpers AssocFnValueCallHelpers AssocHrtHelpers.
From Stdlib Require Import List String Bool.
Import ListNotations.

Fixpoint infer_core_env_fuel (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
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
      | None => infer_err (ErrUnknownVar x)
      | Some (T, b) =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else if b
               then infer_err (ErrAlreadyConsumed x)
               else match ctx_consume_b x Γ with
                    | Some Γ' => infer_ok (T, Γ')
                    | None => infer_err (ErrUnknownVar x)
                    end
      end
  | EPlace p =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else match p with
               | PVar x =>
                   match ctx_consume_b x Γ with
                   | Some Γ' => infer_ok (T, Γ')
                   | None => infer_err (ErrUnknownVar x)
                   end
               | PField q _ =>
                   match ctx_consume_b (place_name q) Γ with
                   | Some Γ' => infer_ok (T, Γ')
                   | None => infer_err (ErrUnknownVar (place_name q))
                   end
               | PDeref _ => infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
               end
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Γ)
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_ctx env Ω Γ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Γ)
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
                          let fix go (Γ0 : ctx) (defs : list field_def)
                              : infer_result ctx :=
                            match defs with
                            | [] => infer_ok Γ0
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_fuel fuel' env Ω n Γ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Γ1) =>
                                        let T_expected := instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then go Γ1 rest
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Γ (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok Γ' => infer_ok (instantiate_struct_ty s lts args, Γ')
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts variant_lts args payloads =>
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
              if negb (enum_outlives_hold_b Ω edef lts)
              then infer_err ErrLifetimeConflict
              else
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  if negb (Nat.eqb (List.length variant_lts)
                      (enum_variant_lifetimes vdef))
                  then infer_err ErrArityMismatch
                  else
                  let fix go (Γ0 : ctx) (fields : list Ty) (es : list expr)
                      : infer_result ctx :=
                    match fields, es with
                    | [], [] => infer_ok Γ0
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_fuel fuel' env Ω n Γ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Γ1) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts variant_lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then go Γ1 fields' es'
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Γ (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok Γ' => infer_ok (instantiate_enum_ty edef lts args, Γ')
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_fuel fuel' env Ω n Γ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Γ1) =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  if negb (Nat.eqb (Datatypes.length lts) (enum_lifetimes edef))
                  then infer_err ErrArityMismatch
                  else if negb (Nat.eqb (Datatypes.length args) (enum_type_params edef))
                  then infer_err ErrArityMismatch
                  else
                    match check_struct_bounds env (enum_bounds edef) args with
                    | Some err => infer_err err
                    | None =>
                        if negb (enum_outlives_hold_b Ω edef lts)
                        then infer_err ErrLifetimeConflict
                        else
                        match first_duplicate_branch branches with
                        | Some name => infer_err (ErrDuplicateVariant name)
                        | None =>
                            match first_unknown_variant_branch branches (enum_variants edef) with
                            | Some name => infer_err (ErrVariantNotFound name)
                            | None =>
                                match first_unsupported_match_payload branches
                                        (enum_variants edef) with
                                | Some name => infer_err (ErrMatchPayloadUnsupported name)
                                | None =>
                                match first_missing_variant_branch (enum_variants edef) branches with
                                | Some name => infer_err (ErrMissingVariant name)
                                | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result (Ty * list ctx * list Ty) :=
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
                                                     ctx_lookup_params_none_b ps Γ1
                                                  then
                                                  match infer_core_env_fuel fuel' env Ω n
                                                          (ctx_add_params ps Γ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Γ_branch_payload) =>
                                                      if contains_lbound_ty T_branch
                                                      then infer_err ErrLifetimeLeak
                                                      else if ctx_check_ok_params ps Γ_branch_payload
                                                      then infer_ok
                                                        (T_branch, ctx_remove_params ps Γ_branch_payload)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Γ_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result (list ctx * list Ty) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Γ0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_result :=
                                                                  infer_rest T_head rest0 in
                                                                match rest_result with
                                                                | infer_err err => infer_err err
                                                                | infer_ok (Γs, Ts) =>
                                                                    infer_ok (Γ0 :: Γs, T0 :: Ts)
                                                                end
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                      end
                                                  end
                                                in
                                                match infer_rest T_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Γs, Ts) =>
                                                    infer_ok (T_branch, Γ_branch :: Γs, Ts)
                                                end
                                            end
                                        end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Γ_head :: Γ_tail, Ts_tail) =>
                                      match ctx_merge_many Γ_head Γ_tail with
	                                      | Some Γ_out =>
	                                          infer_ok
	                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
	                                                  (ty_core T_head), Γ_out)
	                                      | None => infer_err ErrContextCheckFailed
	                                      end
	                                  | infer_ok (_, [], _) => infer_err ErrContextCheckFailed
	                                  end
	                                end
	                            end
		                        end
		                  end
		                  end
			              end
			          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          if ty_compatible_b Ω T1 T
          then match infer_core_env_fuel fuel' env Ω n (ctx_add_b x T m Γ1) e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Γ2) =>
                   if ctx_check_ok x T Γ2
                   then infer_ok (T2, ctx_remove_b x Γ2)
                   else infer_err ErrContextCheckFailed
               end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          match infer_core_env_fuel fuel' env Ω n (ctx_add_b x T1 m Γ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Γ2) =>
              if ctx_check_ok x T1 Γ2
              then infer_ok (T2, ctx_remove_b x Γ2)
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Γ') => infer_ok (MkTy UUnrestricted TUnits, Γ')
      end
  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | Some MMutable =>
              match infer_core_env_fuel fuel' env Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_x
                  then infer_ok (T_x, Γ')
                  else infer_err (compatible_error T_new T_x)
              end
          | Some MImmutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | EReplace (PDeref p) e_new =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              match infer_core_env_fuel fuel' env Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_inner
                  then infer_ok (T_inner, Γ')
                  else infer_err (compatible_error T_new T_inner)
              end
          | c => infer_err (ErrNotAReference c)
          end
      end
  | EReplace (PField p field) e_new =>
      match infer_place_env env Γ (PField p field) with
      | infer_err err => infer_err err
      | infer_ok T_field =>
          match ctx_lookup_mut_b (place_name p) Γ with
          | Some MMutable =>
              match infer_core_env_fuel fuel' env Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_field
                  then infer_ok (T_field, Γ')
                  else infer_err (compatible_error T_new T_field)
              end
          | Some MImmutable => infer_err (ErrNotMutable (place_name p))
          | None => infer_err (ErrUnknownVar (place_name p))
          end
      end
  | EAssign (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | Some MMutable =>
              if usage_eqb (ty_usage T_x) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_x) UAffine)
              else match infer_core_env_fuel fuel' env Ω n Γ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Γ') =>
                       if ty_compatible_b Ω T_new T_x
                       then infer_ok (MkTy UUnrestricted TUnits, Γ')
                       else infer_err (compatible_error T_new T_x)
                   end
          | Some MImmutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | EAssign (PDeref p) e_new =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              if usage_eqb (ty_usage T_inner) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_inner) UAffine)
              else match infer_core_env_fuel fuel' env Ω n Γ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Γ') =>
                       if ty_compatible_b Ω T_new T_inner
                       then infer_ok (MkTy UUnrestricted TUnits, Γ')
                       else infer_err (compatible_error T_new T_inner)
                   end
          | c => infer_err (ErrNotAReference c)
          end
      end
  | EAssign (PField p field) e_new =>
      match infer_place_env env Γ (PField p field) with
      | infer_err err => infer_err err
      | infer_ok T_field =>
          match ctx_lookup_mut_b (place_name p) Γ with
          | Some MMutable =>
              if usage_eqb (ty_usage T_field) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_field) UAffine)
              else match infer_core_env_fuel fuel' env Ω n Γ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Γ') =>
                       if ty_compatible_b Ω T_new T_field
                       then infer_ok (MkTy UUnrestricted TUnits, Γ')
                       else infer_err (compatible_error T_new T_field)
                   end
          | Some MImmutable => infer_err (ErrNotMutable (place_name p))
          | None => infer_err (ErrUnknownVar (place_name p))
          end
      end
  | EBorrow rk p =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match rk with
          | RShared => infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Γ)
          | RUnique =>
              match ctx_lookup_mut_b (place_name p) Γ with
              | Some MMutable => infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Γ)
              | Some MImmutable => infer_err (ErrImmutableBorrow (place_name p))
              | None => infer_err (ErrUnknownVar (place_name p))
              end
          end
      end
  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place_env env Γ p with
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
          match infer_core_env_fuel fuel' env Ω n Γ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Γ') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end
  | EIf e1 e2 e3 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Γ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then match infer_core_env_fuel fuel' env Ω n Γ1 e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Γ2) =>
                   match infer_core_env_fuel fuel' env Ω n Γ1 e3 with
                   | infer_err err => infer_err err
                   | infer_ok (T3, Γ3) =>
                       if ty_core_eqb (ty_core T2) (ty_core T3)
                       then match ctx_merge Γ2 Γ3 with
                            | Some Γ4 =>
                                infer_ok (MkTy (usage_max (ty_usage T2) (ty_usage T3))
                                               (ty_core T2), Γ4)
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
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | [] => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core_env_fuel fuel' env Ω n Γ0 e' with
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
              match infer_direct_call_assoc env Ω n fdef arg_tys with
              | infer_err err => infer_err err
              | infer_ok ret => infer_ok (ret, Γ')
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
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | [] => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core_env_fuel fuel' env Ω n Γ0 e' with
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
              match infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys with
              | infer_err err => infer_err err
              | infer_ok ret => infer_ok (ret, Γ')
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | ECallExpr callee args =>
      match infer_core_env_fuel fuel' env Ω n Γ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Γc) =>
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | [] => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core_env_fuel fuel' env Ω n Γ0 e' with
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
              | TFn _ _ =>
                  match infer_fn_value_call_assoc env Ω T_callee arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Γ')
                  end
              | TClosure _ _ _ =>
                  match infer_fn_value_call_assoc env Ω T_callee arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Γ')
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env_assoc env Ω type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Γ')
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env_assoc env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret => infer_ok (ret, Γ')
                      end
                  | TFn _ _ =>
                      match infer_hrt_call_env_assoc env Ω n m bounds body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret => infer_ok (ret, Γ')
                      end
                  | TClosure _ _ _ =>
                      match infer_hrt_call_env_assoc env Ω n m bounds body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret => infer_ok (ret, Γ')
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

