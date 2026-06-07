From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Fixpoint infer_core_env_state_fuel (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ)
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ)
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ)
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ)
  | EVar x =>
      match infer_place_sctx env Σ (PVar x) with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ (PVar x) T with
          | infer_ok Σ' => infer_ok (T, Σ')
          | infer_err err => infer_err err
          end
      end
  | EPlace p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ p T with
          | infer_ok Σ' => infer_ok (T, Σ')
          | infer_err err => infer_err err
          end
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ)
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ)
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
                              : infer_result sctx :=
                            match defs with
                            | [] => infer_ok Σ0
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel fuel' env Ω n Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1) =>
                                        let T_expected := instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then go Σ1 rest
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok Σ' => infer_ok (instantiate_struct_instance_ty s lts args, Σ')
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
                  let fix go (Σ0 : sctx) (fields : list Ty) (es : list expr)
                      : infer_result sctx :=
                    match fields, es with
                    | [], [] => infer_ok Σ0
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel fuel' env Ω n Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts variant_lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then go Σ1 fields' es'
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok Σ' => infer_ok (instantiate_enum_ty edef lts args, Σ')
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel fuel' env Ω n Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1) =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  if negb (Nat.eqb (Datatypes.length lts) (enum_lifetimes edef))
                  then infer_err ErrArityMismatch
                  else if negb (Nat.eqb (Datatypes.length args) (enum_type_params edef))
                  then infer_err ErrArityMismatch
                  else match check_struct_bounds env (enum_bounds edef) args with
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
                                      : infer_result (Ty * list sctx * list Ty) :=
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
                                                  match infer_core_env_state_fuel fuel' env Ω n
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload) =>
                                                      if contains_lbound_ty T_branch
                                                      then infer_err ErrLifetimeLeak
                                                      else if params_ok_sctx_b env ps Σ_branch_payload
                                                      then infer_ok
                                                        (T_branch, sctx_remove_params ps Σ_branch_payload)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result (list sctx * list Ty) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_result :=
                                                                  infer_rest T_head rest0 in
                                                                match rest_result with
                                                                | infer_err err => infer_err err
                                                                | infer_ok (Σs, Ts) =>
                                                                    infer_ok (Σ0 :: Σs, T0 :: Ts)
                                                                end
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts) =>
                                                    infer_ok (T_branch, Σ_branch :: Σs, Ts)
                                                end
                                            end
                                        end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head :: Σ_tail, Ts_tail) =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
                                                  (ty_core T_head), sctx_of_ctx Γ_out)
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
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1) =>
          if ty_compatible_b Ω T1 T
          then match infer_core_env_state_fuel fuel' env Ω n (sctx_add x T m Σ1) e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2) =>
                   if sctx_check_ok env x T Σ2
                   then infer_ok (T2, sctx_remove x Σ2)
                   else infer_err ErrContextCheckFailed
               end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1) =>
          match infer_core_env_state_fuel fuel' env Ω n (sctx_add x T1 m Σ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Σ2) =>
              if sctx_check_ok env x T1 Σ2
              then infer_ok (T2, sctx_remove x Σ2)
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ') => infer_ok (MkTy UUnrestricted TUnits, Σ')
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
                  then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1) =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ =>
                                    match sctx_restore_path Σ1 x path with
                                    | infer_ok Σ2 => infer_ok (T_old, Σ2)
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
              then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1) =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (T_old, Σ1)
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
                  then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1) =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ => infer_ok (MkTy UUnrestricted TUnits, Σ1)
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1) =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (MkTy UUnrestricted TUnits, Σ1)
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
          | RShared => infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ)
          | RUnique =>
              match place_path p with
              | Some (x, _) =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable => infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ)
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              | None =>
                  if place_under_unique_ref_b env Σ p
                  then infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ)
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
                  then infer_ok (T_inner, Σ)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core_env_state_fuel fuel' env Ω n Σ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Σ') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then match infer_core_env_state_fuel fuel' env Ω n Σ1 e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2) =>
                   match infer_core_env_state_fuel fuel' env Ω n Σ1 e3 with
                   | infer_err err => infer_err err
                   | infer_ok (T3, Σ3) =>
                       if ty_core_eqb (ty_core T2) (ty_core T3)
                       then match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                            | Some Γ4 => infer_ok
                                (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                                 sctx_of_ctx Γ4)
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
              : infer_result (list Ty * sctx) :=
            match as_ with
            | [] => infer_ok ([], Σ0)
            | e' :: es =>
                match infer_core_env_state_fuel fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ') =>
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
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Σ')
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
              : infer_result (list Ty * sctx) :=
            match as_ with
            | [] => infer_ok ([], Σ0)
            | e' :: es =>
                match infer_core_env_state_fuel fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ') =>
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
                            (subst_type_params_ty type_args (fn_ret fdef)), Σ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | ECallExpr callee args =>
      match infer_core_env_state_fuel fuel' env Ω n Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σc) =>
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx) :=
            match as_ with
            | [] => infer_ok ([], Σ0)
            | e' :: es =>
                match infer_core_env_state_fuel fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
                    end
                end
            end
          in
          match collect Σc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ')
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Σ')
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
	                      | infer_ok ret => infer_ok (ret, Σ')
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
                                   then infer_ok (ret_open, Σ')
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
                                   then infer_ok (ret_open, Σ')
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

Definition infer_core_env
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match infer_core_env_state_fuel 10000 env Ω n (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ) => infer_ok (T, ctx_of_sctx Σ)
  | infer_err err => infer_err err
  end.

