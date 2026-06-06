From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Fixpoint infer_core_env_state_fuel_roots_shadow_safe (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx * root_env * root_set) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ, R, [])
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ, R, [])
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ, R, [])
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ, R, [])
  | EVar x =>
      match consume_direct_place_value_roots env Σ R (PVar x) with
      | infer_ok (T, Σ', roots) => infer_ok (T, Σ', R, roots)
      | infer_err err => infer_err err
      end
  | EPlace p =>
      match consume_direct_place_value_roots env Σ R p with
      | infer_ok (T, Σ', roots) => infer_ok (T, Σ', R, roots)
      | infer_err err => infer_err err
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, R1, roots_e) =>
                    match collect Σ1 R1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, R2, roots_es) =>
                        infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ R args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
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
                        then
                          infer_ok
                            (apply_lt_ty σ (fn_ret fdef), Σ', R',
                             root_sets_union arg_roots)
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
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, R1, roots_e) =>
                    match collect Σ1 R1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, R2, roots_es) =>
                        infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ R args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
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
                           Σ', R', root_sets_union arg_roots)
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ, R, [])
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ, R, [])
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
                          let fix go (Σ0 : sctx) (R0 : root_env)
                              (defs : list field_def)
                              : infer_result (sctx * root_env * root_set) :=
                            match defs with
                            | [] => infer_ok (Σ0, R0, [])
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel_roots_shadow_safe
                                            fuel' env Ω n R0 Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1, R1, roots_field) =>
                                        let T_expected :=
                                          instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then
                                          match go Σ1 R1 rest with
                                          | infer_err err => infer_err err
                                          | infer_ok (Σ2, R2, roots_rest) =>
                                              infer_ok
                                                (Σ2, R2,
                                                 root_set_union roots_field roots_rest)
                                          end
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ R (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok (Σ', R', roots) =>
                              infer_ok
                                (instantiate_struct_instance_ty s lts args, Σ', R', roots)
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
                  let fix go (Σ0 : sctx) (R0 : root_env)
                      (fields : list Ty) (es : list expr)
                      : infer_result (sctx * root_env * root_set) :=
                    match fields, es with
                    | [], [] => infer_ok (Σ0, R0, [])
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel_roots_shadow_safe
                                fuel' env Ω n R0 Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1, R1, roots_payload) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then
                              match go Σ1 R1 fields' es' with
                              | infer_err err => infer_err err
                              | infer_ok (Σ2, R2, roots_rest) =>
                                  infer_ok
                                    (Σ2, R2,
                                     root_set_union roots_payload roots_rest)
                              end
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ R (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok (Σ', R', roots) =>
                      infer_ok (instantiate_enum_ty edef lts args, Σ', R', roots)
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1, R1, roots_scrut) =>
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
                                          (Ty * sctx * root_env * root_set *
                                           list sctx * list Ty * list root_set) :=
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
                                                     ctx_lookup_params_none_b ps Σ1 &&
                                                     root_env_lookup_params_none_b ps R1
                                                  then
                                                  let R_payload :=
                                                    root_env_add_params_roots_same ps roots_scrut R1 in
                                                  match infer_core_env_state_fuel_roots_shadow_safe
                                                          fuel' env Ω n R_payload
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload,
                                                              R_branch_payload, roots_branch) =>
                                                      let R_branch :=
                                                        root_env_remove_match_params ps R_branch_payload in
                                                      if params_ok_sctx_b env ps Σ_branch_payload &&
                                                         roots_exclude_params_b ps roots_branch &&
                                                         root_env_excludes_params_b ps R_branch
                                                      then infer_ok
                                                        (T_branch,
                                                         sctx_remove_params ps Σ_branch_payload,
                                                         R_branch,
                                                         roots_branch)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch, R_branch, roots_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (R_out : root_env)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result
                                                        (list sctx * list Ty * list root_set) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0, R0, roots0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_ok :=
                                                                  let rest_result :=
                                                                    infer_rest T_head R_out rest0 in
                                                                  match rest_result with
                                                                  | infer_err err => infer_err err
                                                                  | infer_ok (Σs, Ts, rootss) =>
                                                                      infer_ok
                                                                        (Σ0 :: Σs,
                                                                         T0 :: Ts,
                                                                         roots0 :: rootss)
                                                                  end
                                                                in
                                                                let context_error :=
                                                                  infer_err ErrContextCheckFailed in
                                                                infer_if_bool
                                                                  (root_env_eqb R0 R_out)
                                                                  rest_ok context_error
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch R_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts, rootss) =>
                                                    infer_ok
                                                      (T_branch, Σ_branch, R_branch, roots_branch,
                                                       Σs, Ts, rootss)
	                                  end
	                          end
	                          end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head, R_out, roots_head,
                                              Σ_tail, Ts_tail, roots_tail) =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
	                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
	                                                  (ty_core T_head),
	                                             sctx_of_ctx Γ_out, R_out,
	                                             root_sets_union (roots_head :: roots_tail))
	                                      | None => infer_err ErrContextCheckFailed
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
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, R1, roots1) =>
          if ty_compatible_b Ω T1 T
          then
            match root_env_lookup x R1 with
            | Some _ => infer_err ErrContextCheckFailed
            | None =>
                if roots_exclude_b x roots1 && root_env_excludes_b x R1
                then
                  match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
                          (root_env_add x roots1 R1) (sctx_add x T m Σ1) e2 with
                  | infer_err err => infer_err err
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      if sctx_check_ok env x T Σ2 &&
                         roots_exclude_b x roots2 &&
                         root_env_excludes_b x (root_env_remove x R2)
                      then infer_ok (T2, sctx_remove x Σ2, root_env_remove x R2, roots2)
                      else infer_err ErrContextCheckFailed
                  end
                else infer_err ErrContextCheckFailed
            end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, R1, roots1) =>
          match root_env_lookup x R1 with
          | Some _ => infer_err ErrContextCheckFailed
          | None =>
              if roots_exclude_b x roots1 && root_env_excludes_b x R1
              then
                match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
                        (root_env_add x roots1 R1) (sctx_add x T1 m Σ1) e2 with
                | infer_err err => infer_err err
                | infer_ok (T2, Σ2, R2, roots2) =>
                    if sctx_check_ok env x T1 Σ2 &&
                       roots_exclude_b x roots2 &&
                       root_env_excludes_b x (root_env_remove x R2)
                    then infer_ok (T2, sctx_remove x Σ2, root_env_remove x R2, roots2)
                    else infer_err ErrContextCheckFailed
                end
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ', R', _) => infer_ok (MkTy UUnrestricted TUnits, Σ', R', [])
      end
  | EReplace p e_new =>
      match place_path p with
      | None =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if place_resolved_write_writable_chain_b env R Σ p then
              match place_resolved_write_target R p with
              | None => infer_err ErrNotImplemented
              | Some x =>
                  match root_env_lookup x R with
                  | None => infer_err ErrContextCheckFailed
                  | Some roots_result =>
                      match sctx_lookup_mut x Σ with
                      | Some MMutable =>
                          if writable_place_b env Σ p
                          then
                            match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e_new with
                            | infer_err err => infer_err err
                            | infer_ok (T_new, Σ1, R1, roots_new) =>
                                match root_env_lookup x R1 with
                                | None => infer_err ErrContextCheckFailed
                                | Some roots_old =>
                                    if ty_compatible_b Ω T_new T_old
                                    then
                                      infer_ok
                                        (T_old, Σ1,
                                         root_env_update x
                                           (root_set_union roots_old roots_new) R1,
                                         roots_result)
                                    else infer_err (compatible_error T_new T_old)
                                end
                            end
                          else infer_err (ErrNotMutable x)
                      | Some MImmutable => infer_err (ErrNotMutable x)
                      | None => infer_err (ErrUnknownVar x)
                      end
                  end
              end
              else infer_err ErrNotImplemented
          end
      | Some (x, path) =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              match root_env_lookup x R with
              | None => infer_err ErrContextCheckFailed
              | Some roots_result =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      if writable_place_b env Σ p
                      then
                        match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e_new with
                        | infer_err err => infer_err err
                        | infer_ok (T_new, Σ1, R1, roots_new) =>
                            match root_env_lookup x R1 with
                            | None => infer_err ErrContextCheckFailed
                            | Some roots_old =>
                                if ty_compatible_b Ω T_new T_old
                                then
                                  match sctx_path_available Σ1 x path with
                                  | infer_err err => infer_err err
                                  | infer_ok _ =>
                                      match sctx_restore_path Σ1 x path with
                                      | infer_ok Σ2 =>
                                          infer_ok
                                            (T_old, Σ2,
                                             root_env_update x
                                               (root_set_union roots_old roots_new) R1,
                                             roots_result)
                                      | infer_err err => infer_err err
                                      end
                                  end
                                else infer_err (compatible_error T_new T_old)
                            end
                        end
                      else infer_err (ErrNotMutable x)
                  | Some MImmutable => infer_err (ErrNotMutable x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
          end
      end
  | EAssign p e_new =>
      match place_path p with
      | None =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if usage_eqb (ty_usage T_old) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
              else
              if place_resolved_write_writable_chain_b env R Σ p then
              match place_resolved_write_target R p with
              | None => infer_err ErrNotImplemented
              | Some x =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      if writable_place_b env Σ p
                      then
                        match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e_new with
                        | infer_err err => infer_err err
                        | infer_ok (T_new, Σ1, R1, roots_new) =>
                            match root_env_lookup x R1 with
                            | None => infer_err ErrContextCheckFailed
                            | Some roots_old =>
                                if ty_compatible_b Ω T_new T_old
                                then
                                  infer_ok
                                    (MkTy UUnrestricted TUnits, Σ1,
                                     root_env_update x
                                       (root_set_union roots_old roots_new) R1,
                                     [])
                                else infer_err (compatible_error T_new T_old)
                            end
                        end
                      else infer_err (ErrNotMutable x)
                  | Some MImmutable => infer_err (ErrNotMutable x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
              else infer_err ErrNotImplemented
          end
      | Some (x, path) =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if usage_eqb (ty_usage T_old) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
              else
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then
                    match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e_new with
                    | infer_err err => infer_err err
                    | infer_ok (T_new, Σ1, R1, roots_new) =>
                        match root_env_lookup x R1 with
                        | None => infer_err ErrContextCheckFailed
                        | Some roots_old =>
                            if ty_compatible_b Ω T_new T_old
                            then
                              match sctx_path_available Σ1 x path with
                              | infer_err err => infer_err err
                              | infer_ok _ =>
                                  infer_ok
                                    (MkTy UUnrestricted TUnits, Σ1,
                                     root_env_update x
                                       (root_set_union roots_old roots_new) R1,
                                     [])
                              end
                            else infer_err (compatible_error T_new T_old)
                        end
                    end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          end
      end
  | EBorrow rk p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match place_path p with
          | Some (x, _) =>
              match rk with
              | RShared =>
                  infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, [RStore x])
              | RUnique =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, [RStore x])
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
          | None =>
              match rk with
              | RShared =>
                  match place_resolved_roots R p with
                  | Some roots =>
                      match singleton_store_root roots with
                      | Some root_x =>
                          match root_env_lookup root_x R with
                          | Some roots_x =>
                              match singleton_store_root roots_x with
                              | Some root_y =>
                                  if ident_eqb root_x root_y
                                  then infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                                  else
                                    match place_borrow_roots R p with
                                    | Some roots =>
                                        infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                                    | None => infer_err ErrContextCheckFailed
                                    end
                              | None =>
                                  match place_borrow_roots R p with
                                  | Some roots =>
                                      infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                                  | None => infer_err ErrContextCheckFailed
                                  end
                              end
                          | None =>
                              match place_borrow_roots R p with
                              | Some roots =>
                                  infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                              | None => infer_err ErrContextCheckFailed
                              end
                          end
                      | None =>
                          match place_borrow_roots R p with
                          | Some roots =>
                              infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                          | None => infer_err ErrContextCheckFailed
                          end
                      end
                  | None =>
                      match place_borrow_roots R p with
                      | Some roots =>
                          infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                      | None => infer_err ErrContextCheckFailed
                      end
                  end
              | RUnique =>
                  if place_under_unique_ref_b env Σ p
                  then
                    match
                      if place_resolved_write_writable_chain_b env R Σ p then
                        match place_resolved_write_target R p with
                        | Some x => Some [RStore x]
                        | None => None
                        end
                      else None
                    with
                    | Some roots =>
                        infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                    | None =>
                    match place_resolved_roots R p with
                    | Some roots =>
                        match singleton_store_root roots with
                        | Some root_x =>
                            match root_env_lookup root_x R with
                            | Some roots_x =>
                                match singleton_store_root roots_x with
                                | Some root_y =>
                                    if ident_eqb root_x root_y
                                    then infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                                    else
                                      match place_borrow_roots R p with
                                      | Some roots =>
                                          infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                                      | None => infer_err ErrContextCheckFailed
                                      end
                                | None =>
                                    match place_borrow_roots R p with
                                    | Some roots =>
                                        infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                                    | None => infer_err ErrContextCheckFailed
                                    end
                                end
                            | None =>
                                match place_borrow_roots R p with
                                | Some roots =>
                                    infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                                | None => infer_err ErrContextCheckFailed
                                end
                            end
                        | None =>
                            match place_borrow_roots R p with
                            | Some roots =>
                                infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                            | None => infer_err ErrContextCheckFailed
                            end
                        end
                    | None =>
                        match place_borrow_roots R p with
                        | Some roots =>
                            infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                        | None => infer_err ErrContextCheckFailed
                        end
                    end
                    end
                  else infer_err (ErrImmutableBorrow (place_name p))
              end
          end
      end
  | EDeref (EBorrow rk p) =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          if usage_eqb (ty_usage T_p) UUnrestricted
          then
            match place_path p with
            | Some (x, _) =>
                match root_env_lookup x R with
                | None => infer_err ErrContextCheckFailed
                | Some roots =>
                    match rk with
                    | RShared => infer_ok (T_p, Σ, R, roots)
                    | RUnique =>
                        match sctx_lookup_mut x Σ with
                        | Some MMutable => infer_ok (T_p, Σ, R, roots)
                        | Some MImmutable => infer_err (ErrImmutableBorrow x)
                        | None => infer_err (ErrUnknownVar x)
                        end
                    end
                end
            | None =>
                match place_root_lookup R p with
                | None => infer_err ErrContextCheckFailed
                | Some roots =>
                    match rk with
                    | RShared => infer_ok (T_p, Σ, R, roots)
                    | RUnique =>
                        if place_under_unique_ref_b env Σ p
                        then infer_ok (T_p, Σ, R, roots)
                        else infer_err (ErrImmutableBorrow (place_name p))
                    end
                end
            end
          else infer_err (ErrUsageMismatch (ty_usage T_p) UUnrestricted)
      end
  | EDeref _ => infer_err ErrNotImplemented
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1, R1, _) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then
            match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1 Σ1 e2 with
            | infer_err err => infer_err err
            | infer_ok (T2, Σ2, R2, roots2) =>
                match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1 Σ1 e3 with
                | infer_err err => infer_err err
                | infer_ok (T3, Σ3, R3, roots3) =>
                    if ty_core_eqb (ty_core T2) (ty_core T3)
                    then
                      if root_env_eqb R2 R3
                      then
                        match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                        | Some Γ4 =>
                            infer_ok
                              (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                               sctx_of_ctx Γ4, R2, root_set_union roots2 roots3)
                        | None => infer_err ErrContextCheckFailed
                        end
                      else infer_err ErrContextCheckFailed
                    else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                end
            end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECallExpr (EMakeClosure fname captures) args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
            match check_make_closure_captures_sctx_with_env env Ω Σ captures
                    (fn_captures fdef) with
            | infer_err err => infer_err err
            | infer_ok _ =>
                let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
                    : infer_result (list Ty * sctx * root_env * list root_set) :=
                  match as_ with
                  | [] => infer_ok ([], Σ0, R0, [])
                  | e' :: es =>
                      match infer_core_env_state_fuel_roots_shadow_safe
                              fuel' env Ω n R0 Σ0 e' with
                      | infer_err err => infer_err err
                      | infer_ok (T_e, Σ1, R1, roots_e) =>
                          match collect Σ1 R1 es with
                          | infer_err err => infer_err err
                          | infer_ok (tys, Σ2, R2, roots_es) =>
                              infer_ok
                                (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                          end
                      end
                  end
                in
                match collect Σ R args with
                | infer_err err => infer_err err
                | infer_ok (arg_tys, Σ', R', arg_roots) =>
                    match build_sigma (fn_lifetimes fdef)
                            (repeat None (fn_lifetimes fdef))
                            arg_tys (fn_params fdef) with
                    | None => infer_err ErrLifetimeConflict
                    | Some σ_acc =>
                        let σ := finalize_subst σ_acc in
                        let ps_subst := apply_lt_params σ (fn_params fdef) in
                        match check_args Ω arg_tys ps_subst with
                        | Some err => infer_err err
                        | None =>
                            if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                            then
                              let Ω_subst :=
                                apply_lt_outlives σ (fn_outlives fdef) in
                              if outlives_constraints_hold_b Ω Ω_subst
                              then infer_ok
                                (apply_lt_ty σ (fn_ret fdef), Σ', R',
                                  root_sets_union arg_roots)
                              else infer_err ErrHrtBoundUnsatisfied
                            else infer_err ErrLifetimeLeak
                        end
                    end
                end
            end
      end
  | ECallExpr (EFn _) _ => infer_err ErrNotImplemented
  | ECallExpr callee args =>
      (* General function-value call: check callee, collect args, match callee type. *)
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σ1, R1, roots_callee) =>
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ2, R2, roots_e) =>
                    match collect Σ2 R2 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ3, R3, roots_es) =>
                        infer_ok (T_e :: tys, Σ3, R3, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ1 R1 args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None =>
                      infer_ok (ret, Σ', R',
                        root_set_union roots_callee (root_sets_union arg_roots))
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None =>
                      infer_ok (ret, Σ', R',
                        root_set_union roots_callee (root_sets_union arg_roots))
                  end
              | TTypeForall type_params bounds body =>
                 match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                 | infer_err err => infer_err err
                 | infer_ok ret =>
                     infer_ok (ret, Σ', R',
                       root_set_union roots_callee (root_sets_union arg_roots))
                 end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret =>
                          infer_ok (ret, Σ', R',
                            root_set_union roots_callee (root_sets_union arg_roots))
                      end
                  | _ =>
                      match infer_hrt_call_env Ω n m bounds body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret =>
                          infer_ok (ret, Σ', R',
                            root_set_union roots_callee (root_sets_union arg_roots))
                      end
                  end
              | _ => infer_err ErrNotImplemented
              end
          end
      end
  | ECallExprGeneric callee type_args args =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σ1, R1, roots_callee) =>
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ2, R2, roots_e) =>
                    match collect Σ2 R2 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ3, R3, roots_es) =>
                        infer_ok (T_e :: tys, Σ3, R3, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ1 R1 args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match ty_core T_callee with
              | TTypeForall type_params bounds body =>
                  match ty_core body with
                  | TFn param_tys ret =>
                      match check_type_forall_bounds env bounds type_args with
                      | Some err => infer_err err
                      | None =>
                          match check_arg_tys Ω arg_tys
                                  (map (subst_type_params_ty type_args) param_tys) with
                          | Some err => infer_err err
                          | None => infer_ok
                              (subst_type_params_ty type_args ret, Σ', R',
                                root_set_union roots_callee
                                  (root_sets_union arg_roots))
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | _ => infer_err ErrNotImplemented
              end
          end
      end
  end
  end.

Fixpoint infer_core_env_state_fuel_roots_shadow_safe_checked (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_ok (T, Σ', R', roots) =>
      infer_ok (T, Σ', R', roots_for_checked_result env T roots)
  | infer_err err =>
      match fuel with
      | O => infer_err err
      | S fuel' =>
          match e with
          | ELet m x T e1 e2 =>
              match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
              | infer_err err1 => infer_err err1
              | infer_ok (T1, Σ1, R1, roots1) =>
                  if ty_compatible_b Ω T1 T
                  then
                    match root_env_lookup x R1 with
                    | Some _ => infer_err ErrContextCheckFailed
                    | None =>
                        if roots_exclude_b x roots1 && root_env_excludes_b x R1
                        then
                          match infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Ω n
                                  (root_env_add x roots1 R1) (sctx_add x T m Σ1) e2 with
                          | infer_err err2 => infer_err err2
                          | infer_ok (T2, Σ2, R2, roots2) =>
                              if sctx_check_ok env x T Σ2 &&
                                 capture_ref_free_ty_b env T2 &&
                                 root_env_excludes_b x (root_env_remove x R2)
                              then
                                infer_ok
                                  (T2, sctx_remove x Σ2, root_env_remove x R2,
                                   roots_for_checked_result env T2 roots2)
                              else infer_err ErrContextCheckFailed
                          end
                        else infer_err ErrContextCheckFailed
                    end
                  else infer_err (compatible_error T1 T)
              end
          | ELetInfer m x e1 e2 =>
              match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
              | infer_err err1 => infer_err err1
              | infer_ok (T1, Σ1, R1, roots1) =>
                  match root_env_lookup x R1 with
                  | Some _ => infer_err ErrContextCheckFailed
                  | None =>
                      if roots_exclude_b x roots1 && root_env_excludes_b x R1
                      then
                        match infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Ω n
                                (root_env_add x roots1 R1) (sctx_add x T1 m Σ1) e2 with
                        | infer_err err2 => infer_err err2
                        | infer_ok (T2, Σ2, R2, roots2) =>
                            if sctx_check_ok env x T1 Σ2 &&
                               capture_ref_free_ty_b env T2 &&
                               root_env_excludes_b x (root_env_remove x R2)
                            then
                              infer_ok
                                (T2, sctx_remove x Σ2, root_env_remove x R2,
                                 roots_for_checked_result env T2 roots2)
                            else infer_err ErrContextCheckFailed
                        end
                      else infer_err ErrContextCheckFailed
                  end
              end
          | _ => infer_err err
          end
      end
  end.

Definition infer_core_env_roots_shadow_safe
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots_shadow_safe 10000 env Ω n R (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ, R', roots) => infer_ok (T, ctx_of_sctx Σ, R', roots)
  | infer_err err => infer_err err
  end.

Definition infer_core_env_roots_shadow_safe_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots_shadow_safe_checked 10000 env Ω n R (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ, R', roots) => infer_ok (T, ctx_of_sctx Σ, R', roots)
  | infer_err err => infer_err err
  end.
