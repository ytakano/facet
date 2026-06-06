From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram CheckerExamplesBasic CheckerBorrow CheckerFull CheckerAlphaElabProgram CheckerRootSidecars CheckerExamplesRootSidecars.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Direct variant (no alpha renaming) — for differential testing only   *)
(* ------------------------------------------------------------------ *)

(* infer_direct skips alpha_rename_for_infer and calls infer_core directly.
   If the parser's de Bruijn indexing is correct, infer_direct fenv f and
   infer fenv f should always agree.  Run both at development time to
   validate that alpha renaming is indeed a no-op. *)
Definition infer_direct (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core fenv Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_b (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

(* ------------------------------------------------------------------ *)
(* Surface closure elaboration                                          *)
(* ------------------------------------------------------------------ *)

Inductive raw_expr : Type :=
| RawUnit : raw_expr
| RawLit : literal -> raw_expr
| RawVar : ident -> raw_expr
| RawFn : ident -> raw_expr
| RawPlace : place -> raw_expr
| RawLet : mutability -> ident -> Ty -> raw_expr -> raw_expr -> raw_expr
| RawLetInfer : mutability -> ident -> raw_expr -> raw_expr -> raw_expr
| RawCall : ident -> list raw_expr -> raw_expr
| RawCallGeneric : ident -> list Ty -> list raw_expr -> raw_expr
| RawCallExpr : raw_expr -> list raw_expr -> raw_expr
| RawStruct : string -> list lifetime -> list Ty -> list (string * raw_expr) -> raw_expr
| RawEnum : string -> string -> list lifetime -> list Ty -> list raw_expr -> raw_expr
| RawMatch : raw_expr -> list (string * list ident * raw_expr) -> raw_expr
| RawReplace : place -> raw_expr -> raw_expr
| RawAssign : place -> raw_expr -> raw_expr
| RawBorrow : ref_kind -> place -> raw_expr
| RawDeref : raw_expr -> raw_expr
| RawDrop : raw_expr -> raw_expr
| RawIf : raw_expr -> raw_expr -> raw_expr -> raw_expr
| RawClosure : list ident -> list param -> Ty -> raw_expr -> raw_expr
| RawCore : expr -> raw_expr.

Record raw_fn_def : Type := MkRawFnDef {
  raw_fn_name      : ident;
  raw_fn_lifetimes : nat;
  raw_fn_outlives  : outlives_ctx;
  raw_fn_params    : list param;
  raw_fn_ret       : Ty;
  raw_fn_body      : raw_expr;
  raw_fn_type_params : nat;
  raw_fn_bounds    : list trait_bound
}.

Definition fn_stub_of_raw (f : raw_fn_def) : fn_def :=
  MkFnDef (raw_fn_name f) (raw_fn_lifetimes f) (raw_fn_outlives f)
    [] (raw_fn_params f) (raw_fn_ret f) EUnit
    (raw_fn_type_params f) (raw_fn_bounds f).

Definition append_env_fns (env : global_env) (fns : list fn_def) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    (env_local_bounds env) (env_fns env ++ fns).

Fixpoint closure_elab_suffix (idx : nat) : string :=
  match idx with
  | O => EmptyString
  | S idx' => String.append "_"%string (closure_elab_suffix idx')
  end.

Definition closure_elab_name (idx : nat) : ident :=
  (String.append "__facet_closure"%string (closure_elab_suffix idx), 0).

Definition generic_fn_value_wrapper_name (idx : nat) : ident :=
  (String.append "__facet_generic_fn_value"%string (closure_elab_suffix idx), 0).

Fixpoint wrapper_params_from_tys_from
    (idx : nat) (tys : list Ty) : list param :=
  match tys with
  | [] => []
  | T :: rest =>
      MkParam MImmutable ("__facet_generic_arg"%string, idx) T ::
      wrapper_params_from_tys_from (S idx) rest
  end.

Definition wrapper_params_from_tys (tys : list Ty) : list param :=
  wrapper_params_from_tys_from 0 tys.

Fixpoint expr_vars_of_params (ps : list param) : list expr :=
  match ps with
  | [] => []
  | p :: rest => EVar (param_name p) :: expr_vars_of_params rest
  end.


Definition infer_fn_value_type_args_expected
    (fdef : fn_def) (expected : option Ty) : option (list Ty * list Ty * Ty) :=
  match expected with
  | Some (MkTy _ (TFn param_tys ret)) =>
      match infer_call_type_args_expected fdef param_tys (Some ret) with
      | Some type_args => Some (type_args, param_tys, ret)
      | None => None
      end
  | _ => None
  end.

Definition auto_drop_ret_name (idx : nat) : ident :=
  ("__facet_auto_drop_ret"%string, idx).

Definition auto_drop_tmp_name (idx : nat) : ident :=
  ("__facet_auto_drop"%string, idx).

Fixpoint place_of_path_from (base : place) (p : field_path) : place :=
  match p with
  | [] => base
  | field :: rest => place_of_path_from (PField base field) rest
  end.

Definition place_of_field_path (x : ident) (p : field_path) : place :=
  place_of_path_from (PVar x) p.

Fixpoint wrap_auto_drop_expr
    (x : ident) (paths : list field_path) (ret : expr) (next : nat)
    : expr * nat :=
  match paths with
  | [] => (ret, next)
  | path :: rest =>
      let tmp := auto_drop_tmp_name next in
      let '(tail, next') := wrap_auto_drop_expr x rest ret (S next) in
      (ELet MImmutable tmp (MkTy UUnrestricted TUnits)
        (EDrop (EPlace (place_of_field_path x path))) tail, next')
  end.

Definition wrap_let_body_auto_drops
    (env : global_env) (x : ident) (T : Ty) (Σ_body : sctx)
    (body_ty : Ty) (body : expr) (next : nat) : expr * nat :=
  match auto_drop_live_paths env x T Σ_body with
  | [] => (body, next)
  | paths =>
      let ret := auto_drop_ret_name next in
      let '(tail, next') := wrap_auto_drop_expr x paths (EVar ret) (S next) in
      (ELet MImmutable ret body_ty body tail, next')
  end.

Definition closure_elab_capture_param
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx) (x : ident)
    : infer_result param :=
  match sctx_lookup x Σ with
  | None => infer_err (ErrUnknownVar x)
  | Some (T, st) =>
      if negb (binding_available_b st [])
      then infer_err (ErrAlreadyConsumed x)
      else
      match sctx_lookup_mut x Σ with
      | Some MImmutable =>
          if usage_eqb (ty_usage T) UUnrestricted
          then
            if capture_ref_free_ty_b env T
            then infer_ok (MkParam MImmutable x T)
            else
              match T with
              | MkTy _ (TRef _ RShared _) => infer_ok (MkParam MImmutable x T)
              | _ => infer_err (ErrNotAReference (ty_core T))
              end
          else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
      | Some MMutable => infer_err (ErrNotMutable x)
      | None => infer_err (ErrUnknownVar x)
      end
  end.

Fixpoint closure_elab_capture_params
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx) (captures : list ident)
    : infer_result (list param) :=
  match captures with
  | [] => infer_ok []
  | x :: xs =>
      match closure_elab_capture_param env Ω Σ x with
      | infer_err err => infer_err err
      | infer_ok p =>
          match closure_elab_capture_params env Ω Σ xs with
          | infer_err err => infer_err err
          | infer_ok ps => infer_ok (p :: ps)
          end
      end
  end.

Definition infer_elaborated_expr_state
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (e : expr) : infer_result sctx :=
  match infer_core_env_state_fuel fuel env Ω n Σ e with
  | infer_err err => infer_err err
  | infer_ok (_, Σ') => infer_ok Σ'
  end.

Fixpoint elaborate_raw_expr_fuel
    (fuel : nat) (expected : option Ty)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (next : nat) (e : raw_expr)
    : infer_result (expr * sctx * list fn_def * nat) :=
  let finish env' e' extras next' :=
    match infer_elaborated_expr_state fuel env' Ω n Σ e' with
    | infer_err err => infer_err err
    | infer_ok Σ' => infer_ok (e', Σ', extras, next')
    end in
  let fix go_args fuel0 env0 Σ0 next0 args :=
    match args with
    | [] => infer_ok ([], Σ0, [], next0)
    | a :: rest =>
        match elaborate_raw_expr_fuel fuel0 None env0 Ω n Σ0 next0 a with
        | infer_err err => infer_err err
        | infer_ok (a', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_args fuel0 env1 Σ1 next1 rest with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok (a' :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    end in
  let fix go_args_expected fuel0 env0 Σ0 next0 args params :=
    match args, params with
    | [], [] => infer_ok ([], Σ0, [], next0)
    | a :: rest, p :: ps =>
        match elaborate_raw_expr_fuel fuel0 (Some (param_ty p)) env0 Ω n Σ0 next0 a with
        | infer_err err => infer_err err
        | infer_ok (a', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_args_expected fuel0 env1 Σ1 next1 rest ps with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok (a' :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    | _, _ => infer_err ErrArityMismatch
    end in
  let fix infer_arg_tys_state fuel0 env0 Σ0 args :=
    match args with
    | [] => infer_ok ([], Σ0)
    | a :: rest =>
        match infer_core_env_state_fuel fuel0 env0 Ω n Σ0 a with
        | infer_err err => infer_err err
        | infer_ok (T, Σ1) =>
            match infer_arg_tys_state fuel0 env0 Σ1 rest with
            | infer_err err => infer_err err
            | infer_ok (Ts, Σ2) => infer_ok (T :: Ts, Σ2)
            end
        end
    end in
  let fix go_fields fuel0 env0 Σ0 next0 fields :=
    match fields with
    | [] => infer_ok ([], Σ0, [], next0)
    | (fname, fe) :: rest =>
        match elaborate_raw_expr_fuel fuel0 None env0 Ω n Σ0 next0 fe with
        | infer_err err => infer_err err
        | infer_ok (fe', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_fields fuel0 env1 Σ1 next1 rest with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok ((fname, fe') :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    end in
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
      match e with
      | RawUnit => finish env EUnit [] next
      | RawLit lit => finish env (ELit lit) [] next
      | RawVar x => finish env (EVar x) [] next
      | RawFn fname =>
          match lookup_fn_b fname (env_fns env) with
          | None => finish env (EFn fname) [] next
          | Some fdef =>
              if Nat.eqb (fn_type_params fdef) 0
              then finish env (EFn fname) [] next
              else
                if negb (no_captures_b fdef)
                then infer_err ErrNotImplemented
                else
                  match expected with
                  | Some T_expected =>
                      if ty_compatible_b Ω (fn_value_ty fdef) T_expected
                      then finish env (EFn fname) [] next
                      else if negb (Nat.eqb (fn_lifetimes fdef) 0)
                      then infer_err ErrTypeArgInferenceFailed
                      else
                        match infer_fn_value_type_args_expected fdef expected with
                        | None => infer_err ErrTypeArgInferenceFailed
                        | Some (type_args, param_tys, ret) =>
                            match check_struct_bounds env (fn_bounds fdef) type_args with
                            | Some err => infer_err err
                            | None =>
                                let wrapper_name := generic_fn_value_wrapper_name next in
                                let wrapper_params := wrapper_params_from_tys param_tys in
                                let wrapper_body :=
                                  ECallGeneric fname type_args
                                    (expr_vars_of_params wrapper_params) in
                                let wrapper :=
                                  MkFnDef wrapper_name 0 [] [] wrapper_params ret
                                    wrapper_body 0 [] in
                                let env' := append_env_fns env [wrapper] in
                                finish env' (EFn wrapper_name) [wrapper] (S next)
                            end
                        end
                  | None => infer_err ErrTypeArgInferenceFailed
                  end
          end
      | RawPlace p => finish env (EPlace p) [] next
      | RawCore ecore => finish env ecore [] next
      | RawBorrow rk p => finish env (EBorrow rk p) [] next
      | RawLet m x T e1 e2 =>
          match elaborate_raw_expr_fuel fuel' (Some T) env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match elaborate_raw_expr_fuel fuel' expected env1 Ω n
                      (sctx_add x T m Σ1) next1 e2 with
              | infer_err err => infer_err err
              | infer_ok (e2', Σ2, extras2, next2) =>
                  let extras := extras1 ++ extras2 in
                  let env2 := append_env_fns env extras in
                  match infer_core_env_state_fuel fuel' env2 Ω n
                          (sctx_add x T m Σ1) e2' with
                  | infer_err err => infer_err err
                  | infer_ok (T2, _) =>
                      let '(e2'', next3) :=
                        wrap_let_body_auto_drops env2 x T Σ2 T2 e2' next2 in
                      let e' := ELet m x T e1' e2'' in
                      finish env2 e' extras next3
                  end
              end
          end
      | RawLetInfer m x e1 e2 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              match infer_core_env_state_fuel fuel' (append_env_fns env extras1)
                      Ω n Σ e1' with
              | infer_err err => infer_err err
              | infer_ok (T1, _) =>
                  let env1 := append_env_fns env extras1 in
                  match elaborate_raw_expr_fuel fuel' expected env1 Ω n
                          (sctx_add x T1 m Σ1) next1 e2 with
                  | infer_err err => infer_err err
                  | infer_ok (e2', Σ2, extras2, next2) =>
                      let extras := extras1 ++ extras2 in
                      let env2 := append_env_fns env extras in
                      match infer_core_env_state_fuel fuel' env2 Ω n
                              (sctx_add x T1 m Σ1) e2' with
                      | infer_err err => infer_err err
                      | infer_ok (T2, _) =>
                          let '(e2'', next3) :=
                            wrap_let_body_auto_drops env2 x T1 Σ2 T2 e2' next2 in
                          let e' := ELet m x T1 e1' e2'' in
                          finish env2 e' extras next3
                      end
                  end
              end
          end
      | RawCall fname args =>
          let infer_plain :=
            match go_args fuel' env Σ next args with
            | infer_err err => infer_err err
            | infer_ok (args', _, extras, next') =>
                let env' := append_env_fns env extras in
                match lookup_fn_b fname (env_fns env') with
                | None => finish env' (ECall fname args') extras next'
                | Some fdef =>
                    if Nat.eqb (fn_type_params fdef) 0
                    then finish env' (ECall fname args') extras next'
                    else
                      match infer_arg_tys_state fuel' env' Σ args' with
                      | infer_err err => infer_err err
                      | infer_ok (arg_tys, _) =>
                          match infer_call_type_args_expected fdef arg_tys expected with
                          | None => infer_err ErrTypeArgInferenceFailed
                          | Some type_args =>
                              match check_struct_bounds env' (fn_bounds fdef) type_args with
                              | Some err => infer_err err
                              | None =>
                                  match specialize_simple_generic_wrapper_call env' fname type_args args' with
                                  | Some (target, target_type_args, target_args) =>
                                      finish env'
                                        (ECallGeneric target target_type_args target_args)
                                        extras next'
                                  | None =>
                                      finish env' (ECallGeneric fname type_args args')
                                        extras next'
                                  end
                              end
                          end
                      end
                end
            end in
          match lookup_fn_b fname (env_fns env) with
          | Some fdef =>
	              if Nat.eqb (fn_type_params fdef) 0
              then
                match go_args_expected fuel' env Σ next args (fn_params fdef) with
                | infer_err _ => infer_plain
                | infer_ok (args', _, extras, next') =>
                    finish (append_env_fns env extras)
                      (ECall fname args') extras next'
                end
              else infer_plain
          | None => infer_plain
          end
      | RawCallGeneric fname type_args args =>
          match go_args fuel' env Σ next args with
          | infer_err err => infer_err err
          | infer_ok (args', _, extras, next') =>
              let env' := append_env_fns env extras in
              match specialize_simple_generic_wrapper_call env' fname type_args args' with
              | Some (target, target_type_args, target_args) =>
                  finish env' (ECallGeneric target target_type_args target_args)
                    extras next'
              | None =>
                  finish env' (ECallGeneric fname type_args args')
                    extras next'
              end
          end
      | RawCallExpr callee args =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next callee with
          | infer_err err => infer_err err
          | infer_ok (callee', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match go_args fuel' env1 Σ1 next1 args with
              | infer_err err => infer_err err
              | infer_ok (args', _, extras2, next2) =>
                  let extras := extras1 ++ extras2 in
                  finish (append_env_fns env extras)
                    (ECallExpr callee' args') extras next2
              end
          end
      | RawStruct sname lts tys fields =>
          match go_fields fuel' env Σ next fields with
          | infer_err err => infer_err err
          | infer_ok (fields', _, extras, next') =>
              finish (append_env_fns env extras)
                (EStruct sname lts tys fields') extras next'
          end
      | RawEnum enum_name variant_name lts tys payloads =>
          match go_args fuel' env Σ next payloads with
          | infer_err err => infer_err err
          | infer_ok (payloads', _, extras, next') =>
              finish (append_env_fns env extras)
                (EEnum enum_name variant_name lts tys payloads') extras next'
          end
      | RawMatch scrut branches =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next scrut with
          | infer_err err => infer_err err
          | infer_ok (scrut', Σ1, extras_scrut, next1) =>
              let env1 := append_env_fns env extras_scrut in
              match infer_core_env_state_fuel fuel' env1 Ω n Σ scrut' with
              | infer_err err => infer_err err
              | infer_ok (T_scrut, _) =>
                  match ty_core T_scrut with
                  | TEnum enum_name lts args =>
                      match lookup_enum enum_name env1 with
                      | None => infer_err (ErrEnumNotFound enum_name)
                      | Some edef =>
                          let fix go_branches env0 next0 branches0 :=
                            match branches0 with
                            | [] => infer_ok ([], [], next0)
                            | (variant_name, binders, e_branch) :: rest =>
                                match lookup_enum_variant variant_name (enum_variants edef) with
	                                | None => infer_err (ErrVariantNotFound variant_name)
	                                | Some vdef =>
	                                    match match_payload_params binders lts args vdef with
                                    | infer_err err => infer_err err
                                    | infer_ok ps =>
                                        if params_names_nodup_b ps &&
                                           ctx_lookup_params_none_b ps Σ1
                                        then
                                        match elaborate_raw_expr_fuel fuel' expected env0 Ω n
                                                (sctx_add_params ps Σ1) next0 e_branch with
                                        | infer_err err => infer_err err
                                        | infer_ok (e_branch', _, extras_branch, next_branch) =>
                                            let env_branch := append_env_fns env0 extras_branch in
                                            match go_branches env_branch next_branch rest with
                                            | infer_err err => infer_err err
                                            | infer_ok (rest', extras_rest, next_rest) =>
                                                infer_ok ((variant_name, binders, e_branch') :: rest',
                                                          extras_branch ++ extras_rest, next_rest)
                                            end
                                        end
	                                        else infer_err ErrContextCheckFailed
	                                    end
	                                end
                            end
                          in
                          match go_branches env1 next1 branches with
                          | infer_err err => infer_err err
                          | infer_ok (branches', extras_branches, next') =>
                              let extras := extras_scrut ++ extras_branches in
                              let env' := append_env_fns env extras in
                              match infer_core_env_state_fuel_elab fuel env' Ω n Σ
                                      (EMatch scrut' branches') with
                              | infer_err err => infer_err err
                              | infer_ok (_, Σ', e_match') =>
                                  infer_ok (e_match', Σ', extras, next')
                              end
                          end
                      end
                  | c => infer_err (ErrNotAnEnum c)
                  end
              end
          end
      | RawReplace p e1 =>
          let expected_rhs :=
            match infer_place_sctx env Σ p with
            | infer_ok T => Some T
            | infer_err _ => None
            end in
          match elaborate_raw_expr_fuel fuel' expected_rhs env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EReplace p e1') extras next'
          end
      | RawAssign p e1 =>
          let expected_rhs :=
            match infer_place_sctx env Σ p with
            | infer_ok T => Some T
            | infer_err _ => None
            end in
          match elaborate_raw_expr_fuel fuel' expected_rhs env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EAssign p e1') extras next'
          end
      | RawDeref e1 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EDeref e1') extras next'
          end
      | RawDrop e1 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EDrop e1') extras next'
          end
      | RawIf e1 e2 e3 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match elaborate_raw_expr_fuel fuel' expected env1 Ω n Σ1 next1 e2 with
              | infer_err err => infer_err err
              | infer_ok (e2', _, extras2, next2) =>
                  let env2 := append_env_fns env1 extras2 in
                  match elaborate_raw_expr_fuel fuel' expected env2 Ω n Σ1 next2 e3 with
                  | infer_err err => infer_err err
                  | infer_ok (e3', _, extras3, next3) =>
                      let extras := extras1 ++ extras2 ++ extras3 in
                      finish (append_env_fns env extras)
                        (EIf e1' e2' e3') extras next3
                  end
              end
          end
      | RawClosure captures params ret body =>
          match closure_elab_capture_params env Ω Σ captures with
          | infer_err err => infer_err err
          | infer_ok cap_params =>
              let fname := closure_elab_name next in
              let body_ctx := sctx_of_ctx (params_ctx (cap_params ++ params)) in
              match elaborate_raw_expr_fuel fuel' (Some ret) env Ω n body_ctx (S next) body with
              | infer_err err => infer_err err
              | infer_ok (body', _, body_extras, next') =>
                  let fdef := MkFnDef fname n Ω cap_params params ret body' 0 [] in
                  let env_with_closure := append_env_fns env (body_extras ++ [fdef]) in
                  match infer_full_env env_with_closure fdef with
                  | infer_err err => infer_err err
                  | infer_ok _ =>
                      finish env_with_closure (EMakeClosure fname captures)
                        (body_extras ++ [fdef]) next'
                  end
              end
          end
      end
  end.

Definition elaborate_raw_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx)
    (e : raw_expr) : infer_result (expr * list fn_def) :=
  match elaborate_raw_expr_fuel 10000 None env Ω n Σ 0 e with
  | infer_err err => infer_err err
  | infer_ok (e', _, extras, _) => infer_ok (e', extras)
  end.

Definition raw_fn_body_ctx (f : raw_fn_def) : ctx :=
  params_ctx (raw_fn_params f).

Fixpoint elaborate_raw_fns_fuel
    (fuel : nat) (base_env : global_env) (done : list fn_def)
    (next : nat) (fs : list raw_fn_def)
    : infer_result (list fn_def * nat) :=
  match fs with
  | [] => infer_ok ([], next)
  | f :: rest =>
      let env0 := append_env_fns base_env done in
      let body_env := global_env_with_local_bounds env0 (raw_fn_bounds f) in
      match elaborate_raw_expr_fuel fuel (Some (raw_fn_ret f))
              body_env (raw_fn_outlives f)
              (raw_fn_lifetimes f) (sctx_of_ctx (raw_fn_body_ctx f))
              next (raw_fn_body f) with
      | infer_err err => infer_err err
      | infer_ok (body', _, extras, next1) =>
          let f' := MkFnDef (raw_fn_name f) (raw_fn_lifetimes f)
                      (raw_fn_outlives f) [] (raw_fn_params f)
                      (raw_fn_ret f) body'
                      (raw_fn_type_params f) (raw_fn_bounds f) in
          match elaborate_raw_fns_fuel fuel base_env (done ++ extras ++ [f'])
                  next1 rest with
          | infer_err err => infer_err err
          | infer_ok (rest', next2) => infer_ok (extras ++ f' :: rest', next2)
          end
      end
  end.

Definition elaborate_raw_global_env (env : global_env) (fs : list raw_fn_def)
    : infer_result global_env :=
  let stubs := map fn_stub_of_raw fs in
  let base := MkGlobalEnv (env_structs env) (env_enums env)
    (env_traits env) (env_impls env)
    [] stubs in
  match elaborate_raw_fns_fuel 10000 base [] 0 fs with
  | infer_err err => infer_err err
  | infer_ok (fns, _) =>
      infer_ok (MkGlobalEnv (env_structs env) (env_enums env)
        (env_traits env) (env_impls env) [] fns)
  end.
