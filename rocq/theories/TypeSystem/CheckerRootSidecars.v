From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram CheckerExamplesBasic CheckerBorrow CheckerFull CheckerAlphaElabProgram.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Lemma lookup_fn_b_sound_sidecar : forall fname fenv fdef,
  lookup_fn_b fname fenv = Some fdef ->
  In fdef fenv /\ fn_name fdef = fname.
Proof.
  intros fname fenv.
  induction fenv as [| f fs IH]; intros fdef Hlookup.
  - discriminate.
  - simpl in Hlookup.
    destruct (ident_eqb fname (fn_name f)) eqn:Hname.
    + injection Hlookup as <-.
      apply ident_eqb_eq in Hname.
      split; [left; reflexivity | symmetry; exact Hname].
    + destruct (IH fdef Hlookup) as [Hin Hfn].
      split; [right; exact Hin | exact Hfn].
Qed.

Definition fn_params_roots_exclude_b (ps : list param) (roots : root_set) : bool :=
  forallb (fun x => roots_exclude_b x roots) (ctx_names (params_ctx ps)).

Definition fn_params_root_env_excludes_b (ps : list param) (R : root_env) : bool :=
  forallb (fun x => root_env_excludes_b x R) (ctx_names (params_ctx ps)).

Definition check_fn_root_shadow_summary (env : global_env) (fdef : fn_def) : bool :=
  preservation_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | infer_err _ => false
  end.

Definition check_env_root_shadow_summary (env : global_env) : bool :=
  forallb (check_fn_root_shadow_summary env) (env_fns env).

Definition check_fn_root_shadow_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  provenance_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | infer_err _ => false
  end.

Definition check_env_root_shadow_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_provenance_summary env) (env_fns env).

Fixpoint store_safe_function_value_call_args_b
    (env : global_env) (args : list expr) : bool :=
  match args with
  | [] => true
  | EUnit :: rest =>
      store_safe_function_value_call_args_b env rest
  | ELit _ :: rest =>
      store_safe_function_value_call_args_b env rest
  | EVar _ :: rest =>
      store_safe_function_value_call_args_b env rest
  | EFn fname :: rest =>
      match lookup_fn_b fname (env_fns env) with
      | Some callee =>
          check_fn_root_shadow_provenance_summary env callee &&
          store_safe_function_value_call_args_b env rest
      | None => false
      end
  | EStruct name lts tys [] :: rest =>
      match lookup_struct name env with
      | Some sdef =>
          match struct_bounds sdef with
          | [] =>
              capture_ref_free_ty_b env
                (MkTy UUnrestricted (TStruct name lts tys)) &&
              store_safe_function_value_call_args_b env rest
          | _ :: _ => false
          end
      | None => false
      end
  | EEnum name variant _ _ _ [] :: rest =>
      match lookup_enum name env with
      | Some edef =>
          match enum_bounds edef with
          | [] =>
              match lookup_enum_variant variant (enum_variants edef) with
              | Some vdef =>
                  match enum_variant_fields vdef with
                  | [] => store_safe_function_value_call_args_b env rest
                  | _ :: _ => false
                  end
              | None => false
              end
          | _ :: _ => false
          end
      | None => false
      end
  | _ :: _ => false
  end.

Definition direct_call_target_expr (e : expr) : option (ident * list expr * expr) :=
  match e with
  | ECall fname args => Some (fname, args, ECall fname args)
  | ECallExpr (EFn fname) args => Some (fname, args, ECall fname args)
  | _ => None
  end.

Definition generic_direct_call_target_expr
    (e : expr) : option (ident * list Ty * list expr * expr) :=
  match e with
  | ECallGeneric fname type_args args =>
      Some (fname, type_args, args, ECallGeneric fname type_args args)
  | _ => None
  end.

Definition let_bound_generic_direct_call_target_expr
    (e : expr) : option (ident * list Ty * list expr * Ty * expr) :=
  match e with
  | ELet m x T_hidden (ECallGeneric fname type_args args) (EVar y) =>
      if ident_eqb x y
      then Some
        (fname, type_args, args, T_hidden,
          ELet m x T_hidden (ECallGeneric fname type_args args) (EVar y))
      else None
  | _ => None
  end.

Definition direct_call_receiver_method_target_expr
    (e : expr) : option (ident * list Ty * ident * list expr * list expr * expr) :=
  match e with
  | ECallGeneric method_name type_args
      (ECall receiver_name receiver_args :: method_args) =>
      Some (method_name, type_args, receiver_name, receiver_args, method_args,
        ECallGeneric method_name type_args
          (ECall receiver_name receiver_args :: method_args))
  | ECallGeneric method_name type_args
      (ECallExpr (EFn receiver_name) receiver_args :: method_args) =>
      Some (method_name, type_args, receiver_name, receiver_args, method_args,
        ECallGeneric method_name type_args
          (ECall receiver_name receiver_args :: method_args))
  | _ => None
  end.

Definition receiver_method_hidden_receiver_name : ident :=
  ("__facet_method_receiver"%string, 0).

Definition direct_call_receiver_method_hidden_let_synthetic_body
    (T_receiver : Ty) (method_name : ident) (type_args : list Ty)
    (receiver_name : ident) (receiver_args method_args : list expr) : expr :=
  ELet MImmutable receiver_method_hidden_receiver_name T_receiver
    (ECall receiver_name receiver_args)
    (ECallGeneric method_name type_args
      (EVar receiver_method_hidden_receiver_name :: method_args)).

Definition generic_direct_call_receiver_method_hidden_let_synthetic_body
    (T_receiver : Ty) (method_name : ident) (type_args : list Ty)
    (receiver_name : ident) (receiver_type_args : list Ty)
    (receiver_args method_args : list expr) : expr :=
  ELet MImmutable receiver_method_hidden_receiver_name T_receiver
    (ECallGeneric receiver_name receiver_type_args receiver_args)
    (ECallGeneric method_name type_args
      (EVar receiver_method_hidden_receiver_name :: method_args)).

Definition generic_direct_call_receiver_method_target_expr
    (e : expr)
    : option (ident * list Ty * ident * list Ty * list expr * list expr * expr) :=
  match e with
  | ECallGeneric method_name type_args
      (ECallGeneric receiver_name receiver_type_args receiver_args :: method_args) =>
      Some (method_name, type_args, receiver_name, receiver_type_args,
        receiver_args, method_args,
        ECallGeneric method_name type_args
          (ECallGeneric receiver_name receiver_type_args receiver_args ::
            method_args))
  | _ => None
  end.

Definition if_literal_generic_direct_call_target_expr
    (e : expr)
    : option (bool * ident * list Ty * list expr *
              ident * list Ty * list expr * expr) :=
  match e with
  | EIf (ELit (LBool b))
      (ECallGeneric fname_then type_args_then args_then)
      (ECallGeneric fname_else type_args_else args_else) =>
      if ident_eqb fname_then fname_else &&
         ty_list_eqb type_args_then type_args_else
      then
        match args_then, args_else with
        | [], [] => Some (b, fname_then, type_args_then, args_then,
            fname_else, type_args_else, args_else,
            EIf (ELit (LBool b))
              (ECallGeneric fname_then type_args_then args_then)
              (ECallGeneric fname_else type_args_else args_else))
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition direct_call_ready_expr_b (e : expr) : bool :=
  match direct_call_target_expr e with
  | Some (_, args, _) => preservation_ready_args_b args
  | None => false
  end.

Definition check_fn_root_shadow_direct_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_provenance_summary env fdef with
  | true => true
  | false =>
      match direct_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          end
      | None => false
      end
  end.

Definition local_fn_value_call_target_expr
    (e : expr) : option (ident * list expr * expr) :=
  match e with
  | ELet m x T (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted
      then Some (fname, args, ELet m x T (EFn fname) (ECall fname args))
      else None
  | ELetInfer m x (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y
      then Some (fname, args, ELetInfer m x (EFn fname) (ECall fname args))
      else None
  | _ => None
  end.

Definition local_fn_value_call_target_expr_with_binder
    (e : expr) : option (ident * ident * list expr * expr) :=
  match e with
  | ELet m x T (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted
      then Some (x, fname, args, ELet m x T (EFn fname) (ECall fname args))
      else None
  | ELetInfer m x (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y
      then Some (x, fname, args, ELetInfer m x (EFn fname) (ECall fname args))
      else None
  | _ => None
  end.

Definition supported_non_type_generic_function_value_call_callee_ty_b
    (T : Ty) : bool :=
  match ty_core T with
  | TFn _ _ => true
  | TForall _ _ body =>
      match ty_core body with
      | TFn _ _ => true
      | _ => false
      end
  | _ => false
  end.

Definition supported_type_generic_function_value_call_callee_ty_b
    (T : Ty) : bool :=
  match ty_core T with
  | TTypeForall _ bounds body =>
      match bounds with
      | [] =>
          match ty_core body with
          | TFn _ _ => true
          | _ => false
          end
      | _ :: _ => false
      end
  | _ => false
  end.

Definition type_arg_no_lifetime_forall_b (T : Ty) : bool :=
  match ty_core T with
  | TForall _ _ _ => false
  | _ => true
  end.

Definition type_args_no_lifetime_forall_b (type_args : list Ty) : bool :=
  forallb type_arg_no_lifetime_forall_b type_args.

Definition type_args_lbound_free_b (type_args : list Ty) : bool :=
  forallb (fun T => negb (contains_lbound_ty T)) type_args.

Definition check_supported_non_type_generic_function_value_call_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (callee : expr) : bool :=
  match callee with
  | EVar _ =>
      match infer_core_env_roots_shadow_safe env Ω n R Γ callee with
      | infer_ok (T_callee, _, _, _) =>
          supported_non_type_generic_function_value_call_callee_ty_b T_callee
      | infer_err _ => false
      end
  | _ => false
  end.

Definition check_supported_type_generic_function_value_call_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (callee : expr)
    (type_args : list Ty) : bool :=
  type_args_lbound_free_b type_args &&
  type_args_no_lifetime_forall_b type_args &&
  match callee with
  | EVar _ =>
      match infer_core_env_roots_shadow_safe env Ω n R Γ callee with
      | infer_ok (T_callee, _, _, _) =>
          match ty_core T_callee with
          | TTypeForall type_params bounds body =>
              Nat.eqb (Datatypes.length type_args) type_params &&
              match bounds with
              | [] =>
                  match ty_core body with
                  | TFn _ _ => true
                  | _ => false
                  end
              | _ :: _ => false
              end
          | _ => false
          end
      | infer_err _ => false
      end
  | _ => false
  end.

Definition check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
    (check_expr : nat -> global_env -> outlives_ctx -> nat ->
      root_env -> sctx -> expr -> bool)
    (fuel : nat) (env : global_env) (fdef : fn_def)
    (type_args : list Ty) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      let body_ctx := subst_type_params_ctx type_args (fn_body_ctx fdef) in
      let body := subst_type_params_expr type_args (fn_body fdef) in
      let params := apply_type_params type_args (fn_params fdef) in
      let body_env :=
        global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)) in
      match infer_env_roots_shadow_safe env fdef
              (initial_root_env_for_fn fdef) with
      | infer_err _ => false
      | infer_ok _ =>
          match infer_core_env_state_fuel_roots_shadow_safe fuel' body_env
                   (fn_outlives fdef)
                   (fn_lifetimes fdef)
                   (initial_root_env_for_fn fdef)
                   (sctx_of_ctx body_ctx) body with
          | infer_ok (T_body, _, R_body, roots_body) =>
              check_expr fuel' body_env (fn_outlives fdef) (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef) (sctx_of_ctx body_ctx) body &&
              ty_compatible_b (fn_outlives fdef) T_body
                (subst_type_params_ty type_args (fn_ret fdef)) &&
              fn_params_roots_exclude_b params roots_body &&
              fn_params_root_env_excludes_b params R_body
          | infer_err _ => false
          end
      end
  end.

Definition check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (check_expr : nat -> global_env -> outlives_ctx -> nat ->
      root_env -> sctx -> expr -> bool)
    (fuel : nat) (env : global_env) (type_args : list Ty) : bool :=
  forallb
    (fun fdef =>
      if Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
      then
        check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
          check_expr fuel env fdef type_args
      else true)
    (env_fns env).

Definition check_fn_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_direct_call_provenance_summary env fdef with
  | true => true
  | false =>
      match local_fn_value_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          end
      | None =>
          match fn_body fdef with
          | ECallExpr callee args =>
              preservation_ready_expr_b callee &&
              preservation_ready_args_b args &&
              check_supported_non_type_generic_function_value_call_expr
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef)
                (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef)
                (fn_body_ctx fdef)
                callee &&
              match infer_env_roots_shadow_safe env fdef
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          | _ => false
          end
      end
  end.

Definition captured_call_target_expr
    (e : expr) : option (ident * list ident * list expr) :=
  match e with
  | ECallExpr (EMakeClosure fname captures) args =>
      Some (fname, captures, args)
  | _ => None
  end.

Definition args_free_vars_checker (args : list expr) : list ident :=
  args_local_store_names_with free_vars_expr args.

Definition local_captured_call_target_expr
    (e : expr)
    : option (ident * list ident * list expr * mutability * ident * Ty *
        expr * expr) :=
  match e with
  | ELet m x T (EMakeClosure fname captures) (ECallExpr (EVar y) args) =>
      if ident_eqb x y &&
         usage_eqb (ty_usage T) UUnrestricted &&
         negb (existsb (ident_eqb x) captures) &&
         negb (existsb (ident_eqb x) (args_free_vars_checker args)) &&
         negb (existsb (ident_eqb x) (args_local_store_names args))
      then
        let direct_body := ECallExpr (EMakeClosure fname captures) args in
        Some (fname, captures, args, m, x, T, direct_body,
          ELet m x T (EMakeClosure fname captures) direct_body)
      else None
  | _ => None
  end.

Definition check_fn_root_shadow_captured_callee_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  provenance_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef
          (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef)) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef ++ fn_captures fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef ++ fn_captures fdef) R_out
  | infer_err _ => false
  end.

Fixpoint capture_root_bound
    (R : root_env) (captures : list ident) (caps : list param)
    : option root_set :=
  match captures, caps with
  | [], [] => Some []
  | x :: captures', _ :: caps' =>
      match root_env_lookup x R, capture_root_bound R captures' caps' with
      | Some roots, Some rest => Some (root_set_union roots rest)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition callee_hidden_capture_args_disjoint_b
    (callee : fn_def) (args : list expr) : bool :=
  forallb
    (fun x =>
       negb (existsb (ident_eqb x) (args_local_store_names args)))
    (ctx_names (params_ctx (fn_captures callee))).

Fixpoint check_expr_root_shadow_captured_call_provenance_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      provenance_ready_expr_b e ||
      match direct_call_target_expr e with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel env Ω n R Σ synthetic_body with
              | infer_ok _ => true
              | infer_err _ => false
              end
          end
      | None => false
      end ||
      match captured_call_target_expr e with
      | Some (fname, captures, args) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              match check_make_closure_captures_exact_sctx_with_env env
                      Ω Σ captures (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  match capture_root_bound R captures (fn_captures callee) with
                  | Some _ =>
                      check_fn_root_shadow_captured_callee_provenance_summary
                        env callee
                  | None => false
                  end
              end
          end
      | None => false
      end ||
      match local_captured_call_target_expr e with
      | Some (fname, captures, args, m, x, T_hidden, direct_body, let_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              negb (existsb (ident_eqb x)
                (ctx_names (params_ctx (fn_captures callee)))) &&
              match root_env_lookup x R with
              | Some _ => false
              | None =>
                  match check_make_closure_captures_exact_sctx_with_env env
                          Ω Σ captures (fn_captures callee) with
                  | infer_err _ => false
                  | infer_ok _ =>
                      match capture_root_bound R captures
                              (fn_captures callee) with
                      | None => false
                      | Some _ =>
                          check_fn_root_shadow_captured_callee_provenance_summary
                            env callee &&
                          match
                            infer_core_env_state_fuel_roots_shadow_safe
                              fuel env Ω n R Σ direct_body,
                            infer_core_env_state_fuel_roots_shadow_safe
                              fuel env Ω n R Σ e
                          with
	                          | infer_ok (T_direct, Σ_direct, R_direct, _),
	                            infer_ok (T_let, Σ_let, R_let, _) =>
	                              sctx_eqb Σ_direct Σ_let &&
	                              root_env_eqb R_direct R_let &&
	                              ty_compatible_b Ω T_direct T_let
                          | _, _ => false
                          end
                      end
                  end
              end
          end
      | None => false
      end ||
      match e with
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              provenance_ready_expr_b e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      capture_ref_free_ty_b env T2 &&
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_captured_call_provenance_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | _ => false
      end ||
      match e with
      | EIf e1 e2 e3 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T_cond, Σ1, R1, _) =>
              ty_core_eqb (ty_core T_cond) TBooleans &&
              provenance_ready_expr_b e1 &&
              check_expr_root_shadow_captured_call_provenance_summary_fuel
                fuel' env Ω n R1 Σ1 e2 &&
              check_expr_root_shadow_captured_call_provenance_summary_fuel
                fuel' env Ω n R1 Σ1 e3
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_captured_call_provenance_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_captured_call_provenance_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint non_function_value_ty_b (T : Ty) : bool :=
  match T with
  | MkTy _ (TFn _ _) => false
  | MkTy _ (TClosure _ _ _) => false
  | MkTy _ (TForall _ _ body) => non_function_value_ty_b body
  | MkTy _ (TTypeForall _ _ body) => non_function_value_ty_b body
  | _ => true
  end.

Fixpoint check_expr_root_shadow_store_safe_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      check_expr_root_shadow_captured_call_provenance_summary_fuel
        fuel env Ω n R Σ e ||
      match e with
      | ECallExpr callee args =>
          preservation_ready_args_b args &&
          check_supported_non_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee
      | _ => false
      end ||
      match e with
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      capture_ref_free_ty_b env T2 &&
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | _ => false
      end ||
      match e with
      | EIf e1 e2 e3 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T_cond, Σ1, R1, _) =>
              ty_core_eqb (ty_core T_cond) TBooleans &&
              provenance_ready_expr_b e1 &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R1 Σ1 e2 &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R1 Σ1 e3
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_store_safe_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint check_expr_root_shadow_store_safe_narrow_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok (T, Σ', R', roots) =>
      match e with
      | EUnit => true
      | EStruct name _ _ [] =>
          match lookup_struct name env with
          | Some sdef =>
              match struct_bounds sdef with
              | [] => capture_ref_free_ty_b env T
              | _ :: _ => false
              end
          | None => false
          end
      | EVar _ => non_function_value_ty_b T
      | EAssign _ (ELit _) => true
      | EAssign (PVar x) (ECallGeneric fname type_args []) =>
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              match fn_bounds callee with
              | [] =>
                  match fn_params callee with
                  | [] =>
                      Nat.eqb (Datatypes.length type_args) (fn_type_params callee) &&
                      let body_ctx :=
                        subst_type_params_ctx type_args (fn_body_ctx callee) in
                      let body :=
                        subst_type_params_expr type_args (fn_body callee) in
                      match body_ctx with
                      | [] =>
                      match body with
                      | EStruct _ _ _ [] =>
                          let params := apply_type_params type_args (fn_params callee) in
                          match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env (fn_outlives callee)
                                  (fn_lifetimes callee)
                                  (initial_root_env_for_fn callee)
                                  (sctx_of_ctx body_ctx) body,
                                infer_env_roots_shadow_safe env callee
                                  (initial_root_env_for_fn callee),
                                infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env Ω n R Σ
                                  (ECallGeneric fname type_args []),
                                infer_place_sctx env Σ (PVar x) with
                          | infer_ok (T_body, _, R_body, roots_body),
                            infer_ok _,
                            infer_ok (T_rhs, _, _, _),
                            infer_ok T_old =>
                              check_expr_root_shadow_store_safe_narrow_summary_fuel
                                fuel' env (fn_outlives callee)
                                (fn_lifetimes callee)
                                (initial_root_env_for_fn callee)
                                (sctx_of_ctx body_ctx) body &&
                              ty_compatible_b (fn_outlives callee) T_body
                                (subst_type_params_ty type_args (fn_ret callee)) &&
                              fn_params_roots_exclude_b params roots_body &&
                              fn_params_root_env_excludes_b params R_body &&
                              ty_compatible_b Ω T_rhs T_old
                          | _, _, _, _ => false
                          end
                      | _ => false
                      end
                      | _ :: _ => false
                      end
                  | _ :: _ => false
                  end
              | _ :: _ => false
              end
          end
      | EAssign _ _ => false
      | EDrop (EPlace p) =>
          match place_path p with
          | Some _ => true
          | None => false
          end
      | EDrop _ => false
      | EBorrow rk p =>
          match place_path p with
          | Some _ => true
          | None =>
              match rk with
              | RShared => false
              | RUnique =>
                  place_resolved_write_writable_chain_b env R Σ p &&
                  match place_resolved_write_target R p with
                  | Some root_x =>
                      match singleton_store_root roots with
                      | Some root_y => ident_eqb root_x root_y
                      | None => false
                      end
                  | None => false
                  end
              end
          end
      | ECallExpr callee args =>
          store_safe_function_value_call_args_b env args &&
          check_supported_non_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee
      | ECallExprGeneric callee type_args args =>
          store_safe_function_value_call_args_b env args &&
          check_supported_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee type_args &&
          check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
            check_expr_root_shadow_store_safe_narrow_summary_fuel
            (S fuel') env type_args
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              non_function_value_ty_b T_hidden &&
              check_expr_root_shadow_store_safe_narrow_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_narrow_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | ELetInfer m x e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              non_function_value_ty_b T1 &&
              check_expr_root_shadow_store_safe_narrow_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T1 m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      sctx_check_ok env x T1 Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_narrow_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T1 m Σ1) e2
                  end
              end
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_store_safe_narrow_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_narrow_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (fuel : nat) (env : global_env) (fdef : fn_def)
    (type_args : list Ty) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      let body_ctx := subst_type_params_ctx type_args (fn_body_ctx fdef) in
      let body := subst_type_params_expr type_args (fn_body fdef) in
      let params := apply_type_params type_args (fn_params fdef) in
      let body_env :=
        global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)) in
      match infer_env_roots_shadow_safe env fdef
              (initial_root_env_for_fn fdef) with
      | infer_err _ => false
      | infer_ok _ =>
          check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
            check_expr_root_shadow_store_safe_narrow_summary_fuel
            (S fuel') env fdef type_args ||
          match generic_direct_call_target_expr body with
          | Some (fname, nested_type_args, args, synthetic_body) =>
              store_safe_function_value_call_args_b env args &&
              match lookup_fn_b fname (env_fns env) with
              | None => false
              | Some fcallee =>
                  Nat.eqb (Datatypes.length nested_type_args)
                    (fn_type_params fcallee) &&
                  match check_struct_bounds body_env (fn_bounds fcallee)
                          nested_type_args with
                  | Some _ => false
                  | None =>
                      match infer_core_env_roots_shadow_safe body_env
                              (fn_outlives fdef) (fn_lifetimes fdef)
                              (initial_root_env_for_fn fdef) body_ctx
                              synthetic_body with
                      | infer_ok (T_synth, _, R_synth, roots_synth) =>
                          check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
                            fuel' env fcallee nested_type_args &&
                          ty_compatible_b (fn_outlives fdef) T_synth
                            (subst_type_params_ty type_args (fn_ret fdef)) &&
                          fn_params_roots_exclude_b params roots_synth &&
                          fn_params_root_env_excludes_b params R_synth
                      | infer_err _ => false
                      end
                  end
              end
          | None => false
          end
      end
  end.

Definition check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
    (env : global_env) (fdef : fn_def) (type_args : list Ty) : bool :=
  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    10000 env fdef type_args.

Fixpoint check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match check_expr_root_shadow_store_safe_narrow_summary_fuel
          fuel env Ω n R Σ e with
  | true => true
  | false =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
      | infer_ok (T, _, _, _) =>
          match e with
          | EDeref (EBorrow RShared _) => capture_ref_free_ty_b env T
          | EStruct _ _ _ [] => capture_ref_free_ty_b env T
          | ELet m x T_hidden e1 e2 =>
              match fuel with
              | 0 => false
              | S fuel' =>
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n R Σ e1 with
                  | infer_err _ => false
                  | infer_ok (T1, Σ1, R1, roots1) =>
                      ty_compatible_b Ω T1 T_hidden &&
                      non_function_value_ty_b T_hidden &&
                      (check_expr_root_shadow_store_safe_narrow_summary_fuel
                         fuel' env Ω n R Σ e1 ||
                       (capture_ref_free_ty_b env T1 &&
                        check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                          fuel' env Ω n R Σ e1)) &&
                      match root_env_lookup x R1 with
                      | Some _ => false
                      | None =>
                          roots_exclude_b x roots1 &&
                          root_env_excludes_b x R1 &&
                          match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env Ω n
                                  (root_env_add x roots1 R1)
                                  (sctx_add x T_hidden m Σ1) e2 with
                          | infer_err _ => false
                          | infer_ok (T2, Σ2, R2, _) =>
                              sctx_check_ok env x T_hidden Σ2 &&
                              capture_ref_free_ty_b env T2 &&
                              root_env_excludes_b x (root_env_remove x R2) &&
                              check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env Ω n
                                (root_env_add x roots1 R1)
                                (sctx_add x T_hidden m Σ1) e2
                          end
                      end
                  end
              end
          | ELetInfer m x e1 e2 =>
              match fuel with
              | 0 => false
              | S fuel' =>
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n R Σ e1 with
                  | infer_err _ => false
                  | infer_ok (T1, Σ1, R1, roots1) =>
                      non_function_value_ty_b T1 &&
                      (check_expr_root_shadow_store_safe_narrow_summary_fuel
                         fuel' env Ω n R Σ e1 ||
                       (capture_ref_free_ty_b env T1 &&
                        check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                          fuel' env Ω n R Σ e1)) &&
                      match root_env_lookup x R1 with
                      | Some _ => false
                      | None =>
                          roots_exclude_b x roots1 &&
                          root_env_excludes_b x R1 &&
                          match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env Ω n
                                  (root_env_add x roots1 R1)
                                  (sctx_add x T1 m Σ1) e2 with
                          | infer_err _ => false
                          | infer_ok (T2, Σ2, R2, _) =>
                              sctx_check_ok env x T1 Σ2 &&
                              capture_ref_free_ty_b env T2 &&
                              root_env_excludes_b x (root_env_remove x R2) &&
                              check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env Ω n
                                (root_env_add x roots1 R1)
                                (sctx_add x T1 m Σ1) e2
                          end
                      end
                  end
              end
          | _ => false
          end
      | infer_err _ =>
      match fuel with
      | 0 => false
      | S fuel' =>
          match e with
          | ELet m x T_hidden e1 e2 =>
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel' env Ω n R Σ e1 with
              | infer_err _ => false
              | infer_ok (T1, Σ1, R1, roots1) =>
                  ty_compatible_b Ω T1 T_hidden &&
                  non_function_value_ty_b T_hidden &&
                  (check_expr_root_shadow_store_safe_narrow_summary_fuel
                     fuel' env Ω n R Σ e1 ||
                   (capture_ref_free_ty_b env T1 &&
                    check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                      fuel' env Ω n R Σ e1)) &&
                  match root_env_lookup x R1 with
                  | Some _ => false
                  | None =>
                      roots_exclude_b x roots1 &&
                      root_env_excludes_b x R1 &&
                      match infer_core_env_state_fuel_roots_shadow_safe_checked
                              fuel' env Ω n
                              (root_env_add x roots1 R1)
                              (sctx_add x T_hidden m Σ1) e2 with
                      | infer_err _ => false
                      | infer_ok (T2, Σ2, R2, roots2) =>
                          sctx_check_ok env x T_hidden Σ2 &&
                          capture_ref_free_ty_b env T2 &&
                          root_env_excludes_b x (root_env_remove x R2) &&
                          check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env Ω n
                            (root_env_add x roots1 R1)
                            (sctx_add x T_hidden m Σ1) e2
                      end
                  end
              end
          | ELetInfer m x e1 e2 =>
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel' env Ω n R Σ e1 with
              | infer_err _ => false
              | infer_ok (T1, Σ1, R1, roots1) =>
                  non_function_value_ty_b T1 &&
                  (check_expr_root_shadow_store_safe_narrow_summary_fuel
                     fuel' env Ω n R Σ e1 ||
                   (capture_ref_free_ty_b env T1 &&
                    check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                      fuel' env Ω n R Σ e1)) &&
                  match root_env_lookup x R1 with
                  | Some _ => false
                  | None =>
                      roots_exclude_b x roots1 &&
                      root_env_excludes_b x R1 &&
                      match infer_core_env_state_fuel_roots_shadow_safe_checked
                              fuel' env Ω n
                              (root_env_add x roots1 R1)
                              (sctx_add x T1 m Σ1) e2 with
                      | infer_err _ => false
                      | infer_ok (T2, Σ2, R2, roots2) =>
                          sctx_check_ok env x T1 Σ2 &&
                          capture_ref_free_ty_b env T2 &&
                          root_env_excludes_b x (root_env_remove x R2) &&
                          check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env Ω n
                            (root_env_add x roots1 R1)
                            (sctx_add x T1 m Σ1) e2
                      end
                  end
              end
          | _ => false
          end
      end
      end
  end.

Definition check_expr_root_shadow_store_safe_narrow_summary_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Definition check_fn_root_shadow_generic_direct_store_safe_summary_target
    (env : global_env) (fdef : fn_def) (fname : ident) (type_args : list Ty)
    (args : list expr) (synthetic_body : expr) : bool :=
  store_safe_function_value_call_args_b env args &&
  match lookup_fn_b fname (env_fns env) with
  | None => false
  | Some callee =>
      Nat.eqb (Datatypes.length type_args) (fn_type_params callee) &&
      match check_struct_bounds
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_bounds callee) type_args with
      | Some _ => false
      | None =>
          let callee_body_env :=
            global_env_with_local_bounds env
              (subst_type_params_trait_bounds type_args (fn_bounds callee)) in
          match infer_core_env_roots_shadow_safe callee_body_env
                    (fn_outlives callee)
                    (fn_lifetimes callee)
                    (initial_root_env_for_fn callee)
                    (subst_type_params_ctx type_args (fn_body_ctx callee))
                    (subst_type_params_expr type_args (fn_body callee)),
                infer_env_roots_shadow_safe env callee
                  (initial_root_env_for_fn callee),
                infer_env_roots_shadow_safe env
                  (fn_with_body fdef synthetic_body)
                  (initial_root_env_for_fn fdef) with
          | infer_ok (T_callee, _, R_callee, roots_callee),
            infer_ok _,
            infer_ok (T_body, _, R_out, roots) =>
              preservation_ready_expr_b
                (subst_type_params_expr type_args (fn_body callee)) &&
              check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                env callee type_args &&
              ty_compatible_b (fn_outlives callee) T_callee
                (subst_type_params_ty type_args (fn_ret callee)) &&
              fn_params_roots_exclude_b
                (apply_type_params type_args (fn_params callee))
                roots_callee &&
              fn_params_root_env_excludes_b
                (apply_type_params type_args (fn_params callee))
                R_callee &&
              ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
              fn_params_roots_exclude_b (fn_params fdef) roots &&
              fn_params_root_env_excludes_b (fn_params fdef) R_out
          | _, _, _ => false
          end
      end
  end.

Definition check_fn_root_shadow_generic_direct_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match generic_direct_call_target_expr (fn_body fdef) with
  | Some (fname, type_args, args, synthetic_body) =>
      check_fn_root_shadow_generic_direct_store_safe_summary_target
        env fdef fname type_args args synthetic_body
  | None => false
  end.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_unfold :
  forall env fdef,
    check_fn_root_shadow_generic_direct_store_safe_summary env fdef =
    match generic_direct_call_target_expr (fn_body fdef) with
    | Some (fname, type_args, args, synthetic_body) =>
        check_fn_root_shadow_generic_direct_store_safe_summary_target
          env fdef fname type_args args synthetic_body
    | None => false
    end.
Proof.
  reflexivity.
Qed.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_view :
  forall env fdef,
    check_fn_root_shadow_generic_direct_store_safe_summary env fdef = true ->
    exists fname type_args args synthetic_body,
      generic_direct_call_target_expr (fn_body fdef) =
        Some (fname, type_args, args, synthetic_body) /\
      check_fn_root_shadow_generic_direct_store_safe_summary_target
        env fdef fname type_args args synthetic_body = true.
Proof.
  intros env fdef Hcheck.
  rewrite check_fn_root_shadow_generic_direct_store_safe_summary_unfold in Hcheck.
  destruct (generic_direct_call_target_expr (fn_body fdef))
    as [[[[fname type_args] args] synthetic_body] |] eqn:Htarget;
    try discriminate.
  exists fname, type_args, args, synthetic_body.
  split; [reflexivity | exact Hcheck].
Qed.

Inductive check_fn_root_shadow_generic_direct_store_safe_summary_target_view
    (env : global_env) (fdef : fn_def) (fname : ident)
    (type_args : list Ty) (args : list expr) (synthetic_body : expr) : Prop :=
| GDSummaryTargetView :
    forall fcallee T_body Gamma_body R_body roots_body,
      store_safe_function_value_call_args_b env args = true ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      Datatypes.length type_args = fn_type_params fcallee ->
      check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fcallee) type_args = None ->
      infer_env_roots_shadow_safe env (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef) =
        infer_ok (T_body, Gamma_body, R_body, roots_body) ->
      preservation_ready_expr_b
        (subst_type_params_expr type_args (fn_body fcallee)) = true ->
      check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fcallee type_args = true ->
      fn_params_roots_exclude_b (fn_params fdef) roots_body = true ->
      fn_params_root_env_excludes_b (fn_params fdef) R_body = true ->
      check_fn_root_shadow_generic_direct_store_safe_summary_target_view
        env fdef fname type_args args synthetic_body.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_target_view_sound :
  forall env fdef fname type_args args synthetic_body,
    check_fn_root_shadow_generic_direct_store_safe_summary_target
      env fdef fname type_args args synthetic_body = true ->
    check_fn_root_shadow_generic_direct_store_safe_summary_target_view
      env fdef fname type_args args synthetic_body.
Proof.
  intros env fdef fname type_args args synthetic_body Hcheck.
  unfold check_fn_root_shadow_generic_direct_store_safe_summary_target in Hcheck.
  apply andb_true_iff in Hcheck as [Hsafe_args Hcheck].
  destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
    eqn:Hlookup; try discriminate.
  apply andb_true_iff in Hcheck as [Htype_params Hcheck].
  apply Nat.eqb_eq in Htype_params.
  destruct (check_struct_bounds
    (global_env_with_local_bounds env (fn_bounds fdef))
    (fn_bounds fcallee) type_args) as [bounds_err |] eqn:Hbounds;
    try discriminate.
  destruct (lookup_fn_b_sound_sidecar fname (env_fns env) fcallee Hlookup)
    as [Hin_callee Hname_callee].
  destruct (infer_core_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
      (fn_outlives fcallee) (fn_lifetimes fcallee)
      (initial_root_env_for_fn fcallee)
      (subst_type_params_ctx type_args (fn_body_ctx fcallee))
      (subst_type_params_expr type_args (fn_body fcallee)))
    as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
    eqn:Hcallee_core; try discriminate.
  destruct (infer_env_roots_shadow_safe env fcallee
    (initial_root_env_for_fn fcallee))
    as [[[[T_callee_env Gamma_callee_env] R_callee_env]
          roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
  destruct (infer_env_roots_shadow_safe env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    [[[[[[[Hcallee_ready Hcallee_expr] Hcallee_compat] Hcallee_roots]
         Hcallee_env_excl] Hcompat] Hroots] Henv].
  econstructor; eauto.
Qed.

Lemma infer_env_roots_shadow_safe_core_success_sidecar :
  forall env f R0 T Gamma R roots,
    infer_env_roots_shadow_safe env f R0 = infer_ok (T, Gamma, R, roots) ->
    exists T_body,
      infer_core_env_roots_shadow_safe
        (global_env_with_local_bounds env (fn_bounds f))
        (fn_outlives f) (fn_lifetimes f) R0 (fn_body_ctx f) (fn_body f) =
        infer_ok (T_body, Gamma, R, roots) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true.
Proof.
  unfold infer_env_roots_shadow_safe.
  intros env f R0 T Gamma R roots Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f))
    (fn_outlives f))); try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f))
    (fn_ret f))); try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f) R0 (fn_body_ctx f) (fn_body f))
    as [[[[T_body Gamma_body] R_body] roots_body] | err] eqn:Hcore;
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompat; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Gamma_body); try discriminate.
  inversion Hinfer; subst.
  exists T_body. split; [reflexivity | exact Hcompat].
Qed.

Lemma infer_env_roots_shadow_safe_params_nodup_sidecar :
  forall env f R0 T Gamma R roots,
    infer_env_roots_shadow_safe env f R0 = infer_ok (T, Gamma, R, roots) ->
    NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f R0 T Gamma R roots Hinfer.
  unfold infer_env_roots_shadow_safe in Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f))
    (fn_outlives f))); try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f))
    (fn_ret f))); try discriminate.
  unfold check_fn_binding_params in Hinfer.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f))
    (fn_captures f))); try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f))
    (fn_params f))); try discriminate.
  destruct (duplicate_param_name (fn_binding_params f)) as [dup |]
    eqn:Hdup; try discriminate.
  unfold fn_binding_params in Hdup.
  eapply duplicate_param_name_none_nodup_params_ctx_prefix. exact Hdup.
Qed.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_view_prop :
  forall env fdef,
    check_fn_root_shadow_generic_direct_store_safe_summary env fdef = true ->
    exists fname type_args args synthetic_body fcallee T_body Gamma_body R_body
      roots_body T_body_core,
      generic_direct_call_target_expr (fn_body fdef) =
        Some (fname, type_args, args, synthetic_body) /\
      synthetic_body = ECallGeneric fname type_args args /\
      store_safe_function_value_call_args_b env args = true /\
      In fcallee (env_fns env) /\
      fn_name fcallee = fname /\
      Datatypes.length type_args = fn_type_params fcallee /\
      check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fcallee) type_args = None /\
      infer_env_roots_shadow_safe env (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef) =
        infer_ok (T_body, Gamma_body, R_body, roots_body) /\
      NoDup (ctx_names (params_ctx (fn_params fdef))) /\
      infer_core_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (fn_bounds (fn_with_body fdef synthetic_body)))
        (fn_outlives (fn_with_body fdef synthetic_body))
        (fn_lifetimes (fn_with_body fdef synthetic_body))
        (initial_root_env_for_fn fdef)
        (fn_body_ctx (fn_with_body fdef synthetic_body)) synthetic_body =
        infer_ok (T_body_core, Gamma_body, R_body, roots_body) /\
      ty_compatible_b (fn_outlives (fn_with_body fdef synthetic_body))
        T_body_core (fn_ret (fn_with_body fdef synthetic_body)) = true /\
      preservation_ready_expr_b
        (subst_type_params_expr type_args (fn_body fcallee)) = true /\
      check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fcallee type_args = true /\
      fn_params_roots_exclude_b (fn_params fdef) roots_body = true /\
      fn_params_root_env_excludes_b (fn_params fdef) R_body = true.
Proof.
  intros env fdef Hcheck.
  destruct (check_fn_root_shadow_generic_direct_store_safe_summary_view
    env fdef Hcheck) as
    (fname & type_args & args & synthetic_body & Htarget & Htarget_check).
  pose proof
    (check_fn_root_shadow_generic_direct_store_safe_summary_target_view_sound
      env fdef fname type_args args synthetic_body Htarget_check) as Hview.
  destruct Hview as
    [fcallee T_body Gamma_body R_body roots_body Hsafe_args Hin_callee
      Hname_callee Htype_params Hbounds Hbody_env Hcallee_ready
      Hcallee_expr Hroots Henv].
  pose proof (infer_env_roots_shadow_safe_params_nodup_sidecar env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Hnodup.
  unfold fn_with_body in Hnodup. simpl in Hnodup.
  destruct (infer_env_roots_shadow_safe_core_success_sidecar env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env)
    as (T_body_core & Hbody_core & Hbody_compat).
  exists fname, type_args, args, synthetic_body, fcallee, T_body,
    Gamma_body, R_body, roots_body, T_body_core.
  repeat split; try assumption.
  unfold generic_direct_call_target_expr in Htarget.
  destruct (fn_body fdef); try discriminate.
  inversion Htarget. reflexivity.
Qed.

Definition check_fn_root_shadow_direct_receiver_method_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match direct_call_receiver_method_target_expr (fn_body fdef) with
  | Some (method_name, type_args, receiver_name, receiver_args, method_args,
      synthetic_body) =>
      store_safe_function_value_call_args_b env receiver_args &&
      store_safe_function_value_call_args_b env method_args &&
      negb (ident_in_b receiver_method_hidden_receiver_name
        (args_free_vars_checker method_args)) &&
      negb (ident_in_b receiver_method_hidden_receiver_name
        (args_local_store_names method_args)) &&
      negb (ident_in_b receiver_method_hidden_receiver_name
        (ctx_names (fn_body_ctx fdef))) &&
      match lookup_fn_b receiver_name (env_fns env),
            lookup_fn_b method_name (env_fns env) with
      | Some receiver_callee, Some method_callee =>
          Nat.eqb (Datatypes.length type_args) (fn_type_params method_callee) &&
          match check_struct_bounds
                  (global_env_with_local_bounds env (fn_bounds fdef))
                  (fn_bounds method_callee) type_args with
          | Some _ => false
          | None =>
              let method_body_env :=
                global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args
                    (fn_bounds method_callee)) in
              match infer_core_env_roots_shadow_safe env
                        (fn_outlives receiver_callee)
                        (fn_lifetimes receiver_callee)
                        (initial_root_env_for_fn receiver_callee)
                        (fn_body_ctx receiver_callee)
                        (fn_body receiver_callee),
                    infer_env_roots_shadow_safe env receiver_callee
                      (initial_root_env_for_fn receiver_callee),
                    infer_core_env_roots_shadow_safe method_body_env
                        (fn_outlives method_callee)
                        (fn_lifetimes method_callee)
                        (initial_root_env_for_fn method_callee)
                        (subst_type_params_ctx type_args
                          (fn_body_ctx method_callee))
                        (subst_type_params_expr type_args
                          (fn_body method_callee)),
                    infer_env_roots_shadow_safe env method_callee
                      (initial_root_env_for_fn method_callee),
                    infer_env_roots_shadow_safe env
                      (fn_with_body fdef
                        (direct_call_receiver_method_hidden_let_synthetic_body
                          (fn_ret receiver_callee) method_name type_args
                          receiver_name receiver_args method_args))
                      (initial_root_env_for_fn fdef) with
              | infer_ok (T_receiver, _, R_receiver, roots_receiver),
                infer_ok _,
                infer_ok (T_method, _, R_method, roots_method),
                infer_ok _,
                infer_ok (T_body, _, R_out, roots) =>
                  check_expr_root_shadow_store_safe_narrow_summary
                    env (fn_outlives receiver_callee)
                    (fn_lifetimes receiver_callee)
                    (initial_root_env_for_fn receiver_callee)
                    (fn_body_ctx receiver_callee)
                    (fn_body receiver_callee) &&
                  ty_compatible_b (fn_outlives receiver_callee) T_receiver
                    (fn_ret receiver_callee) &&
                  fn_params_roots_exclude_b (fn_params receiver_callee)
                    roots_receiver &&
                  fn_params_root_env_excludes_b (fn_params receiver_callee)
                    R_receiver &&
                  preservation_ready_expr_b
                    (subst_type_params_expr type_args
                      (fn_body method_callee)) &&
                  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                    env method_callee type_args &&
                  ty_compatible_b (fn_outlives method_callee) T_method
                    (subst_type_params_ty type_args (fn_ret method_callee)) &&
                  fn_params_roots_exclude_b
                    (apply_type_params type_args (fn_params method_callee))
                    roots_method &&
                  fn_params_root_env_excludes_b
                    (apply_type_params type_args (fn_params method_callee))
                    R_method &&
                  ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | _, _, _, _, _ => false
              end
          end
      | _, _ => false
      end
  | None => false
  end.

Definition check_fn_root_shadow_generic_direct_receiver_method_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match generic_direct_call_receiver_method_target_expr (fn_body fdef) with
  | Some (method_name, type_args, receiver_name, receiver_type_args,
      receiver_args, method_args, synthetic_body) =>
      store_safe_function_value_call_args_b env receiver_args &&
      store_safe_function_value_call_args_b env method_args &&
      negb (ident_in_b receiver_method_hidden_receiver_name
        (args_free_vars_checker method_args)) &&
      negb (ident_in_b receiver_method_hidden_receiver_name
        (args_local_store_names method_args)) &&
      negb (ident_in_b receiver_method_hidden_receiver_name
        (ctx_names (fn_body_ctx fdef))) &&
      match lookup_fn_b receiver_name (env_fns env),
            lookup_fn_b method_name (env_fns env) with
      | Some receiver_callee, Some method_callee =>
          Nat.eqb (Datatypes.length receiver_type_args)
            (fn_type_params receiver_callee) &&
          Nat.eqb (Datatypes.length type_args) (fn_type_params method_callee) &&
          match check_struct_bounds
                  (global_env_with_local_bounds env (fn_bounds fdef))
                  (fn_bounds receiver_callee) receiver_type_args,
                check_struct_bounds
                  (global_env_with_local_bounds env (fn_bounds fdef))
                  (fn_bounds method_callee) type_args with
          | None, None =>
              match infer_env_roots_shadow_safe env receiver_callee
                      (initial_root_env_for_fn receiver_callee),
                    infer_env_roots_shadow_safe env method_callee
                      (initial_root_env_for_fn method_callee),
                    infer_env_roots_shadow_safe env
                      (fn_with_body fdef
                        (generic_direct_call_receiver_method_hidden_let_synthetic_body
                          (subst_type_params_ty receiver_type_args
                            (fn_ret receiver_callee))
                          method_name type_args receiver_name
                          receiver_type_args receiver_args method_args))
                      (initial_root_env_for_fn fdef) with
              | infer_ok _,
                infer_ok _,
                infer_ok (T_body, _, R_out, roots) =>
                  preservation_ready_expr_b
                    (subst_type_params_expr receiver_type_args
                      (fn_body receiver_callee)) &&
                  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                    env receiver_callee receiver_type_args &&
                  preservation_ready_expr_b
                    (subst_type_params_expr type_args
                      (fn_body method_callee)) &&
                  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                    env method_callee type_args &&
                  ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | _, _, _ => false
              end
          | _, _ => false
          end
      | _, _ => false
      end
  | None => false
  end.

Definition check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match fn_captures fdef with
  | [] =>
      match direct_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          store_safe_function_value_call_args_b env args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              match fn_captures callee with
              | [] =>
                  match infer_env_roots_shadow_safe env
                          (fn_with_body fdef synthetic_body)
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (T_body, _, R_out, roots) =>
                      ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
                      fn_params_roots_exclude_b (fn_params fdef) roots &&
                      fn_params_root_env_excludes_b (fn_params fdef) R_out
                  | infer_err _ => false
                  end
              | _ => false
              end
          end
      | None => false
      end
  | _ => false
  end.

Fixpoint check_fn_root_shadow_no_capture_direct_call_component_closure_seen
    (fuel : nat) (seen : list ident) (env : global_env)
    (fdef : fn_def) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if ident_in_b (fn_name fdef) seen then true
      else
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env fdef &&
        match direct_call_target_expr (fn_body fdef) with
        | Some (fname, _, _) =>
            match lookup_fn_b fname (env_fns env) with
            | Some callee =>
                check_fn_root_shadow_no_capture_direct_call_component_closure_seen
                  fuel' (fn_name fdef :: seen) env callee
            | None => false
            end
        | None => false
        end
  end.

Definition check_fn_root_shadow_no_capture_direct_call_component_closure
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_no_capture_direct_call_component_closure_seen
    10001 [] env fdef.

Definition check_fn_root_shadow_no_capture_direct_call_component_exact_body_target
    (_env : global_env) (fdef : fn_def) : bool :=
  match fn_body fdef with
  | ECall _ _ => true
  | _ => false
  end.

Fixpoint check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
    (fuel : nat) (seen : list ident) (env : global_env)
    (fdef : fn_def) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if ident_in_b (fn_name fdef) seen then true
      else
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env fdef &&
        check_fn_root_shadow_no_capture_direct_call_component_exact_body_target
          env fdef &&
        match direct_call_target_expr (fn_body fdef) with
        | Some (fname, _, _) =>
            match lookup_fn_b fname (env_fns env) with
            | Some callee =>
                check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
                  fuel' (fn_name fdef :: seen) env callee
            | None => false
            end
        | None => false
        end
  end.

Definition check_fn_root_shadow_no_capture_direct_call_component_exact_closure
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
    10001 [] env fdef.

Definition check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
    (env : global_env) : bool :=
  forallb
    (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary env)
    (env_fns env).

Definition check_fn_root_shadow_captured_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_non_capturing_call_provenance_summary env fdef with
  | true => true
  | false =>
      (preservation_ready_expr_b (fn_body fdef) &&
       check_fn_root_shadow_captured_callee_provenance_summary env fdef) ||
      (match captured_call_target_expr (fn_body fdef) with
      | Some (fname, captures, args) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              match check_make_closure_captures_exact_sctx_with_env env
                      (fn_outlives fdef)
                      (sctx_of_ctx (fn_body_ctx fdef))
                      captures
                      (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  check_fn_root_shadow_captured_callee_provenance_summary
                    env callee &&
                  match infer_env_roots_shadow_safe env fdef
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (_, _, R_out, roots) =>
                      fn_params_roots_exclude_b (fn_params fdef) roots &&
                      fn_params_root_env_excludes_b (fn_params fdef) R_out
                  | infer_err _ => false
                  end
              end
          end
      | None => false
      end ||
      (match infer_core_env_roots_shadow_safe env
                  (fn_outlives fdef)
                  (fn_lifetimes fdef)
                  (initial_root_env_for_fn fdef)
                  (fn_body_ctx fdef)
                  (fn_body fdef),
                infer_env_roots_shadow_safe env fdef
                  (initial_root_env_for_fn fdef) with
          | infer_ok (T_body, _, R_out, roots), infer_ok _ =>
              check_expr_root_shadow_captured_call_provenance_summary
                env (fn_outlives fdef) (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef)
                (fn_body_ctx fdef) (fn_body fdef) &&
              ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
              fn_params_roots_exclude_b (fn_params fdef) roots &&
              fn_params_root_env_excludes_b (fn_params fdef) R_out
          | _, _ => false
          end) ||
      match local_captured_call_target_expr (fn_body fdef) with
      | Some (fname, captures, args, m, x, T, direct_body, let_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              negb (existsb (ident_eqb x)
                (ctx_names (params_ctx (fn_captures callee)))) &&
              match check_make_closure_captures_exact_sctx_with_env env
                      (fn_outlives fdef)
                      (sctx_of_ctx (fn_body_ctx fdef))
                      captures
                      (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  check_fn_root_shadow_captured_callee_provenance_summary
                    env callee &&
                  match infer_env_roots_shadow_safe env
                          (fn_with_body fdef direct_body)
                          (initial_root_env_for_fn fdef),
                        infer_env_roots_shadow_safe env
                          (fn_with_body fdef let_body)
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (_, _, R_direct, roots_direct),
                    infer_ok (_, _, _, _) =>
                      fn_params_roots_exclude_b (fn_params fdef)
                        roots_direct &&
                      fn_params_root_env_excludes_b (fn_params fdef)
                        R_direct
                  | _, _ => false
                  end
              end
          end
      | None => false
      end)
  end.

Definition check_fn_root_shadow_captured_call_core_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  (check_fn_root_shadow_captured_call_provenance_summary env fdef ||
  (match direct_call_target_expr (fn_body fdef) with
   | Some (fname, args, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           match infer_core_env_roots_shadow_safe env
                     (fn_outlives callee)
                     (fn_lifetimes callee)
                     (initial_root_env_for_fn callee)
                     (fn_body_ctx callee)
                     (fn_body callee),
                 infer_env_roots_shadow_safe env callee
                   (initial_root_env_for_fn callee),
                 infer_env_roots_shadow_safe env
                   (fn_with_body fdef synthetic_body)
                   (initial_root_env_for_fn fdef) with
           | infer_ok (T_callee, _, R_callee, roots_callee),
             infer_ok _,
             infer_ok (T_body, _, R_out, roots) =>
               check_expr_root_shadow_store_safe_narrow_summary
                 env (fn_outlives callee) (fn_lifetimes callee)
                 (initial_root_env_for_fn callee)
                 (fn_body_ctx callee) (fn_body callee) &&
               ty_compatible_b (fn_outlives callee) T_callee
                 (fn_ret callee) &&
               fn_params_roots_exclude_b (fn_params callee) roots_callee &&
               fn_params_root_env_excludes_b (fn_params callee) R_callee &&
               ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
               fn_params_roots_exclude_b (fn_params fdef) roots &&
               fn_params_root_env_excludes_b (fn_params fdef) R_out
           | _, _, _ => false
           end
       end
   | None => false
   end) ||
  check_fn_root_shadow_generic_direct_store_safe_summary env fdef) ||
  (match let_bound_generic_direct_call_target_expr (fn_body fdef) with
   | Some (fname, type_args, args, T_hidden, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           Nat.eqb (Datatypes.length type_args) (fn_type_params callee) &&
           match check_struct_bounds
                   (global_env_with_local_bounds env (fn_bounds fdef))
                   (fn_bounds callee) type_args with
           | Some _ => false
           | None =>
               let callee_body_env :=
                 global_env_with_local_bounds env
                   (subst_type_params_trait_bounds type_args (fn_bounds callee)) in
               match infer_core_env_roots_shadow_safe callee_body_env
                         (fn_outlives callee)
                         (fn_lifetimes callee)
                         (initial_root_env_for_fn callee)
                         (subst_type_params_ctx type_args (fn_body_ctx callee))
                         (subst_type_params_expr type_args (fn_body callee)),
                     infer_env_roots_shadow_safe env callee
                       (initial_root_env_for_fn callee),
                     infer_env_roots_shadow_safe env
                       (fn_with_body fdef synthetic_body)
                       (initial_root_env_for_fn fdef) with
               | infer_ok (T_callee, _, R_callee, roots_callee),
                 infer_ok _,
                 infer_ok (T_body, _, R_out, roots) =>
                   check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                     env callee type_args &&
                   ty_compatible_b (fn_outlives callee) T_callee
                     (subst_type_params_ty type_args (fn_ret callee)) &&
                   fn_params_roots_exclude_b
                     (apply_type_params type_args (fn_params callee))
                     roots_callee &&
                   fn_params_root_env_excludes_b
                     (apply_type_params type_args (fn_params callee))
                     R_callee &&
                   ty_compatible_b (fn_outlives fdef) T_hidden (fn_ret fdef) &&
                   fn_params_roots_exclude_b (fn_params fdef) roots &&
                   fn_params_root_env_excludes_b (fn_params fdef) R_out
               | _, _, _ => false
               end
           end
       end
   | None => false
   end) ||
  (match if_literal_generic_direct_call_target_expr (fn_body fdef) with
   | Some (b, fname_then, type_args_then, args_then,
       fname_else, type_args_else, args_else, synthetic_body) =>
       store_safe_function_value_call_args_b env args_then &&
       store_safe_function_value_call_args_b env args_else &&
       match lookup_fn_b fname_then (env_fns env),
             lookup_fn_b fname_else (env_fns env) with
       | Some callee_then, Some callee_else =>
           Nat.eqb (Datatypes.length type_args_then)
             (fn_type_params callee_then) &&
           Nat.eqb (Datatypes.length type_args_else)
             (fn_type_params callee_else) &&
           match check_struct_bounds
                   (global_env_with_local_bounds env (fn_bounds fdef))
                   (fn_bounds callee_then) type_args_then,
                 check_struct_bounds
                   (global_env_with_local_bounds env (fn_bounds fdef))
                   (fn_bounds callee_else) type_args_else with
           | None, None =>
               match infer_core_env_roots_shadow_safe env
                         (fn_outlives callee_then)
                         (fn_lifetimes callee_then)
                         (initial_root_env_for_fn callee_then)
                         (subst_type_params_ctx type_args_then
                           (fn_body_ctx callee_then))
                         (subst_type_params_expr type_args_then
                           (fn_body callee_then)),
                     infer_env_roots_shadow_safe env callee_then
                       (initial_root_env_for_fn callee_then),
                     infer_core_env_roots_shadow_safe env
                         (fn_outlives callee_else)
                         (fn_lifetimes callee_else)
                         (initial_root_env_for_fn callee_else)
                         (subst_type_params_ctx type_args_else
                           (fn_body_ctx callee_else))
                         (subst_type_params_expr type_args_else
                           (fn_body callee_else)),
                     infer_env_roots_shadow_safe env callee_else
                       (initial_root_env_for_fn callee_else),
                     infer_env_roots_shadow_safe env
                       (fn_with_body fdef synthetic_body)
                       (initial_root_env_for_fn fdef) with
               | infer_ok (T_then, _, R_then, roots_then),
                 infer_ok _,
                 infer_ok (T_else, _, R_else, roots_else),
                 infer_ok _,
                 infer_ok (T_body, _, R_out, roots) =>
                   check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                     env callee_then type_args_then &&
                   ty_compatible_b (fn_outlives callee_then) T_then
                     (subst_type_params_ty type_args_then
                       (fn_ret callee_then)) &&
                   fn_params_roots_exclude_b
                     (apply_type_params type_args_then (fn_params callee_then))
                     roots_then &&
                   fn_params_root_env_excludes_b
                     (apply_type_params type_args_then (fn_params callee_then))
                     R_then &&
                   check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                     env callee_else type_args_else &&
                   ty_compatible_b (fn_outlives callee_else) T_else
                     (subst_type_params_ty type_args_else
                       (fn_ret callee_else)) &&
                   fn_params_roots_exclude_b
                     (apply_type_params type_args_else (fn_params callee_else))
                     roots_else &&
                   fn_params_root_env_excludes_b
                     (apply_type_params type_args_else (fn_params callee_else))
                     R_else &&
                   ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
                   fn_params_roots_exclude_b (fn_params fdef) roots &&
                   fn_params_root_env_excludes_b (fn_params fdef) R_out
               | _, _, _, _, _ => false
               end
           | _, _ => false
           end
       | _, _ => false
       end
   | None => false
   end) ||
  (match local_fn_value_call_target_expr_with_binder (fn_body fdef) with
   | Some (x, fname, args, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       negb (ident_in_b x (args_free_vars_checker args)) &&
       negb (ident_in_b x (args_local_store_names args)) &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           check_fn_root_shadow_generic_direct_store_safe_summary env callee &&
           match infer_env_roots_shadow_safe env
                   (fn_with_body fdef synthetic_body)
                   (initial_root_env_for_fn fdef) with
           | infer_ok (T_body, _, R_out, roots) =>
               ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
               fn_params_roots_exclude_b (fn_params fdef) roots &&
               fn_params_root_env_excludes_b (fn_params fdef) R_out
           | infer_err _ => false
           end
       end
   | None => false
   end) ||
  match infer_core_env_roots_shadow_safe_checked env
              (fn_outlives fdef)
              (fn_lifetimes fdef)
              (initial_root_env_for_fn fdef)
              (fn_body_ctx fdef)
              (fn_body fdef),
            infer_env_roots_shadow_safe_checked env fdef
              (initial_root_env_for_fn fdef) with
  | infer_ok (T_body, _, R_out, roots), infer_ok _ =>
      check_expr_root_shadow_store_safe_narrow_summary_checked
        env (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (fn_body_ctx fdef) (fn_body fdef) &&
      ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | _, _ => false
  end.

Definition check_fn_root_shadow_captured_call_base_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_core_store_safe_summary env fdef.

Definition check_fn_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_base_store_safe_summary env fdef.

Definition check_env_root_shadow_captured_call_store_safe_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_captured_call_store_safe_summary env)
    (env_fns env).

Definition check_fn_root_shadow_captured_call_store_safe_summary_with_direct_receiver_method
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_store_safe_summary env fdef ||
  check_fn_root_shadow_direct_receiver_method_store_safe_summary env fdef.

Definition check_env_root_shadow_captured_call_store_safe_summary_with_direct_receiver_method
    (env : global_env) : bool :=
  forallb
    (check_fn_root_shadow_captured_call_store_safe_summary_with_direct_receiver_method
      env)
    (env_fns env).

Definition check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_store_safe_summary env fdef ||
  check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
    env fdef.

Definition check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    (env : global_env) : bool :=
  forallb
    (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env)
    (env_fns env).

Definition check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_store_safe_summary env fdef ||
  check_fn_root_shadow_no_capture_direct_call_component_closure env fdef.

Definition check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_store_safe_summary env fdef ||
  check_fn_root_shadow_no_capture_direct_call_component_exact_closure env fdef.

Definition check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
    (env : global_env) (fdef : fn_def) : bool :=
  if check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
       env fdef
  then check_fn_root_shadow_no_capture_direct_call_component_exact_closure
       env fdef
  else check_fn_root_shadow_captured_call_store_safe_summary env fdef.

Definition check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
    (env : global_env) : bool :=
  forallb
    (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
      env)
    (env_fns env).

Definition check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    (env : global_env) : bool :=
  forallb
    (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env)
    (env_fns env).

Definition check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
    (env : global_env) : bool :=
  forallb
    (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env)
    (env_fns env).

Definition check_env_root_shadow_direct_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_direct_call_provenance_summary env)
    (env_fns env).

Definition check_env_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_non_capturing_call_provenance_summary env)
    (env_fns env).

Definition check_env_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_captured_call_provenance_summary env)
    (env_fns env).

Definition check_fn_ordinary_safety_gate
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_provenance_summary env fdef.

Definition check_program_env (env : global_env) : bool :=
  forallb (fun f =>
    match infer_full_env env f with
    | infer_ok _ => check_fn_ordinary_safety_gate env f
    | infer_err _ => false
    end) (env_fns env).

Definition check_program_env_alpha (env : global_env) : bool :=
  global_names_unique_b (alpha_normalize_global_env env) &&
  check_program_env (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated (env : global_env) : bool :=
  check_program_env_alpha env.

Definition check_program_env_alpha_elab (env : global_env) : bool :=
  global_names_unique_b (alpha_normalize_global_env env) &&
  match infer_program_env_alpha_elab env with
  | infer_ok env' => check_program_env env'
  | infer_err _ => false
  end.

Definition check_env_preservation_ready (env : global_env) : bool :=
  forallb (fun fdef => preservation_ready_expr_b (fn_body fdef))
    (env_fns env).

Definition check_program_env_alpha_validated_root_shadow (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_summary (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_provenance_summary (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_direct_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_non_capturing_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_captured_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  top_level_names_unique_b (alpha_normalize_global_env env) &&
  match infer_program_env_alpha_elab env with
  | infer_ok env' =>
      check_env_root_shadow_captured_call_provenance_summary env'
  | infer_err _ => false
  end.

Definition check_program_env_alpha_validated_root_shadow_provenance
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  (check_env_root_shadow_provenance_summary
     (alpha_normalize_global_env env) &&
   check_env_preservation_ready (alpha_normalize_global_env env)).

Definition infer_fn_env_end2end (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let R0 := initial_root_env_for_params (fn_params f ++ fn_captures f) in
  match infer_full_env_roots_checked env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      if check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
           env f
      then infer_ok res
      else infer_err ErrEndToEndSafetyGateFailed
  end.

Fixpoint infer_fns_env_end2end (env : global_env) (fns : list fn_def)
    : infer_result unit :=
  match fns with
  | [] => infer_ok tt
  | f :: rest =>
      match infer_fn_env_end2end env f with
      | infer_err err => infer_err (ErrInFunction (fn_name f) err)
      | infer_ok _ => infer_fns_env_end2end env rest
      end
  end.

Definition infer_program_env_end2end (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  if global_names_unique_b env_alpha then
    match infer_program_env_alpha_elab env with
    | infer_err err => infer_err err
    | infer_ok env_elab =>
        match infer_fns_env_end2end env_elab (env_fns env_elab) with
        | infer_err err => infer_err err
        | infer_ok _ => infer_ok env_elab
        end
    end
  else infer_err ErrGlobalNamesNotUnique.

Definition check_program_env_end2end (env : global_env) : bool :=
  match infer_program_env_end2end env with
  | infer_ok _ => true
  | infer_err _ => false
  end.

Definition infer_fn_env_end2end_assoc (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let R0 := initial_root_env_for_params (fn_params f ++ fn_captures f) in
  match infer_full_env_roots_checked_assoc env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      if check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
           env f
      then infer_ok res
      else infer_err ErrEndToEndSafetyGateFailed
  end.

Fixpoint infer_fns_env_end2end_assoc (env : global_env) (fns : list fn_def)
    : infer_result unit :=
  match fns with
  | [] => infer_ok tt
  | f :: rest =>
      match infer_fn_env_end2end_assoc env f with
      | infer_err err => infer_err (ErrInFunction (fn_name f) err)
      | infer_ok _ => infer_fns_env_end2end_assoc env rest
      end
  end.

Definition infer_program_env_end2end_assoc (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  if global_names_unique_b env_alpha then
    match infer_program_env_alpha_elab env with
    | infer_err err => infer_err err
    | infer_ok env_elab =>
        match infer_fns_env_end2end_assoc env_elab (env_fns env_elab) with
        | infer_err err => infer_err err
        | infer_ok _ => infer_ok env_elab
        end
    end
  else infer_err ErrGlobalNamesNotUnique.

Definition check_program_env_end2end_assoc (env : global_env) : bool :=
  match infer_program_env_end2end_assoc env with
  | infer_ok _ => true
  | infer_err _ => false
  end.


Definition infer_fn_env_end2end_strict_exact_closure (env : global_env)
    (f : fn_def) : infer_result (Ty * ctx * root_env * root_set) :=
  let R0 := initial_root_env_for_params (fn_params f ++ fn_captures f) in
  match infer_full_env_roots_checked env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      if check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
           env f
      then infer_ok res
      else infer_err ErrEndToEndSafetyGateFailed
  end.

Fixpoint infer_fns_env_end2end_strict_exact_closure (env : global_env)
    (fns : list fn_def) : infer_result unit :=
  match fns with
  | [] => infer_ok tt
  | f :: rest =>
      match infer_fn_env_end2end_strict_exact_closure env f with
      | infer_err err => infer_err (ErrInFunction (fn_name f) err)
      | infer_ok _ => infer_fns_env_end2end_strict_exact_closure env rest
      end
  end.

Definition infer_program_env_end2end_strict_exact_closure (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  if global_names_unique_b env_alpha then
    match infer_program_env_alpha_elab env with
    | infer_err err => infer_err err
    | infer_ok env_elab =>
        match infer_fns_env_end2end_strict_exact_closure
                env_elab (env_fns env_elab) with
        | infer_err err => infer_err err
        | infer_ok _ => infer_ok env_elab
        end
    end
  else infer_err ErrGlobalNamesNotUnique.

Definition check_program_env_end2end_strict_exact_closure
    (env : global_env) : bool :=
  match infer_program_env_end2end_strict_exact_closure env with
  | infer_ok _ => true
  | infer_err _ => false
  end.


Definition infer_fn_env_end2end_assoc_strict_exact_closure (env : global_env)
    (f : fn_def) : infer_result (Ty * ctx * root_env * root_set) :=
  let R0 := initial_root_env_for_params (fn_params f ++ fn_captures f) in
  match infer_full_env_roots_checked_assoc env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      if check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
           env f
      then infer_ok res
      else infer_err ErrEndToEndSafetyGateFailed
  end.

Fixpoint infer_fns_env_end2end_assoc_strict_exact_closure (env : global_env)
    (fns : list fn_def) : infer_result unit :=
  match fns with
  | [] => infer_ok tt
  | f :: rest =>
      match infer_fn_env_end2end_assoc_strict_exact_closure env f with
      | infer_err err => infer_err (ErrInFunction (fn_name f) err)
      | infer_ok _ => infer_fns_env_end2end_assoc_strict_exact_closure env rest
      end
  end.

Definition infer_program_env_end2end_assoc_strict_exact_closure
    (env : global_env) : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  if global_names_unique_b env_alpha then
    match infer_program_env_alpha_elab env with
    | infer_err err => infer_err err
    | infer_ok env_elab =>
        match infer_fns_env_end2end_assoc_strict_exact_closure
                env_elab (env_fns env_elab) with
        | infer_err err => infer_err err
        | infer_ok _ => infer_ok env_elab
        end
    end
  else infer_err ErrGlobalNamesNotUnique.

Definition check_program_env_end2end_assoc_strict_exact_closure
    (env : global_env) : bool :=
  match infer_program_env_end2end_assoc_strict_exact_closure env with
  | infer_ok _ => true
  | infer_err _ => false
  end.

