From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program TypingRules TypeChecker.
From Stdlib Require Import List String.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Wrapper-free env/stateful typing specification                       *)
(* ------------------------------------------------------------------ *)

Inductive typed_place_type_env_structural (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPTES_Var : forall x T st,
      sctx_lookup x Σ = Some (T, st) ->
      typed_place_type_env_structural env Σ (PVar x) T
  | TPTES_Deref : forall p la rk T u,
      typed_place_type_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      typed_place_type_env_structural env Σ (PDeref p) T
  | TPTES_Field : forall p sname lts args sdef fdef T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      typed_place_type_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef).

Inductive typed_place_env_structural (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPES_Var : forall x T st,
      sctx_lookup x Σ = Some (T, st) ->
      binding_available_b st [] = true ->
      typed_place_env_structural env Σ (PVar x) T
  | TPES_Deref : forall p la rk T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      typed_place_env_structural env Σ (PDeref p) T
  | TPES_Field : forall p sname lts args sdef fdef x path T_root st T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      place_path (PField p (field_name fdef)) = Some (x, path) ->
      sctx_lookup x Σ = Some (T_root, st) ->
      binding_available_b st path = true ->
      typed_place_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef)
  | TPES_Field_Indirect : forall p sname lts args sdef fdef T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      place_path (PField p (field_name fdef)) = None ->
      typed_place_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef).
Inductive place_under_unique_ref_structural (env : global_env) (Σ : sctx)
    : place -> Prop :=
  | PUURS_Deref : forall p la T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
      place_under_unique_ref_structural env Σ (PDeref p)
  | PUURS_Field : forall p f,
      place_under_unique_ref_structural env Σ p ->
      place_under_unique_ref_structural env Σ (PField p f).

Inductive typed_env_structural (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TES_Unit : forall Σ,
      typed_env_structural env Ω n Σ EUnit (MkTy UUnrestricted TUnits) Σ
  | TES_LitInt : forall Σ i,
      typed_env_structural env Ω n Σ (ELit (LInt i)) (MkTy UUnrestricted TIntegers) Σ
  | TES_LitFloat : forall Σ f,
      typed_env_structural env Ω n Σ (ELit (LFloat f)) (MkTy UUnrestricted TFloats) Σ
  | TES_LitBool : forall Σ b,
      typed_env_structural env Ω n Σ (ELit (LBool b)) (MkTy UUnrestricted TBooleans) Σ
  | TES_Var_Copy : forall Σ x T,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EVar x) T Σ
  | TES_Var_Move : forall Σ Σ' x T,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      typed_env_structural env Ω n Σ (EVar x) T Σ'
  | TES_Place_Copy : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EPlace p) T Σ
  | TES_Place_Move : forall Σ Σ' p T x path,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      typed_env_structural env Ω n Σ (EPlace p) T Σ'
  | TES_Fn : forall Σ fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      typed_env_structural env Ω n Σ (EFn fname) (fn_value_ty fdef) Σ
  | TES_Struct : forall Σ Σ' sname lts args fields sdef,
      lookup_struct sname env = Some sdef ->
      Datatypes.length lts = struct_lifetimes sdef ->
      Datatypes.length args = struct_type_params sdef ->
      check_struct_bounds env (struct_bounds sdef) args = None ->
      typed_fields_env_structural env Ω n lts args Σ fields (struct_fields sdef) Σ' ->
      typed_env_structural env Ω n Σ (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ'
  | TES_Let : forall Σ Σ1 Σ2 m x T T1 e1 e2 T2,
      typed_env_structural env Ω n Σ e1 T1 Σ1 ->
      ty_compatible_b Ω T1 T = true ->
      typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
      sctx_check_ok x T Σ2 = true ->
      typed_env_structural env Ω n Σ (ELet m x T e1 e2) T2 (sctx_remove x Σ2)
  | TES_LetInfer : forall Σ Σ1 Σ2 m x T1 e1 e2 T2,
      typed_env_structural env Ω n Σ e1 T1 Σ1 ->
      typed_env_structural env Ω n (sctx_add x T1 m Σ1) e2 T2 Σ2 ->
      sctx_check_ok x T1 Σ2 = true ->
      typed_env_structural env Ω n Σ (ELetInfer m x e1 e2) T2 (sctx_remove x Σ2)
  | TES_Drop : forall Σ Σ' e T,
      typed_env_structural env Ω n Σ e T Σ' ->
      typed_env_structural env Ω n Σ (EDrop e) (MkTy UUnrestricted TUnits) Σ'
  | TES_Replace_Path : forall Σ Σ1 Σ2 p e_new T_old T_new x path,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ2
  | TES_Replace_Indirect : forall Σ Σ' p e_new T_old T_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ'
  | TES_Assign_Path : forall Σ Σ' p e_new T_old T_new x path,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_structural env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TES_Assign_Indirect : forall Σ Σ' p e_new T_old T_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_structural env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TES_BorrowShared : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_structural env Ω n Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ
  | TES_BorrowUnique : forall Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_structural env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ
  | TES_BorrowUnique_Indirect : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      typed_env_structural env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ
  | TES_Deref_Place : forall Σ r p la rk T u,
      expr_as_place r = Some p ->
      typed_place_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EDeref r) T Σ
  | TES_Deref_Expr : forall Σ Σ' r la rk T u,
      expr_as_place r = None ->
      typed_env_structural env Ω n Σ r (MkTy u (TRef la rk T)) Σ' ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EDeref r) T Σ'
  | TES_If : forall Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3,
      typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
      ty_core T_cond = TBooleans ->
      typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
      typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      typed_env_structural env Ω n Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)) Σ4
  | TES_Call : forall Σ Σ' fname fdef args σ,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      typed_args_env_structural env Ω n Σ args (apply_lt_params σ (fn_params fdef)) Σ' ->
      Forall (fun '(a, b) => outlives Ω a b) (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_structural env Ω n Σ (ECall fname args) (apply_lt_ty σ (fn_ret fdef)) Σ'
  | TES_CallExpr_Fn : forall Σ Σ1 Σ' callee args u param_tys ret,
      typed_env_structural env Ω n Σ callee (MkTy u (TFn param_tys ret)) Σ1 ->
      typed_args_env_structural env Ω n Σ1 args (params_of_tys param_tys) Σ' ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) ret Σ'
  | TES_CallExpr_Forall : forall Σ Σ1 Σ' callee args u m bounds body param_tys ret σ,
      typed_env_structural env Ω n Σ callee (MkTy u (TForall m bounds body)) Σ1 ->
      ty_core body = TFn param_tys ret ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) (open_bound_ty σ ret) Σ'
with typed_args_env_structural (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> list expr -> list param -> sctx -> Prop :=
  | TESArgs_Nil : forall Σ,
      typed_args_env_structural env Ω n Σ [] [] Σ
  | TESArgs_Cons : forall Σ Σ1 Σ2 e es p ps T_e,
      typed_env_structural env Ω n Σ e T_e Σ1 ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_env_structural env Ω n Σ1 es ps Σ2 ->
      typed_args_env_structural env Ω n Σ (e :: es) (p :: ps) Σ2
with typed_fields_env_structural
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> sctx -> list (string * expr) -> list field_def -> sctx -> Prop :=
  | TESFields_Nil : forall lts args Σ fields,
      typed_fields_env_structural env Ω n lts args Σ fields [] Σ
  | TESFields_Cons : forall lts args Σ Σ1 Σ2 fields f rest e_field T_field,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_structural env Ω n Σ e_field T_field Σ1 ->
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) = true ->
      typed_fields_env_structural env Ω n lts args Σ1 fields rest Σ2 ->
      typed_fields_env_structural env Ω n lts args Σ fields (f :: rest) Σ2.

Inductive borrow_ok_env_structural (env : global_env)
    : path_borrow_state -> ctx -> expr -> path_borrow_state -> Prop :=
  | BOES_Unit : forall PBS Γ,
      borrow_ok_env_structural env PBS Γ EUnit PBS
  | BOES_Lit : forall PBS Γ l,
      borrow_ok_env_structural env PBS Γ (ELit l) PBS
  | BOES_Var : forall PBS Γ x,
      borrow_ok_env_structural env PBS Γ (EVar x) PBS
  | BOES_Fn : forall PBS Γ fname,
      borrow_ok_env_structural env PBS Γ (EFn fname) PBS
  | BOES_Place : forall PBS Γ p,
      borrow_ok_env_structural env PBS Γ (EPlace p) PBS
  | BOES_Struct : forall PBS PBS' Γ sname lts args fields,
      borrow_ok_fields_env_structural env PBS Γ fields PBS' ->
      borrow_ok_env_structural env PBS Γ (EStruct sname lts args fields) PBS'
  | BOES_BorrowShared : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_mut x path PBS = false ->
      borrow_ok_env_structural env PBS Γ (EBorrow RShared p) (PBShared x path :: PBS)
  | BOES_BorrowUnique : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ (EBorrow RUnique p) (PBMut x path :: PBS)
  | BOES_Write : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ e_new PBS' ->
      borrow_ok_env_structural env PBS Γ (EReplace p e_new) PBS'
  | BOES_Assign : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ e_new PBS' ->
      borrow_ok_env_structural env PBS Γ (EAssign p e_new) PBS'
  | BOES_Deref : forall PBS PBS' Γ e,
      match expr_ref_root e with
      | Some r => pbs_has_mut r [] PBS = false
      | None => True
      end ->
      borrow_ok_env_structural env PBS Γ e PBS' ->
      borrow_ok_env_structural env PBS Γ (EDeref e) PBS'
  | BOES_Drop : forall PBS PBS' Γ e,
      borrow_ok_env_structural env PBS Γ e PBS' ->
      borrow_ok_env_structural env PBS Γ (EDrop e) PBS'
  | BOES_Let : forall PBS PBS1 PBS2 Γ m x T e1 e2,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 (ctx_add_b x T m Γ) e2 PBS2 ->
      borrow_ok_env_structural env PBS Γ (ELet m x T e1 e2)
        (pbs_remove_all (pbs_new_entries PBS PBS1) PBS2)
  | BOES_LetInfer : forall PBS PBS1 PBS2 Γ m x e1 e2,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 Γ e2 PBS2 ->
      borrow_ok_env_structural env PBS Γ (ELetInfer m x e1 e2)
        (pbs_remove_all (pbs_new_entries PBS PBS1) PBS2)
  | BOES_If : forall PBS PBS1 PBS2 PBS3 Γ e1 e2 e3,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 Γ e2 PBS2 ->
      borrow_ok_env_structural env PBS1 Γ e3 PBS3 ->
      PBS2 = PBS3 ->
      borrow_ok_env_structural env PBS Γ (EIf e1 e2 e3) PBS2
  | BOES_Call : forall PBS PBS' Γ fname args,
      borrow_ok_args_env_structural env PBS Γ args PBS' ->
      borrow_ok_env_structural env PBS Γ (ECall fname args) PBS'
  | BOES_CallExpr : forall PBS PBS1 PBS2 Γ callee args,
      borrow_ok_env_structural env PBS Γ callee PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ args PBS2 ->
      borrow_ok_env_structural env PBS Γ (ECallExpr callee args) PBS2
with borrow_ok_args_env_structural (env : global_env)
    : path_borrow_state -> ctx -> list expr -> path_borrow_state -> Prop :=
  | BOESArgs_Nil : forall PBS Γ,
      borrow_ok_args_env_structural env PBS Γ [] PBS
  | BOESArgs_Cons : forall PBS PBS1 PBS2 Γ e rest,
      borrow_ok_env_structural env PBS Γ e PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ rest PBS2 ->
      borrow_ok_args_env_structural env PBS Γ (e :: rest) PBS2
with borrow_ok_fields_env_structural (env : global_env)
    : path_borrow_state -> ctx -> list (string * expr) -> path_borrow_state -> Prop :=
  | BOESFields_Nil : forall PBS Γ,
      borrow_ok_fields_env_structural env PBS Γ [] PBS
  | BOESFields_Cons : forall PBS PBS1 PBS2 Γ name e rest,
      borrow_ok_env_structural env PBS Γ e PBS1 ->
      borrow_ok_fields_env_structural env PBS1 Γ rest PBS2 ->
      borrow_ok_fields_env_structural env PBS Γ ((name, e) :: rest) PBS2.

Definition typed_fn_env_structural (env : global_env) (f : fn_def) : Prop :=
  exists T_body Γ_out,
    typed_env_structural env (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (params_ctx (fn_params f)))
      (fn_body f) T_body (sctx_of_ctx Γ_out) /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_b (fn_params f) Γ_out = true.

Definition checked_fn_env_structural (env : global_env) (f : fn_def) : Prop :=
  typed_fn_env_structural env f /\
  exists PBS',
    borrow_ok_env_structural env [] (params_ctx (fn_params f)) (fn_body f) PBS'.
