From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping AlphaEnvStructural.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Root alpha-renaming relations and helpers                           *)
(* ------------------------------------------------------------------ *)

Lemma root_env_equiv_rename_lookup_forward :
  forall rho R Rr x roots,
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    root_env_lookup x R = Some roots ->
    exists rootsr,
      root_env_lookup (lookup_rename x rho) Rr = Some rootsr /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros rho R Rr x roots Heq Hnocoll Hlookup.
  assert (Hlookup_ren :
    root_env_lookup (lookup_rename x rho) (root_env_rename rho R) =
      Some (root_set_rename rho roots)).
  { eapply root_env_lookup_rename.
    - apply Hnocoll.
      eapply root_env_lookup_some_in_names. exact Hlookup.
    - exact Hlookup. }
  destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R)
    (lookup_rename x rho) (root_set_rename rho roots) Heq Hlookup_ren)
    as [rootsr [Hlookup_r Hroots]].
  exists rootsr. split.
  - exact Hlookup_r.
  - exact Hroots.
Qed.

Lemma root_env_equiv_rename_lookup_none_forward :
  forall rho R Rr x,
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_lookup x R = None ->
    root_env_lookup (lookup_rename x rho) Rr = None.
Proof.
  intros rho R Rr x Heq Hnocoll Hlookup.
  apply root_env_equiv_lookup_none_r with (R' := root_env_rename rho R).
  - exact Heq.
  - apply root_env_lookup_rename_none; assumption.
Qed.

Lemma root_env_rename_no_shadow_collision_on :
  forall rho R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R).
Proof.
  unfold root_env_no_shadow, rename_no_collision_on, rename_no_collision_for.
  intros rho R Hnodup Hnodup_r.
  rewrite root_env_rename_names in Hnodup_r.
  remember (root_env_names R) as names.
  clear Heqnames R.
  induction names as [| a rest IH]; intros x Hx y Hy Hneq Heq.
  - contradiction.
  - simpl in Hnodup, Hnodup_r, Hx, Hy.
    inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]; subst.
    inversion Hnodup_r as [| ? ? Hfa_notin Hnodup_r_tail]; subst.
    destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
    + subst. contradiction.
    + subst x.
      apply Hfa_notin.
      rewrite <- Heq.
      apply (in_map (fun z => lookup_rename z rho)). exact Hy.
    + subst y.
      apply Hfa_notin.
      rewrite Heq.
      apply (in_map (fun z => lookup_rename z rho)). exact Hx.
    + eapply IH.
      * exact Hnodup_tail.
      * exact Hnodup_r_tail.
      * exact Hx.
      * exact Hy.
      * exact Hneq.
      * exact Heq.
Qed.

Lemma root_sets_union_rename_equiv :
  forall rho roots rootsr,
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots) ->
    root_set_equiv (root_sets_union rootsr)
      (root_set_rename rho (root_sets_union roots)).
Proof.
  intros rho roots.
  induction roots as [| roots_hd roots_tl IH]; intros rootsr Hforall.
  - inversion Hforall; subst. apply root_set_equiv_refl.
  - simpl in Hforall |- *.
    destruct rootsr as [| rootsr_hd rootsr_tl].
    { inversion Hforall. }
    inversion Hforall; subst.
    eapply root_set_equiv_trans.
    + apply root_set_union_equiv.
      * match goal with
        | H : root_set_equiv rootsr_hd (root_set_rename rho roots_hd) |- _ =>
            exact H
        end.
      * apply IH.
        match goal with
        | H : Forall2 root_set_equiv rootsr_tl
              (map (root_set_rename rho) roots_tl) |- _ =>
            exact H
        end.
    + apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma root_env_equiv_update_rename_union :
  forall rho R Rr x roots_old roots_new roots_oldr roots_newr,
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv roots_oldr (root_set_rename rho roots_old) ->
    root_set_equiv roots_newr (root_set_rename rho roots_new) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_equiv
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr)
      (root_env_rename rho
        (root_env_update x (root_set_union roots_old roots_new) R)).
Proof.
  intros rho R Rr x roots_old roots_new roots_oldr roots_newr
    HRr Hroots_old Hroots_new Hnocoll.
  rewrite root_env_rename_update.
  - apply root_env_equiv_update.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_union_rename_equiv.
    + exact HRr.
  - exact Hnocoll.
Qed.

Lemma root_env_equiv_remove_rename :
  forall rho R Rr x,
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_equiv
      (root_env_remove (lookup_rename x rho) Rr)
      (root_env_rename rho (root_env_remove x R)).
Proof.
  intros rho R Rr x HnsR HnsRr HRr Hnocoll_on Hnocoll.
  rewrite root_env_rename_remove.
  - apply root_env_equiv_remove.
    + exact HnsRr.
    + apply root_env_rename_no_shadow.
      * exact HnsR.
      * exact Hnocoll_on.
    + exact HRr.
  - exact Hnocoll.
Qed.

Inductive typed_env_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERS_Unit : forall R Σ,
      typed_env_roots_shadow_safe env Ω n R Σ EUnit
        (MkTy UUnrestricted TUnits) Σ R []
  | TERS_LitInt : forall R Σ i,
      typed_env_roots_shadow_safe env Ω n R Σ (ELit (LInt i))
        (MkTy UUnrestricted TIntegers) Σ R []
  | TERS_LitFloat : forall R Σ f,
      typed_env_roots_shadow_safe env Ω n R Σ (ELit (LFloat f))
        (MkTy UUnrestricted TFloats) Σ R []
  | TERS_LitBool : forall R Σ b,
      typed_env_roots_shadow_safe env Ω n R Σ (ELit (LBool b))
        (MkTy UUnrestricted TBooleans) Σ R []
  | TERS_Var_Copy : forall R Σ x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ R roots
  | TERS_Var_Move : forall R Σ Σ' x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R roots
  | TERS_Place_Copy : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ R roots
  | TERS_Place_Move : forall R Σ Σ' p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ' R roots
  | TERS_Call : forall R R' Σ Σ' fname fdef args σ arg_roots,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_roots_shadow_safe env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => Lifetime.outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECall fname args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TERS_CallGeneric :
      forall R R' Σ Σ' fname fdef (type_args : list Ty) args σ arg_roots,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_roots_shadow_safe env Ω n R Σ args
        (apply_lt_params σ
          (apply_type_params type_args (fn_params fdef))) Σ' R' arg_roots ->
      Forall (fun '(a, b) => Lifetime.outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallGeneric fname type_args args)
        (apply_lt_ty σ (subst_type_params_ty type_args (fn_ret fdef)))
        Σ' R' (root_sets_union arg_roots)
  | TERS_Fn : forall R Σ fname fdef,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_env_roots_shadow_safe env Ω n R Σ (EFn fname)
        (fn_value_ty fdef) Σ R []
  | TERS_MakeClosure : forall R Σ fname fdef captures env_lt captured_tys,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) =
        infer_ok (env_lt, captured_tys) ->
      typed_env_roots_shadow_safe env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty_at env_lt fdef captured_tys) Σ R []
  | TERS_MakeClosure_Static : forall R Σ fname fdef captures captured_tys,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx env Ω Σ captures (fn_captures fdef) =
        infer_ok captured_tys ->
      typed_env_roots_shadow_safe env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty fdef captured_tys) Σ R []
  | TERS_CallExpr_MakeClosure : forall R R' Σ Σ' fname fdef captures
      env_lt captured_tys args σ arg_roots,
      In fdef (Program.env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_roots_shadow_safe env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => Lifetime.outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TERS_CallExpr_Fn : forall R R1 R' Σ Σ1 Σ' callee args u
        param_tys ret arg_roots roots_callee,
      (forall fname caps, callee <> EMakeClosure fname caps) ->
      typed_env_roots_shadow_safe env Ω n R Σ callee
        (MkTy u (TFn param_tys ret)) Σ1 R1 roots_callee ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 args
        (params_of_tys param_tys) Σ' R' arg_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args) ret
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERS_CallExpr_Closure : forall R R1 R' Σ Σ1 Σ' callee args u
        env_lt param_tys ret arg_roots roots_callee,
      (forall fname caps, callee <> EMakeClosure fname caps) ->
      typed_env_roots_shadow_safe env Ω n R Σ callee
        (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 args
        (params_of_tys param_tys) Σ' R' arg_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args) ret
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERS_CallExpr_TypeForall : forall R R1 R' Σ Σ1 Σ' callee args u
        type_params bounds body_ty param_tys ret_inner type_args arg_roots roots_callee,
      (forall fname caps, callee <> EMakeClosure fname caps) ->
      typed_env_roots_shadow_safe env Ω n R Σ callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Σ' R' arg_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args)
        (subst_type_params_ty type_args ret_inner)
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERS_CallExpr_MixedForall : forall R R1 R' Σ Σ1 Σ' callee args u u_body
      m bounds type_params type_bounds body_ty param_tys ret σ type_args
      arg_roots roots_callee,
      (forall fname caps, callee <> EMakeClosure fname caps) ->
      typed_env_roots_shadow_safe env Ω n R Σ callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body_ty))))
        Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds σ type_bounds) type_args = None ->
      contains_lbound_ty (open_bound_ty σ (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 args
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys)))
        Σ' R' arg_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args)
        (open_bound_ty σ (subst_type_params_ty type_args ret))
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERS_CallExpr_Forall_Fn : forall R R1 R' Σ Σ1 Σ' callee args u
      m bounds body_ty param_tys ret σ arg_roots roots_callee,
      (forall fname caps, callee <> EMakeClosure fname caps) ->
      typed_env_roots_shadow_safe env Ω n R Σ callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args)
        (open_bound_ty σ ret) Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERS_CallExpr_Forall_Closure : forall R R1 R' Σ Σ1 Σ' callee args u
      m bounds body_ty env_lt param_tys ret σ arg_roots roots_callee,
      (forall fname caps, callee <> EMakeClosure fname caps) ->
      typed_env_roots_shadow_safe env Ω n R Σ callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TClosure env_lt param_tys ret ->
      contains_lbound_lifetime (open_bound_lifetime σ env_lt) = false ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args)
        (open_bound_ty σ ret) Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERS_Struct : forall R R' Σ Σ' sname lts args fields sdef roots,
      Program.lookup_struct sname env = Some sdef ->
      Datatypes.length lts = Program.struct_lifetimes sdef ->
      Datatypes.length args = Program.struct_type_params sdef ->
      check_struct_bounds env (Program.struct_bounds sdef) args = None ->
      typed_fields_roots_shadow_safe env Ω n lts args R Σ fields
        (Program.struct_fields sdef) Σ' R' roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ' R' roots
  | TERS_Enum : forall R R' Σ Σ' enum_name variant_name lts args payloads
      edef vdef payload_roots,
      Program.lookup_enum enum_name env = Some edef ->
      Program.lookup_enum_variant variant_name (Program.enum_variants edef) =
        Some vdef ->
      Datatypes.length lts = Program.enum_lifetimes edef ->
      Datatypes.length args = Program.enum_type_params edef ->
      check_struct_bounds env (Program.enum_bounds edef) args = None ->
      typed_args_roots_shadow_safe env Ω n R Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args)
            (Program.enum_variant_fields vdef))) Σ' R' payload_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EEnum enum_name variant_name lts args payloads)
        (instantiate_enum_ty edef lts args) Σ' R'
        (root_sets_union payload_roots)
  | TERS_Match : forall R R1 R_payload R_head_payload R_out
        Σ Σ1 Σ_head_payload Σ_head Σ_tail Γ_out scrut branches
        enum_name lts args edef v_head v_tail e_head T_scrut T_head Ts_tail
        binders_head ps_head roots_scrut roots_head roots_tail,
      typed_env_roots_shadow_safe env Ω n R Σ scrut T_scrut Σ1 R1 roots_scrut ->
      ty_core T_scrut = TEnum enum_name lts args ->
      Program.lookup_enum enum_name env = Some edef ->
      Datatypes.length lts = Program.enum_lifetimes edef ->
      Datatypes.length args = Program.enum_type_params edef ->
	      check_struct_bounds env (Program.enum_bounds edef) args = None ->
	      first_unknown_variant_branch branches (Program.enum_variants edef) = None ->
	      Program.enum_variants edef = v_head :: v_tail ->
	      lookup_expr_branch_binders (Program.enum_variant_name v_head) branches = Some binders_head ->
	      match_payload_params binders_head lts args v_head = infer_ok ps_head ->
      params_names_nodup_b ps_head = true ->
      ctx_lookup_params_none_b ps_head Σ1 = true ->
      root_env_lookup_params_none_b ps_head R1 = true ->
      lookup_expr_branch (Program.enum_variant_name v_head) branches = Some e_head ->
      R_payload = root_env_add_params_roots_same ps_head roots_scrut R1 ->
      typed_env_roots_shadow_safe env Ω n R_payload (sctx_add_params ps_head Σ1)
        e_head T_head Σ_head_payload R_head_payload roots_head ->
      params_ok_sctx_b env ps_head Σ_head_payload = true ->
      roots_exclude_params ps_head roots_head ->
      R_out = root_env_remove_match_params ps_head R_head_payload ->
      root_env_excludes_params ps_head R_out ->
      Σ_head = sctx_remove_params ps_head Σ_head_payload ->
      typed_match_tail_roots_shadow_safe env Ω n lts args R1 roots_scrut Σ1 branches v_tail
        (ty_core T_head) R_out Σ_tail Ts_tail roots_tail ->
      ctx_merge_many (ctx_of_sctx Σ_head) (map ctx_of_sctx Σ_tail) =
        Some Γ_out ->
      typed_env_roots_shadow_safe env Ω n R Σ (EMatch scrut branches)
        (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head))
        (sctx_of_ctx Γ_out) R_out (root_sets_union (roots_head :: roots_tail))
  | TERS_Let : forall R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2
      roots1 roots2,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      ty_compatible_b Ω T1 T = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots_shadow_safe env Ω n R Σ (ELet m x T e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TERS_LetInfer : forall R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2
      roots1 roots2,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots_shadow_safe env Ω n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TERS_Drop : forall R R' Σ Σ' e T roots,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EDrop e)
        (MkTy UUnrestricted TUnits) Σ' R' []
  | TERS_Replace_Path : forall R R1 Σ Σ1 Σ2 p e_new T_old T_new
      x path roots_result roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      root_env_lookup x R = Some roots_result ->
      typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new) T_old Σ2
        (root_env_update x (root_set_union roots_old roots_new) R1)
        roots_result
  | TERS_Replace_Resolved : forall R R1 Σ Σ1 p e_new T_old T_new
      roots_result x roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = None ->
      place_resolved_write_target R p = Some x ->
      root_env_lookup x R = Some roots_result ->
      writable_place_env_structural env Σ p ->
      typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new) T_old Σ1
        (root_env_update x (root_set_union roots_old roots_new) R1)
        roots_result
  | TERS_Assign_Path : forall R R1 Σ Σ' p e_new T_old T_new
      x path roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
        (MkTy UUnrestricted TUnits) Σ'
        (root_env_update x (root_set_union roots_old roots_new) R1) []
  | TERS_Assign_Resolved : forall R R1 Σ Σ' p e_new T_old T_new
      x roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = None ->
      place_resolved_write_target R p = Some x ->
      writable_place_env_structural env Σ p ->
      typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
        (MkTy UUnrestricted TUnits) Σ'
        (root_env_update x (root_set_union roots_old roots_new) R1) []
  | TERS_BorrowShared : forall R Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_roots_shadow_safe env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (Lifetime.LVar n) RShared T)) Σ R
        (root_of_place p)
  | TERS_BorrowShared_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_borrow_roots R p = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (Lifetime.LVar n) RShared T)) Σ R roots
  | TERS_BorrowUnique : forall R Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_roots_shadow_safe env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (Lifetime.LVar n) RUnique T)) Σ R [RStore x]
  | TERS_BorrowUnique_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_borrow_roots R p = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (Lifetime.LVar n) RUnique T)) Σ R roots
  | TERS_DerefBorrowShared : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EDeref (EBorrow RShared p)) T Σ R roots
  | TERS_DerefBorrowShared_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = None ->
      place_root_lookup R p = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EDeref (EBorrow RShared p)) T Σ R roots
  | TERS_DerefBorrowUnique : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      root_env_lookup x R = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EDeref (EBorrow RUnique p)) T Σ R roots
  | TERS_DerefBorrowUnique_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_root_lookup R p = Some roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (EDeref (EBorrow RUnique p)) T Σ R roots
  | TERS_If : forall R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3
      T_cond T2 T3 roots_cond roots2 roots3,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond ->
      ty_core T_cond = TBooleans ->
      typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
      typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      root_env_equiv R2 R3 ->
      typed_env_roots_shadow_safe env Ω n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        Σ4 R2 (root_set_union roots2 roots3)
with typed_args_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param -> sctx -> root_env ->
      list root_set -> Prop :=
  | TERSArgs_Nil : forall R Σ,
      typed_args_roots_shadow_safe env Ω n R Σ [] [] Σ R []
  | TERSArgs_Cons : forall R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots
      roots_rest,
      typed_env_roots_shadow_safe env Ω n R Σ e T_e Σ1 R1 roots ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_roots_shadow_safe env Ω n R1 Σ1 es ps Σ2 R2 roots_rest ->
      typed_args_roots_shadow_safe env Ω n R Σ (e :: es) (p :: ps)
        Σ2 R2 (roots :: roots_rest)
with typed_fields_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : list Lifetime.lifetime -> list Ty -> root_env -> sctx ->
      list (string * expr) -> list Program.field_def -> sctx -> root_env ->
      root_set -> Prop :=
  | TERSFields_Nil : forall lts args R Σ fields,
      typed_fields_roots_shadow_safe env Ω n lts args R Σ fields []
        Σ R []
  | TERSFields_Cons : forall lts args R R1 R2 Σ Σ1 Σ2 fields f rest
      e_field T_field roots_field roots_rest,
      lookup_field_b (Program.field_name f) fields = Some e_field ->
      typed_env_roots_shadow_safe env Ω n R Σ e_field T_field Σ1 R1
        roots_field ->
      ty_compatible_b Ω T_field (Program.instantiate_struct_field_ty lts args f) =
        true ->
      typed_fields_roots_shadow_safe env Ω n lts args R1 Σ1 fields rest
        Σ2 R2 roots_rest ->
      typed_fields_roots_shadow_safe env Ω n lts args R Σ fields (f :: rest)
        Σ2 R2 (root_set_union roots_field roots_rest)
with typed_match_tail_roots_shadow_safe
    (env : Program.global_env) (Ω : Lifetime.outlives_ctx) (n : nat)
    : list Lifetime.lifetime -> list Ty -> root_env -> root_set -> sctx ->
      list (string * list ident * expr) -> list Program.enum_variant_def ->
      TypeCore Ty -> root_env -> list sctx -> list Ty -> list root_set -> Prop :=
  | TERSMatchTail_Nil : forall lts args R roots_scrut Σ branches expected_core R_out,
      typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches []
        expected_core R_out [] [] []
	  | TERSMatchTail_Cons : forall R R_payload Rv_payload Rv Σ branches v rest e T
	      Σv_payload Σv R_out roots Σs Ts rootss expected_core
	      binders ps lts args roots_scrut,
	      lookup_expr_branch_binders (Program.enum_variant_name v) branches = Some binders ->
	      match_payload_params binders lts args v = infer_ok ps ->
      params_names_nodup_b ps = true ->
      ctx_lookup_params_none_b ps Σ = true ->
      root_env_lookup_params_none_b ps R = true ->
      lookup_expr_branch (Program.enum_variant_name v) branches = Some e ->
      R_payload = root_env_add_params_roots_same ps roots_scrut R ->
      typed_env_roots_shadow_safe env Ω n R_payload (sctx_add_params ps Σ)
        e T Σv_payload Rv_payload roots ->
      params_ok_sctx_b env ps Σv_payload = true ->
      roots_exclude_params ps roots ->
      Rv = root_env_remove_match_params ps Rv_payload ->
      root_env_excludes_params ps Rv ->
      Σv = sctx_remove_params ps Σv_payload ->
      ty_core T = expected_core ->
      root_env_equiv Rv R_out ->
      typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches rest
        expected_core R_out Σs Ts rootss ->
      typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches (v :: rest)
        expected_core R_out (Σv :: Σs) (T :: Ts) (roots :: rootss).

Scheme typed_env_roots_shadow_safe_ind' :=
  Induction for typed_env_roots_shadow_safe Sort Prop
with typed_args_roots_shadow_safe_ind' :=
  Induction for typed_args_roots_shadow_safe Sort Prop
with typed_fields_roots_shadow_safe_ind' :=
  Induction for typed_fields_roots_shadow_safe Sort Prop
with typed_match_tail_roots_shadow_safe_ind' :=
  Induction for typed_match_tail_roots_shadow_safe Sort Prop.
Combined Scheme typed_roots_shadow_safe_ind
  from typed_env_roots_shadow_safe_ind',
    typed_args_roots_shadow_safe_ind',
    typed_fields_roots_shadow_safe_ind',
    typed_match_tail_roots_shadow_safe_ind'.

Lemma typed_roots_shadow_safe_roots :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss).
Proof.
  intros env Ω n.
  apply typed_roots_shadow_safe_ind; intros; subst; try solve [econstructor; eauto].
  all: try (econstructor; eauto).
Qed.

Lemma typed_env_roots_shadow_safe_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots H.
  exact (proj1 (typed_roots_shadow_safe_roots env Ω n)
    R Σ e T Σ' R' roots H).
Qed.

Lemma typed_args_roots_shadow_safe_roots :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots H.
  exact (proj1 (proj2 (typed_roots_shadow_safe_roots env Ω n))
    R Σ args ps Σ' R' roots H).
Qed.

Lemma typed_fields_roots_shadow_safe_roots :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots H.
  exact (proj1 (proj2 (proj2 (typed_roots_shadow_safe_roots env Ω n)))
    lts args R Σ fields defs Σ' R' roots H).
Qed.

Lemma typed_match_tail_roots_shadow_safe_roots :
  forall env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss.
Proof.
  intros env Ω n lts args R roots_scrut Σ branches variants expected_core
    R_out Σs Ts rootss H.
  exact (proj2 (proj2 (proj2 (typed_roots_shadow_safe_roots env Ω n)))
    lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts
    rootss H).
Qed.

Lemma alpha_rename_expr_is_make_closure_inv :
  forall rho used e fn cs used',
    alpha_rename_expr rho used e = (EMakeClosure fn cs, used') ->
    exists fn0 cs0, e = EMakeClosure fn0 cs0.
Proof.
  intros rho used e fn cs used' Hrename.
  destruct e.
  - (* EUnit *) simpl in Hrename. congruence.
  - (* ELit *) simpl in Hrename. congruence.
  - (* EVar *) simpl in Hrename. congruence.
  - (* ELet m i t e1 e2 *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e1) as [e1' u1] eqn:He1.
    cbv zeta in Hrename.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ u1)) :: rho)
      (fresh_ident i (i :: free_vars_expr e2 ++ u1) :: i :: free_vars_expr e2 ++ u1)
      e2) as [e2' u3] eqn:He2.
    congruence.
  - (* ELetInfer m i e1 e2 *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e1) as [e1' u1] eqn:He1.
    cbv zeta in Hrename.
    destruct (alpha_rename_expr
      ((i, fresh_ident i (i :: free_vars_expr e2 ++ u1)) :: rho)
      (fresh_ident i (i :: free_vars_expr e2 ++ u1) :: i :: free_vars_expr e2 ++ u1)
      e2) as [e2' u3] eqn:He2.
    congruence.
  - (* EFn *) simpl in Hrename. congruence.
  - (* EMakeClosure fn0 cs0 *) eexists. eexists. reflexivity.
  - (* EPlace *) simpl in Hrename. congruence.
  - (* ECall fn0 args *)
    simpl in Hrename.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | nil => (nil, used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr rho used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used l) as [args' u'] eqn:Hargs.
    congruence.
  - (* ECallGeneric fn0 tys args *)
    simpl in Hrename.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | nil => (nil, used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr rho used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used l0) as [args' u'] eqn:Hargs.
    congruence.
  - (* ECallExpr callee args *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e) as [c' u1] eqn:Hcallee.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | nil => (nil, used0)
        | arg :: rest =>
            let (arg', used1') := alpha_rename_expr rho used0 arg in
            let (rest', used2) := go used1' rest in
            (arg' :: rest', used2)
        end) u1 l) as [args' u'] eqn:Hargs.
    congruence.
  - (* EStruct name lts tys fields *)
    simpl in Hrename.
    destruct ((fix go (used0 : list ident) (fields0 : list (string * expr))
        : list (string * expr) * list ident :=
        match fields0 with
        | nil => (nil, used0)
        | (fname, fe) :: rest =>
            let (fe', used1) := alpha_rename_expr rho used0 fe in
            let (rest', used2) := go used1 rest in
            ((fname, fe') :: rest', used2)
        end) used l1) as [fields' u'] eqn:Hfields.
    congruence.
  - (* EEnum enum_name variant_name lts tys payloads *)
    simpl in Hrename.
    destruct ((fix go (used0 : list ident) (payloads0 : list expr)
        : list expr * list ident :=
        match payloads0 with
        | nil => (nil, used0)
        | ep :: rest =>
            let (ep', used1) := alpha_rename_expr rho used0 ep in
            let (rest', used2) := go used1 rest in
            (ep' :: rest', used2)
        end) used l1) as [payloads' u'] eqn:Hpayloads.
    congruence.
  - (* EMatch scrut branches *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e) as [scrut' u1] eqn:Hscrut.
    destruct ((fix go (used0 : list ident)
        (branches0 : list (string * list ident * expr))
        : list (string * list ident * expr) * list ident :=
        match branches0 with
        | nil => (nil, used0)
        | (variant_name, binders, eb) :: rest =>
            let binder_seed := binders ++ free_vars_expr eb ++ used0 in
            let '(binders', rho_branch, used1') :=
              alpha_rename_idents rho binder_seed binders in
            let (eb', used2') := alpha_rename_expr rho_branch used1' eb in
            let (rest', used3) := go used2' rest in
            ((variant_name, binders', eb') :: rest', used3)
        end) u1 l) as [br' u'] eqn:Hbr.
    congruence.
  - (* EReplace p e *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e) as [e' u'] eqn:He.
    congruence.
  - (* EAssign p e *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e) as [e' u'] eqn:He.
    congruence.
  - (* EBorrow *) simpl in Hrename. congruence.
  - (* EDeref e *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e) as [e' u'] eqn:He.
    congruence.
  - (* EDrop e *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e) as [e' u'] eqn:He.
    congruence.
  - (* EIf e1 e2 e3 *)
    simpl in Hrename.
    destruct (alpha_rename_expr rho used e1) as [e1' u1] eqn:He1.
    destruct (alpha_rename_expr rho u1 e2) as [e2' u2] eqn:He2.
    destruct (alpha_rename_expr rho u2 e3) as [e3' u3] eqn:He3.
    congruence.
Qed.


Theorem typed_roots_shadow_safe_instantiate_fresh_mutual :
  forall env Ω n rho,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_env_roots_shadow_safe env Ω n R0 Σ e T Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_args_roots_shadow_safe env Ω n R0 Σ args ps Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        Forall2 root_set_equiv roots0
          (map (root_set_instantiate rho) roots)) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_fields_roots_shadow_safe env Ω n lts args R0 Σ fields defs
          Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_subst_images_exclude_names (match_branches_local_store_names branches) rho ->
    forall roots_scrut0 R0 R0_out,
      root_set_equiv roots_scrut0 (root_set_instantiate rho roots_scrut) ->
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0_out ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      root_env_equiv R0_out (root_env_instantiate rho R_out) ->
      exists rootss0,
        typed_match_tail_roots_shadow_safe env Ω n lts args R0 roots_scrut0 Σ branches variants
          expected_core R0_out Σs Ts rootss0 /\
        Forall2 root_set_equiv rootss0
          (map (root_set_instantiate rho) rootss)).
Proof.
  intros env Ω n rho.
  apply typed_roots_shadow_safe_ind.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ i Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ f Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ b Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ x T roots Hplace Husage Hlookup Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Var_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' x T roots Hplace Husage Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Var_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Place_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' p T x path roots Hplace Husage Hpath Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_Place_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R' Σ Σ' fname fdef args σ arg_roots Hin Hfname Hcaps
      Htypeparams Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TERS_Call; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R' Σ Σ' fname fdef type_args args σ arg_roots Hin Hfname
      Hcaps Hlen Hbounds Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_generic in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TERS_CallGeneric; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R Σ fname fdef Hin Hfname Hcaps Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TERS_Fn; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures env_lt captured_tys Hin Hfname Hcheck Hfresh
      R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TERS_MakeClosure; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures captured_tys Hin Hfname Hcheck Hfresh
      R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TERS_MakeClosure_Static; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R R' Σ Σ' fname fdef captures env_lt captured_tys args σ
      arg_roots Hin Hfname Hcheck Hargs IHargs Hout Hfresh R0 HnsR HnsR0
      HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [_ Hfresh_args].
    destruct (IHargs Hfresh_args R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TERS_CallExpr_MakeClosure; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u param_tys ret arg_roots roots_callee
      Hnot_mc Hcallee IHcallee Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hcallee.
      - exact HnsR. }
    destruct (IHargs Hfresh_args R10 Hns_R1 HnsR10 HR10)
      as [R20 [arg_roots0 [Hargs0 [HnsR20 [HR20 Harg_roots0]]]]].
    exists R20, (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TERS_CallExpr_Fn; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u env_lt param_tys ret arg_roots roots_callee
      Hnot_mc Hcallee IHcallee Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hcallee.
      - exact HnsR. }
    destruct (IHargs Hfresh_args R10 Hns_R1 HnsR10 HR10)
      as [R20 [arg_roots0 [Hargs0 [HnsR20 [HR20 Harg_roots0]]]]].
    exists R20, (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TERS_CallExpr_Closure; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u type_params bounds body_ty
      param_tys ret_inner type_args arg_roots roots_callee
      Hnot_mc Hcallee IHcallee Hbody Htf_bounds Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hcallee.
      - exact HnsR. }
    destruct (IHargs Hfresh_args R10 Hns_R1 HnsR10 HR10)
      as [R20 [arg_roots0 [Hargs0 [HnsR20 [HR20 Harg_roots0]]]]].
    exists R20, (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TERS_CallExpr_TypeForall; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u u_body m bounds type_params
      type_bounds body_ty param_tys ret σ type_args arg_roots roots_callee
      Hnot_mc Hcallee IHcallee Hbody Htf_bounds Hret_ok Hbounds_ok Hout
      Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hcallee.
      - exact HnsR. }
    destruct (IHargs Hfresh_args R10 Hns_R1 HnsR10 HR10)
      as [R20 [arg_roots0 [Hargs0 [HnsR20 [HR20 Harg_roots0]]]]].
    exists R20, (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TERS_CallExpr_MixedForall; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u m bounds body_ty param_tys ret σ
      arg_roots roots_callee Hnot_mc Hcallee IHcallee Hbody Hret_ok Hbounds_ok
      Hout Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hcallee.
      - exact HnsR. }
    destruct (IHargs Hfresh_args R10 Hns_R1 HnsR10 HR10)
      as [R20 [arg_roots0 [Hargs0 [HnsR20 [HR20 Harg_roots0]]]]].
    exists R20, (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TERS_CallExpr_Forall_Fn; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
       -- exact Hroots_callee0.
       -- eapply root_set_equiv_trans.
          ++ apply root_sets_union_equiv. exact Harg_roots0.
          ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u m bounds body_ty env_lt
      param_tys ret σ arg_roots roots_callee Hnot_mc Hcallee IHcallee Hbody
      Henv_ok Hret_ok Hbounds_ok Hout Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hcallee.
      - exact HnsR. }
    destruct (IHargs Hfresh_args R10 Hns_R1 HnsR10 HR10)
      as [R20 [arg_roots0 [Hargs0 [HnsR20 [HR20 Harg_roots0]]]]].
    exists R20, (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TERS_CallExpr_Forall_Closure; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
       -- exact Hroots_callee0.
       -- eapply root_set_equiv_trans.
          ++ apply root_sets_union_equiv. exact Harg_roots0.
          ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R' Σ Σ' sname lts args fields sdef roots Hlookup Hlen_lts
      Hlen_args Hbounds Hfields IHfields Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_struct in Hfresh.
    destruct (IHfields Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [Hfields0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', roots0. split; [| split; [| split]].
    + eapply TERS_Struct; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + exact Hroots0.
  - intros R R' Σ Σ' enum_name variant_name lts args payloads edef vdef
      payload_roots Hlookup Hvariant Hlen_lts Hlen_args Hbounds Hpayloads
      IHpayloads Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_enum in Hfresh.
    destruct (IHpayloads Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [payload_roots0 [Hpayloads0 [HnsR0' [HR0' Hpayload_roots0]]]]].
    exists R0', (root_sets_union payload_roots0). split; [| split; [| split]].
    + eapply TERS_Enum; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Hpayload_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R1 R_payload R_head_payload R_out Σ Σ1 Σ_head_payload
	      Σ_head Σ_tail Γ_out scrut branches enum_name lts args edef v_head
	      v_tail e_head T_scrut T_head Ts_tail binders_head ps_head roots_scrut
	      roots_head roots_tail Hscrut IHscrut Hcore Hlookup Hlen_lts Hlen_args
	      Hbounds Hunknown Hvariants
	      Hbinders_head Hpayload_head Hnodup_head Hctx_fresh_head Hroot_fresh_head
	      Hlookup_head HRpayload Hhead IHhead
      Hparams_ok_head Hroots_excl_head HRout Henv_excl_head HΣhead Htail
      IHtail Hmerge Hfresh R0 HnsR HnsR0 HR0.
    simpl in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_scrut Hfresh_branches].
    destruct (IHscrut Hfresh_scrut R0 HnsR HnsR0 HR0)
      as [R10 [roots_scrut0 [Hscrut0 [HnsR10 [HR10 Hroots_scrut0]]]]].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hscrut.
      - exact HnsR. }
    assert (Hfresh_R10 :
      root_env_lookup_params_none_b ps_head R10 = true).
    { eapply root_env_lookup_params_none_b_instantiate_equiv; eassumption. }
    assert (Hfresh_ps_head :
      root_subst_images_exclude_names (ctx_names (params_ctx ps_head)) rho).
    {
      rewrite (match_payload_params_names binders_head lts args v_head ps_head
        Hpayload_head).
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh_branches.
      - eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
    }
    assert (Hfresh_head :
      root_subst_images_exclude_names (expr_local_store_names e_head) rho).
    {
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh_branches.
      - eapply lookup_expr_branch_local_store_names_in; eassumption.
    }
    assert (HnsRpayload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    pose (Rpayload0 := root_env_add_params_roots_same ps_head roots_scrut0 R10).
    assert (HnsRpayload0 : root_env_no_shadow Rpayload0).
    { unfold Rpayload0. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (HRpayload0 :
      root_env_equiv Rpayload0 (root_env_instantiate rho R_payload)).
    { subst R_payload. unfold Rpayload0.
      eapply root_env_add_params_roots_same_instantiate_equiv; eauto. }
    destruct (IHhead Hfresh_head Rpayload0 HnsRpayload HnsRpayload0 HRpayload0)
      as [Rhead0 [roots_head0 [Hhead0 [HnsRhead0 [HRhead0 Hroots_head0]]]]].
    assert (HnsRhead_payload : root_env_no_shadow R_head_payload).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Hhead.
      - exact HnsRpayload. }
    pose (Rout0 := root_env_remove_match_params ps_head Rhead0).
    assert (HnsRout0 : root_env_no_shadow Rout0).
    { unfold Rout0. apply root_env_remove_match_params_no_shadow. exact HnsRhead0. }
    assert (HRout0 : root_env_equiv Rout0 (root_env_instantiate rho R_out)).
    { subst R_out. unfold Rout0.
      eapply root_env_remove_match_params_instantiate_equiv; eauto. }
    destruct (IHtail Hfresh_branches roots_scrut0 R10 Rout0 Hroots_scrut0
      HnsR1 HnsR10 HnsRout0 HR10 HRout0)
      as [roots_tail0 [Htail0 Hroots_tail0]].
    exists Rout0, (root_sets_union (roots_head0 :: roots_tail0)).
    split; [| split; [| split]].
    + eapply TERS_Match; eauto.
      * eapply roots_exclude_params_equiv_local.
        -- apply root_set_equiv_sym. exact Hroots_head0.
        -- eapply roots_exclude_params_instantiate_local; eassumption.
      * eapply root_env_excludes_params_equiv_local.
        -- apply root_env_equiv_sym. exact HRout0.
        -- eapply root_env_excludes_params_instantiate_local; eassumption.
    + exact HnsRout0.
    + exact HRout0.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv.
        simpl. constructor.
        -- exact Hroots_head0.
        -- exact Hroots_tail0.
      * apply root_set_equiv_sym.
        apply root_sets_instantiate_union_equiv.
  - intros R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hcompat Hlookup_none Hexcl_roots1 Hexcl_env1
      He2 IHe2 Hcheck Hexcl_roots2 Hexcl_env2 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TERS_Let.
      * exact He10.
      * exact Hcompat.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hlookup_none Hexcl_roots1 Hexcl_env1
      He2 IHe2 Hcheck Hexcl_roots2 Hexcl_env2 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TERS_LetInfer.
      * exact He10.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R' Σ Σ' e T roots He IHe Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [He0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', []. split; [| split; [| split]].
    + apply TERS_Drop with (T := T) (roots := roots0). exact He0.
    + exact HnsR0'.
    + exact HR0'.
    + apply root_set_equiv_refl.
  - intros R R1 Σ Σ1 Σ2 p e_new T_old T_new x path roots_result
      roots_old roots_new Hplace Hpath Hwritable Hlookup_result He_new IHe_new
      Hlookup_old Hcompat Havailable Hrestore Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_result_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots_result)).
    { apply root_env_lookup_instantiate. exact Hlookup_result. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots_result) HR0 Hlookup_result_inst)
      as [roots_result0 [Hlookup_result0 Hroots_result0]].
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      roots_result0.
    split; [| split; [| split]].
    + eapply TERS_Replace_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + exact Hroots_result0.
  - intros R R1 Σ Σ1 p e_new T_old T_new roots_result x roots_old roots_new
      Hplace Hpath Htarget Hlookup_result Hwritable He_new IHe_new Hlookup_old
      Hcompat Hfresh R0 HnsR HnsR0 HR0.
    assert (Htarget0 : place_resolved_write_target R0 p = Some x).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_target_instantiate. exact Htarget. }
    assert (Hlookup_result_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots_result)).
    { apply root_env_lookup_instantiate. exact Hlookup_result. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots_result) HR0 Hlookup_result_inst)
      as [roots_result0 [Hlookup_result0 Hroots_result0]].
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      roots_result0.
    split; [| split; [| split]].
    + eapply TERS_Replace_Resolved; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + exact Hroots_result0.
  - intros R R1 Σ Σ' p e_new T_old T_new x path roots_old roots_new
      Hplace Husage Hpath Hwritable He_new IHe_new Hlookup_old Hcompat
      Havailable Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      [].
    split; [| split; [| split]].
    + eapply TERS_Assign_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + apply root_set_equiv_refl.
  - intros R R1 Σ Σ' p e_new T_old T_new x roots_old roots_new
      Hplace Husage Hpath Htarget Hwritable He_new IHe_new
      Hlookup_old Hcompat Hfresh R0 HnsR HnsR0 HR0.
    assert (Htarget0 : place_resolved_write_target R0 p = Some x).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_target_instantiate. exact Htarget. }
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      [].
    split; [| split; [| split]].
    + eapply TERS_Assign_Resolved; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + apply root_set_equiv_refl.
  - intros R Σ p T Hplace Hfresh R0 HnsR HnsR0 HR0.
    exists R0, (root_of_place p). split; [| split; [| split]].
    + constructor. exact Hplace.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_root_of_place_equiv.
  - intros R Σ p T roots Hplace Hpath Hborrow Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_borrow_roots_indirect R p Hpath). exact Hborrow. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_BorrowShared_Indirect; eauto.
      rewrite (place_borrow_roots_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path Hplace Hpath Hmut Hfresh R0 HnsR HnsR0 HR0.
    exists R0, [RStore x]. split; [| split; [| split]].
    + eapply TERS_BorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_store_singleton_equiv.
  - intros R Σ p T roots Hplace Hpath Hunique Hborrow Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_borrow_roots_indirect R p Hpath). exact Hborrow. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_BorrowUnique_Indirect; eauto.
      rewrite (place_borrow_roots_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_DerefBorrowShared; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_root :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hlookup. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup_root. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_DerefBorrowShared_Indirect; eauto.
      rewrite (place_root_lookup_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hmut Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_DerefBorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots Hplace Husage Hpath Hunique Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_root :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hlookup. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup_root. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TERS_DerefBorrowUnique_Indirect; eauto.
      rewrite (place_root_lookup_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3
      roots_cond roots2 roots3 He1 IHe1 Hcond He2 IHe2 He3 IHe3 Hcore
      Hmerge HR23 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1)
      (expr_local_store_names e2 ++ expr_local_store_names e3) rho
      Hfresh) as [Hfresh1 Hfresh23].
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e2) (expr_local_store_names e3) rho
      Hfresh23) as [Hfresh2 Hfresh3].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots_cond0 [He10 [HnsR10 [HR10 Hroots_cond0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He1.
      - exact HnsR. }
    destruct (IHe2 Hfresh2 R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    destruct (IHe3 Hfresh3 R10 Hns_R1 HnsR10 HR10)
      as [R30 [roots30 [He30 [HnsR30 [HR30 Hroots30]]]]].
    exists R20, (root_set_union roots20 roots30). split; [| split; [| split]].
    + eapply TERS_If; eauto.
      eapply root_env_equiv_trans.
      * exact HR20.
      * eapply root_env_equiv_trans.
        -- apply root_env_equiv_instantiate. exact HR23.
        -- apply root_env_equiv_sym. exact HR30.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + constructor.
  - intros R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest
      He IHe Hcompat Hes IHes Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_args_cons_inv
      e es rho Hfresh) as [Hfresh_e Hfresh_es].
    destruct (IHe Hfresh_e R0 HnsR HnsR0 HR0)
      as [R10 [roots0 [He0 [HnsR10 [HR10 Hroots0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He.
      - exact HnsR. }
    destruct (IHes Hfresh_es R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hes0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (roots0 :: roots_rest0). split; [| split; [| split]].
    + eapply TERSArgs_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + constructor; assumption.
  - intros lts args R Σ fields Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros lts args R R1 R2 Σ Σ1 Σ2 fields f rest e_field T_field
      roots_field roots_rest Hlookup He_field IHe_field Hcompat Hfields IHfields
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hfresh_field :
      root_subst_images_exclude_names (expr_local_store_names e_field) rho).
    { unfold lookup_field_b in Hlookup.
      clear Hfields IHfields.
      induction fields as [| [field_name0 e0] fields IH]; simpl in *;
        try discriminate.
      destruct (String.eqb (Program.field_name f) field_name0) eqn:Hfield.
      - inversion Hlookup. subst e0.
        apply root_subst_images_exclude_names_app_inv in Hfresh.
        exact (proj1 Hfresh).
      - apply IH.
        + exact Hlookup.
        + apply root_subst_images_exclude_names_app_inv in Hfresh.
          exact (proj2 Hfresh). }
    destruct (IHe_field Hfresh_field R0 HnsR HnsR0 HR0)
      as [R10 [roots_field0 [He_field0 [HnsR10 [HR10 Hroots_field0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact He_field.
      - exact HnsR. }
    destruct (IHfields Hfresh R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hfields0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (root_set_union roots_field0 roots_rest0). split; [| split; [| split]].
    + eapply TERSFields_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros lts args R roots_scrut Σ branches expected_core R_out Hfresh
      roots_scrut0 R0 R0_out Hroots_scrut0 HnsR HnsR0 HnsR0_out HR0
      HR0_out.
    exists []. split.
    + constructor.
    + constructor.
	  - intros R R_payload Rv_payload Rv Σ branches v rest e T
	      Σv_payload Σv R_out roots Σs Ts rootss expected_core binders ps
	      lts args roots_scrut Hbinders Hpayload Hnodup
	      Hctx_fresh Hroot_fresh Hlookup HRpayload Htyped IHtyped Hparams_ok Hroots_excl HRv
      Henv_excl HΣv Hcore Heq_tail Htail IHtail Hfresh roots_scrut0
      R0 R0_out Hroots_scrut0 HnsR HnsR0 HnsR0_out HR0 HR0_out.
    assert (Hfresh_R0 : root_env_lookup_params_none_b ps R0 = true).
    { eapply root_env_lookup_params_none_b_instantiate_equiv; eassumption. }
    assert (Hfresh_ps :
      root_subst_images_exclude_names (ctx_names (params_ctx ps)) rho).
    {
      rewrite (match_payload_params_names binders lts args v ps Hpayload).
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh.
      - eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
    }
    assert (Hfresh_e :
      root_subst_images_exclude_names (expr_local_store_names e) rho).
    {
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh.
      - eapply lookup_expr_branch_local_store_names_in; eassumption.
    }
    assert (HnsRpayload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    pose (Rpayload0 := root_env_add_params_roots_same ps roots_scrut0 R0).
    assert (HnsRpayload0 : root_env_no_shadow Rpayload0).
    { unfold Rpayload0. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (HRpayload0 :
      root_env_equiv Rpayload0 (root_env_instantiate rho R_payload)).
    { subst R_payload. unfold Rpayload0.
      eapply root_env_add_params_roots_same_instantiate_equiv; eauto. }
    destruct (IHtyped Hfresh_e Rpayload0 HnsRpayload HnsRpayload0 HRpayload0)
      as [Rv_payload0 [roots0 [Htyped0 [Hns_payload0 [HR_payload0 Hroots0]]]]].
    assert (HnsRv_payload : root_env_no_shadow Rv_payload).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped.
      - exact HnsRpayload. }
    pose (Rv0 := root_env_remove_match_params ps Rv_payload0).
    assert (HnsRv0 : root_env_no_shadow Rv0).
    { unfold Rv0. apply root_env_remove_match_params_no_shadow. exact Hns_payload0. }
    assert (HRv0 : root_env_equiv Rv0 (root_env_instantiate rho Rv)).
    { subst Rv. unfold Rv0.
      eapply root_env_remove_match_params_instantiate_equiv; eauto. }
    destruct (IHtail Hfresh roots_scrut0 R0 R0_out Hroots_scrut0
      HnsR HnsR0 HnsR0_out HR0 HR0_out)
      as [rootss0 [Htail0 Hrootss0]].
    exists (roots0 :: rootss0). split.
    + eapply TERSMatchTail_Cons; eauto.
      * eapply roots_exclude_params_equiv_local.
        -- apply root_set_equiv_sym. exact Hroots0.
        -- eapply roots_exclude_params_instantiate_local; eassumption.
      * eapply root_env_excludes_params_equiv_local.
        -- apply root_env_equiv_sym. exact HRv0.
        -- eapply root_env_excludes_params_instantiate_local; eassumption.
      * eapply root_env_equiv_trans.
        -- exact HRv0.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_instantiate. exact Heq_tail.
           ++ apply root_env_equiv_sym. exact HR0_out.
    + simpl. constructor; assumption.
Qed.

Lemma typed_env_roots_shadow_safe_instantiate_fresh :
  forall env Ω n rho R Σ e T Σ' R' roots R0,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σ e T Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho R Σ e T Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (typed_roots_shadow_safe_instantiate_fresh_mutual env Ω n rho)
    R Σ e T Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_args_roots_shadow_safe_instantiate_fresh :
  forall env Ω n rho R Σ args ps Σ' R' roots R0,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_args_roots_shadow_safe env Ω n R0 Σ args ps Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      Forall2 root_set_equiv roots0 (map (root_set_instantiate rho) roots).
Proof.
  intros env Ω n rho R Σ args ps Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (typed_roots_shadow_safe_instantiate_fresh_mutual env Ω n rho))
    R Σ args ps Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_fields_roots_shadow_safe_instantiate_fresh :
  forall env Ω n rho lts args R Σ fields defs Σ' R' roots R0,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_fields_roots_shadow_safe env Ω n lts args R0 Σ fields defs
        Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho lts args R Σ fields defs Σ' R' roots R0
    Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (proj2 (typed_roots_shadow_safe_instantiate_fresh_mutual env Ω n rho)))
    lts args R Σ fields defs Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

