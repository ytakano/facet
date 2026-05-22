From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeReadinessFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition env_fns_root_shadow_summary_check_ready (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_summary env fdef.

Definition env_fns_root_shadow_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.

Definition callee_body_root_shadow_direct_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_provenance_summary env fdef \/
  exists fname args raw_body synthetic_body fcallee T_body Γ_out R_body roots_body,
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_provenance_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_direct_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_direct_call_provenance_summary env fdef.

Definition callee_body_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_direct_call_provenance_summary env fdef \/
  exists fname args raw_body synthetic_body fcallee T_body Γ_out R_body roots_body,
    fn_body fdef = raw_body /\
    local_fn_value_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_provenance_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_non_capturing_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_non_capturing_call_provenance_summary env fdef.

Definition callee_body_root_shadow_captured_callee_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) /\
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fdef) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef ++ fn_captures fdef) roots_body /\
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef) R_body.

Definition callee_hidden_capture_args_disjoint
    (callee : fn_def) (args : list expr) : Prop :=
  Forall
    (fun x => ~ In x (args_local_store_names args))
    (ctx_names (params_ctx (fn_captures callee))).

Inductive expr_root_shadow_captured_call_provenance_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> ctx -> expr -> Prop :=
  | ERSC_Provenance : forall R Γ e,
      provenance_ready_expr e ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ e
  | ERSC_DirectCall : forall R Γ e fname args synthetic_body fcallee
      T_body Γ_out R_body roots_body,
      direct_call_target_expr e = Some (fname, args, synthetic_body) ->
      synthetic_body = ECall fname args ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_body_root_shadow_provenance_summary env fcallee ->
      typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ)
        synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ e
  | ERSC_CapturedCall : forall R Γ e fname captures args fcallee
      env_lt captured_tys T_body Γ_out R_body roots_body,
      captured_call_target_expr e = Some (fname, captures, args) ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      fn_lifetimes fcallee = 0 ->
      callee_hidden_capture_args_disjoint fcallee args ->
      check_make_closure_captures_exact_sctx_with_env env Ω
        (sctx_of_ctx Γ) captures (fn_captures fcallee) =
        infer_ok (env_lt, captured_tys) ->
      NoDup (ctx_names (params_ctx (fn_params fcallee ++ fn_captures fcallee))) ->
      provenance_ready_expr (fn_body fcallee) ->
      typed_env_roots_shadow_safe env (fn_outlives fcallee)
        (fn_lifetimes fcallee)
        (initial_root_env_for_params
          (fn_params fcallee ++ fn_captures fcallee))
        (sctx_of_ctx (fn_body_ctx fcallee))
        (fn_body fcallee) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      ty_compatible_b (fn_outlives fcallee) T_body
        (fn_ret fcallee) = true ->
      roots_exclude_params (fn_params fcallee ++ fn_captures fcallee)
        roots_body ->
      root_env_excludes_params (fn_params fcallee ++ fn_captures fcallee)
        R_body ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ e
  | ERSC_If : forall R Γ e1 e2 e3 T_cond Γ1 R1 roots_cond,
      typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ)
        e1 T_cond (sctx_of_ctx Γ1) R1 roots_cond ->
      ty_core T_cond = TBooleans ->
      provenance_ready_expr e1 ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R1 Γ1 e2 ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R1 Γ1 e3 ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ
        (EIf e1 e2 e3).

Inductive expr_root_shadow_captured_call_provenance_summary_exact
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set ->
      Prop :=
  | ERSCE_Provenance : forall R Σ e T Σ' R' roots,
      provenance_ready_expr e ->
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots roots
  | ERSCE_DirectCall : forall R Σ e fname args synthetic_body fcallee
      T Σ' R' roots,
      direct_call_target_expr e = Some (fname, args, synthetic_body) ->
      synthetic_body = ECall fname args ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_body_root_shadow_provenance_summary env fcallee ->
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        synthetic_body T Σ' R' roots ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots roots
  | ERSCE_CapturedCall : forall R Σ fname captures args fcallee
      env_lt captured_tys T Σ' R' roots capture_roots
      T_body Γ_out R_body roots_body,
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      fn_lifetimes fcallee = 0 ->
      callee_hidden_capture_args_disjoint fcallee args ->
      check_make_closure_captures_exact_sctx_with_env env Ω Σ
        captures (fn_captures fcallee) = infer_ok (env_lt, captured_tys) ->
      NoDup (ctx_names (params_ctx (fn_params fcallee ++ fn_captures fcallee))) ->
      provenance_ready_expr (fn_body fcallee) ->
      typed_env_roots_shadow_safe env (fn_outlives fcallee)
        (fn_lifetimes fcallee)
        (initial_root_env_for_params
          (fn_params fcallee ++ fn_captures fcallee))
        (sctx_of_ctx (fn_body_ctx fcallee))
        (fn_body fcallee) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      ty_compatible_b (fn_outlives fcallee) T_body
        (fn_ret fcallee) = true ->
      roots_exclude_params (fn_params fcallee ++ fn_captures fcallee)
        roots_body ->
      root_env_excludes_params (fn_params fcallee ++ fn_captures fcallee)
        R_body ->
      capture_root_bound R captures (fn_captures fcallee) =
        Some capture_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallExpr (EMakeClosure fname captures) args) T Σ' R' roots ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ (ECallExpr (EMakeClosure fname captures) args)
        T Σ' R' roots (root_set_union roots capture_roots)
  | ERSCE_If : forall R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3
      T_cond T2 T3 roots_cond roots2 roots3 ret_roots2 ret_roots3,
      provenance_ready_expr e1 ->
      typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1
        roots_cond ->
      ty_core T_cond = TBooleans ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ret_roots2 ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ret_roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      root_env_equiv R2 R3 ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        (sctx_of_ctx Σ4) R2 (root_set_union roots2 roots3)
        (root_set_union ret_roots2 ret_roots3).

Lemma expr_root_shadow_captured_call_provenance_summary_exact_typed :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - exact H0.
  - exact H5.
  - exact H12.
  - eapply TERS_If; eauto.
Qed.

Definition callee_body_root_shadow_captured_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_non_capturing_call_provenance_summary env fdef \/
  (
  exists fname captures args fcallee env_lt captured_tys
      T_body Γ_out R_body roots_body,
    fn_body fdef = ECallExpr (EMakeClosure fname captures) args /\
    captured_call_target_expr (fn_body fdef) = Some (fname, captures, args) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    fn_lifetimes fcallee = 0 /\
    callee_hidden_capture_args_disjoint fcallee args /\
    check_make_closure_captures_exact_sctx_with_env env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee) = infer_ok (env_lt, captured_tys) /\
    callee_body_root_shadow_captured_callee_provenance_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body) \/
  (
  exists T_body Γ_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_captured_call_provenance_summary_exact env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body) \/
  (
  exists fname captures args m x T direct_body let_body fcallee
      env_lt captured_tys T_direct Γ_direct R_direct roots_direct
      T_let Γ_let R_let roots_let,
    fn_body fdef =
      ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args) /\
    local_captured_call_target_expr (fn_body fdef) =
      Some (fname, captures, args, m, x, T, direct_body, let_body) /\
    direct_body = ECallExpr (EMakeClosure fname captures) args /\
    let_body =
      ELet m x T (EMakeClosure fname captures) direct_body /\
    ty_usage T = UUnrestricted /\
    ~ In x captures /\
    ~ In x (ctx_names (params_ctx (fn_captures fcallee))) /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    fn_lifetimes fcallee = 0 /\
    callee_hidden_capture_args_disjoint fcallee args /\
    check_make_closure_captures_exact_sctx_with_env env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee) = infer_ok (env_lt, captured_tys) /\
    callee_body_root_shadow_captured_callee_provenance_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      direct_body T_direct (sctx_of_ctx Γ_direct) R_direct roots_direct /\
    ty_compatible_b (fn_outlives fdef) T_direct (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_direct /\
    root_env_excludes_params (fn_params fdef) R_direct /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      let_body T_let (sctx_of_ctx Γ_let) R_let roots_let).

Definition env_fns_root_shadow_captured_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_provenance_summary env fdef.
