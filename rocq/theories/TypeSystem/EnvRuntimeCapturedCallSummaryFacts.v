From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectFuelRuntimeFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Inductive expr_root_shadow_store_safe_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSS_Exact : forall R Σ e T Σ' R' roots ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Omega n R Σ e T Σ' R' roots ret_roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots
  | ERSS_FunctionValueCall : forall R Σ x args T_callee Gamma_callee
      R_callee roots_callee T Σ' R' roots,
      preservation_ready_args args ->
      infer_core_env_roots_shadow_safe env Omega n R (ctx_of_sctx Σ)
        (EVar x) = infer_ok
          (T_callee, Gamma_callee, R_callee, roots_callee) ->
      supported_non_type_generic_function_value_call_callee_shape T_callee ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExpr (EVar x) args) T Σ' R' roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ECallExpr (EVar x) args) T Σ' R' roots roots
  | ERSS_Let : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSS_If : forall R R1 R2 R3 Σ Σ1 Sigma2 Sigma3 Sigma4
      e1 e2 e3 T_cond T2 T3 roots_cond roots2 roots3 ret_roots2 ret_roots3,
      provenance_ready_expr e1 ->
      typed_env_roots_shadow_safe env Omega n R Σ e1 T_cond Σ1 R1
        roots_cond ->
      ty_core T_cond = TBooleans ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e2 T2 Sigma2 R2 roots2 ret_roots2 ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 ret_roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Sigma2) (ctx_of_sctx Sigma3) = Some Sigma4 ->
      R2 = R3 ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        (sctx_of_ctx Sigma4) R2 (root_set_union roots2 roots3)
        (root_set_union ret_roots2 ret_roots3).

Lemma expr_root_shadow_store_safe_summary_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Omega n R Σ e T Σ' R' roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
    exact H.
  - exact H2.
  - eapply TERS_Let; eauto.
  - subst R3. eapply TERS_If; eauto. apply root_env_equiv_refl.
Qed.
Definition callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname type_args args raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
    fn_body fdef = raw_body /\
    generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, synthetic_body) /\
    synthetic_body = ECallGeneric fname type_args args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    Datatypes.length type_args = fn_type_params fcallee /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fcallee) type_args = None /\
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcallee)) /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fcallee type_args /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_generic_direct_let_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname type_args args T_hidden raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
    fn_body fdef = raw_body /\
    let_bound_generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, T_hidden, synthetic_body) /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    Datatypes.length type_args = fn_type_params fcallee /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fcallee) type_args = None /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fcallee type_args /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_hidden (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_generic_direct_if_literal_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists b fname_then type_args_then args_then fname_else type_args_else
      args_else raw_body synthetic_body fthen felse T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    if_literal_generic_direct_call_target_expr raw_body =
      Some (b, fname_then, type_args_then, args_then,
        fname_else, type_args_else, args_else, synthetic_body) /\
    store_safe_function_value_call_args env args_then /\
    store_safe_function_value_call_args env args_else /\
    In fthen (env_fns env) /\
    fn_name fthen = fname_then /\
    In felse (env_fns env) /\
    fn_name felse = fname_else /\
    Datatypes.length type_args_then = fn_type_params fthen /\
    Datatypes.length type_args_else = fn_type_params felse /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fthen) type_args_then = None /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds felse) type_args_else = None /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fthen type_args_then /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 felse type_args_else /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_local_fn_value_generic_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists x fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    local_fn_value_call_target_expr_with_binder raw_body =
      Some (x, fname, args, synthetic_body) /\
    store_safe_function_value_call_args env args /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args) /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_captures fdef = [] /\
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    fn_captures fcallee = [] /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_store_safe_synthetic_direct_call_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists fname args synthetic_body T_body Γ_out R_body roots_body,
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    store_safe_function_value_call_args env args /\
    preservation_direct_call_ready_expr synthetic_body /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_store_safe_synthetic_direct_call_ready_at env fdef
    (initial_root_env_for_fn fdef).

Definition env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      env fdef.

Definition component_body_store_safe_synthetic_direct_call_ready_summary_provider
    (env : global_env) : Prop :=
  forall f_component,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_synthetic_direct_call_ready_summary_provider
    (env : global_env) : Prop :=
  forall f_component,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_synthetic_direct_call_ready_summary_at_provider
    (env : global_env) : Prop :=
  forall f_component fname args synthetic_body,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds f_component)) fname.

Definition component_body_synthetic_direct_call_ready_body_env_evidence_provider
    (env : global_env) : Prop :=
  forall f_component,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    forall fcall,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f_component))
          (fn_bounds fcall)).

Definition component_body_no_capture_direct_call_component_closure_check_provider
    (env : global_env) : Prop :=
  forall f_component,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    check_fn_root_shadow_no_capture_direct_call_component_closure
      env f_component = true.

Definition component_body_synthetic_direct_call_ready_summary_at_in_provider
    (env : global_env) : Prop :=
  forall f_component fname args synthetic_body,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds f_component)) fname.

Definition component_body_synthetic_direct_call_ready_body_env_evidence_in_provider
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    forall fcall,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f_component))
          (fn_bounds fcall)).


Definition component_body_synthetic_direct_call_ready_nested_summary_at_in_provider
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    forall fcall fname args synthetic_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f_component))
          (fn_bounds fcall)) fname.

Definition component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    forall fcall fcall_inner,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f_component))
            (fn_bounds fcall))
          (fn_bounds fcall_inner)).



Definition component_body_no_capture_direct_call_component_target_in_provider
    (env : global_env) : Prop :=
  forall f_component fname args synthetic_body,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    forall fdef,
      lookup_fn fname (env_fns (global_env_with_local_bounds env (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f_component)) fdef.

Definition component_body_synthetic_direct_call_ready_closure_nested_summary_at_in_provider
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    forall fcall fname args synthetic_body,
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f_component)) fcall ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f_component))
          (fn_bounds fcall)) fname.

Definition component_body_synthetic_direct_call_ready_closure_nested_body_env_evidence_in_provider
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    forall fcall fcall_inner,
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f_component)) fcall ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f_component))
            (fn_bounds fcall))
          (fn_bounds fcall_inner)).



Lemma component_body_synthetic_direct_call_ready_closure_nested_summary_at_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_closure_nested_summary_at_in_provider env.
Proof.
  intros env Hprovider f_component Hin Hcomponent fcall fname args
    synthetic_body _Hfcall_component Htarget.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_synthetic_direct_call_ready_closure_nested_body_env_evidence_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    component_body_synthetic_direct_call_ready_closure_nested_body_env_evidence_in_provider env.
Proof.
  intros env Hprovider f_component Hin Hcomponent fcall fcall_inner
    _Hfcall_component.
  eapply Hprovider; eassumption.
Qed.

Lemma lookup_fn_b_of_lookup_fn :
  forall fname fenv fdef,
    lookup_fn fname fenv = Some fdef ->
    lookup_fn_b fname fenv = Some fdef.
Proof.
  intros fname fenv.
  induction fenv as [| f rest IH]; intros fdef Hlookup; simpl in *.
  - discriminate.
  - destruct (ident_eqb fname (fn_name f)); [exact Hlookup |].
    eapply IH. exact Hlookup.
Qed.

Lemma component_body_synthetic_direct_call_ready_summary_at_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_summary_at_provider env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env.
Proof.
  intros env Hprovider f_component fname args synthetic_body _Hin Hcomponent
    Htarget.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_synthetic_direct_call_ready_body_env_evidence_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_body_env_evidence_provider env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_in_provider env.
Proof.
  intros env Hprovider f_component _Hin Hcomponent fcall.
  eapply Hprovider. exact Hcomponent.
Qed.

Definition eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_prefix_exact_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
        env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
        env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

Definition eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
        env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
        env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.

Definition eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement
    : Prop :=
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_prefix_exact_call_statement /\
  eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement.

Lemma callee_body_root_shadow_synthetic_direct_call_ready_summary_of_store_safe :
  forall env fdef,
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      env fdef ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary env fdef.
Proof.
  intros env fdef [Hnodup Hready].
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_store_safe_synthetic_direct_call_ready_at
    in Hready.
  unfold callee_body_root_shadow_synthetic_direct_call_ready_at.
  destruct Hready as
    (fname & args & synthetic_body & T_body & Gamma_out & R_body &
      roots_body & Htarget & Hsynthetic & _Hsafe & Hready_body & Htyped &
      Hcompat & Hexclude_roots & Hexclude_env).
  exists fname, args, synthetic_body, T_body, Gamma_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe :
  forall env,
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env.
Proof.
  intros env Hsummary fname fdef Hlookup.
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_store_safe.
  eapply Hsummary. exact Hlookup.
Qed.

Lemma component_body_synthetic_direct_call_ready_summary_provider_of_store_safe :
  forall env,
    component_body_store_safe_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_summary_provider env.
Proof.
  intros env Hprovider f_component Hcomponent.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe.
  eapply Hprovider. exact Hcomponent.
Qed.

Lemma component_body_synthetic_direct_call_ready_summary_provider_of_summary_evidence :
  forall env,
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    component_body_synthetic_direct_call_ready_summary_provider env.
Proof.
  intros env Hsummary f_component _Hcomponent.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  exact Hsummary.
Qed.

Lemma component_body_synthetic_direct_call_ready_summary_at_provider_of_summary_evidence :
  forall env,
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    component_body_synthetic_direct_call_ready_summary_at_provider env.
Proof.
  intros env Hsummary f_component fname args synthetic_body _Hcomponent
    _Htarget.
  eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  exact Hsummary.
Qed.

Lemma component_body_synthetic_direct_call_ready_summary_at_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_summary_at_provider env.
Proof.
  intros env Hprovider f_component fname args synthetic_body Hcomponent
    _Htarget.
  eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
  eapply Hprovider. exact Hcomponent.
Qed.

Theorem eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_plain_summary_exact_package :
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement.
Proof.
  intros [Hplain_prefix Hplain_scope]. split.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots
      Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
      Hsummary Hbridge.
    eapply Hplain_prefix; try eassumption.
    + eapply store_safe_function_value_call_args_preservation_ready.
      exact Hsafe_args.
    + eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe.
      exact Hsummary.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hsafe_args Hstore Hnamed Hkeys Htyped Hunique Hsummary Hbridge
      Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
    eapply Hplain_scope; try eassumption.
    + eapply store_safe_function_value_call_args_preservation_ready.
      exact Hsafe_args.
    + eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe.
      exact Hsummary.
Qed.

Lemma direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge :
  forall env,
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
      env ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env.
Proof.
  intros env Hsummary Hbridge.
  eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge.
  - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe.
    exact Hsummary.
  - exact Hbridge.
Qed.

Lemma callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      env fdef ->
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef [Hnodup Hready].
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_store_safe_synthetic_direct_call_ready_at
    in *.
  destruct Hready as
    (fname & args & synthetic_body & T_body & Gamma_out & R_body &
      roots_body & Htarget & Hsynthetic & Hsafe & Hready_body & Htyped &
      Hcompat & Hexclude_roots & Hexclude_env).
  exists fname, args, synthetic_body, T_body, Gamma_out, R_body, roots_body.
  repeat split; try assumption.
  apply store_safe_function_value_call_args_global_env_with_local_bounds.
  exact Hsafe.
Qed.

Lemma env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds :
  forall env bounds,
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env bounds).
Proof.
  intros env bounds Hsummary fname fdef Hlookup.
  change (lookup_fn fname (env_fns env) = Some fdef) in Hlookup.
  eapply callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_global_env_with_local_bounds.
  exact (Hsummary fname fdef Hlookup).
Qed.

Theorem eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Sigma' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Omega n R Sigma T
    Sigma' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge.
  eapply
    (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_named_bind_facts_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready);
    try eassumption.
  - eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption.
  - intros fcall.
    eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    + eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    + eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      * exact Hroot_names.
      * exact Hroot_keys.
      * unfold fn_env_unique_by_name in *; simpl; exact Hunique.
Qed.


Theorem eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Sigma' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Omega n R Sigma T
    Sigma' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge.
  eapply
    (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core
      Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready);
    try eassumption.
  - eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption.
  - intros fcall.
    eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    + eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    + eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      * exact Hroot_names.
      * exact Hroot_keys.
      * unfold fn_env_unique_by_name in *; simpl; exact Hunique.
Qed.


Theorem eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Omega : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Omega n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Omega n R Σ T
    Σ' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof
    (env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe
      env Hsummary) as Hsummary_plain.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Omega n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Omega n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Σ args
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots s s_args vs Hsafe_args H7 H1 Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    - eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Omega n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H0 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Omega n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary_plain H3 eq_refl H0 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_evidence
      Hsynthetic_route Htyping_ready Hroots_ready env Omega n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H0 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & Hresult_subset & _Heval_synthetic &
        _Hstore_args & Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & Hv_final & Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & Hret_roots).
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Hroots_args.
  - eapply direct_call_value_roots_within_store_subset; eassumption.
  - rewrite Hremoved_exact. exact Hshadow_args.
Qed.

Theorem eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_final_roots_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Omega : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Omega n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Omega n R Σ T
    Σ' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof
    (env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe
      env Hsummary) as Hsummary_plain.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Omega n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Omega n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Σ args
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots s s_args vs Hsafe_args H7 H1 Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    - eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Omega n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H0 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Omega n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary_plain H3 eq_refl H0 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Omega n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H0 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & Hresult_subset & _Heval_synthetic &
        _Hstore_args & Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & Hv_final & Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & Hret_roots).
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Hroots_args.
  - eapply direct_call_value_roots_within_store_subset; eassumption.
  - rewrite Hremoved_exact. exact Hshadow_args.
Qed.

Theorem eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env s fname args s' v
    Heval Ω n R Σ T Σ' R' roots ps frame Hsafe_args Hstore Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof
    (env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe
      env Hsummary) as Hsummary_plain.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hframe_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hroots Hshadow Hrn
              Hframe Hfresh)
    as [_ [_ [_ [_ [Hframe_args _]]]]].
  destruct (proj1 (proj2 Hparam_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hparam)
    as [frame_args Hparam_args].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [_ [_ [_ Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh_params Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots s s_args vs Hsafe_args H7 H1 Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    - eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H5 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary_plain H3 eq_refl H5 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_evidence
      Hsynthetic_route Htyping_ready Hroots_ready env Ω n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H5 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & _roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & _Hresult_subset & _Heval_synthetic &
        _Hstore_args & _Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & _Hv_final & _Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & _Hret_roots).
  split.
  - rewrite Hremoved_exact. exact Hframe_args.
  - exists frame_args. rewrite Hremoved_exact. exact Hparam_args.
Qed.

Theorem eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env s fname args s' v
    Heval Ω n R Σ T Σ' R' roots ps frame Hsafe_args Hstore Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof
    (env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe
      env Hsummary) as Hsummary_plain.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hframe_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hroots Hshadow Hrn
              Hframe Hfresh)
    as [_ [_ [_ [_ [Hframe_args _]]]]].
  destruct (proj1 (proj2 Hparam_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hparam)
    as [frame_args Hparam_args].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [_ [_ [_ Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh_params Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots s s_args vs Hsafe_args H7 H1 Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    - eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H5 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary_plain H3 eq_refl H5 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Ω n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H5 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & _roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & _Hresult_subset & _Heval_synthetic &
        _Hstore_args & _Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & _Hv_final & _Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & _Hret_roots).
  split.
  - rewrite Hremoved_exact. exact Hframe_args.
  - exists frame_args. rewrite Hremoved_exact. exact Hparam_args.
Qed.

Theorem eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_routes_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros Hsynthetic_call_route Hscope_call Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env s fname args s' v
    Heval Ω n R Σ T Σ' R' roots ps frame Hsafe_args Hstore Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof
    (env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_store_safe
      env Hsummary) as Hsummary_plain.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hframe_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hroots Hshadow Hrn
              Hframe Hfresh)
    as [_ [_ [_ [_ [Hframe_args _]]]]].
  destruct (proj1 (proj2 Hparam_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hparam)
    as [frame_args Hparam_args].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [_ [_ [_ Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh_params Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots s s_args vs Hsafe_args H7 H1 Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge.
    - eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_call_statement_ready_evidence
      Hscope_call Htyping_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H5 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary_plain H3 eq_refl H5 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Ω n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H5 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & _roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & _Hresult_subset & _Heval_synthetic &
        _Hstore_args & _Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & _Hv_final & _Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & _Hret_roots).
  split.
  - rewrite Hremoved_exact. exact Hframe_args.
  - exists frame_args. rewrite Hremoved_exact. exact Hparam_args.
Qed.

Theorem eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_final_roots_and_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  split.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots
      Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
      Hsummary Hbridge.
    destruct
      (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core
        Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
        Hroot_names Hroot_keys env s s' v fname args Heval Ω n R Σ T Σ'
        R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
        Hunique Hsummary Hbridge)
      as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    repeat split; try assumption.
    eapply store_typed_prefix_exact. exact Hstore'.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hsafe_args Hstore Hnamed Hkeys Htyped Hunique Hsummary Hbridge
      Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
    eapply eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_cleanup;
      eassumption.
Qed.

Theorem eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_final_roots_and_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  split.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots
      Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
      Hsummary Hbridge.
    destruct
      (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_final_roots_core
        Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
        Hroot_names Hroot_keys env s s' v fname args Heval Ω n R Σ T Σ'
        R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
        Hunique Hsummary Hbridge)
      as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    repeat split; try assumption.
    eapply store_typed_prefix_exact. exact Hstore'.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hsafe_args Hstore Hnamed Hkeys Htyped Hunique Hsummary Hbridge
      Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
    eapply eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup;
      eassumption.
Qed.


Theorem eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_routes_final_roots_and_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement.
Proof.
  intros Hsynthetic_call_route Hscope_call Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  assert (Hscope_synthetic :
    eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement).
  { eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement_of_call_statement;
      eassumption. }
  split.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots
      Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
      Hsummary Hbridge.
    destruct
      (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_final_roots_core
        Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
        Hroot_names Hroot_keys env s s' v fname args Heval Ω n R Σ T Σ'
        R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
        Hunique Hsummary Hbridge)
      as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    repeat split; try assumption.
    eapply store_typed_prefix_exact. exact Hstore'.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hsafe_args Hstore Hnamed Hkeys Htyped Hunique Hsummary Hbridge
      Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
    eapply eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_routes_cleanup;
      eassumption.
Qed.


Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef _ Hsummary.
  destruct Hsummary as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & Hin & Hname & Hcallee_captures &
      Hnodup & Htyped & Hcompat & Hroots & Henv).
  exists fname, args, raw_body, synthetic_body, fcallee, T_body, Gamma_out,
    R_body, roots_body.
  repeat split; try assumption;
    try (apply store_safe_function_value_call_args_global_env_with_local_bounds;
      exact Hsafe_args);
    try (change (env_fns (global_env_with_local_bounds env bounds))
      with (env_fns env); exact Hin);
    try (change (typed_env_roots_shadow_safe
      (global_env_with_local_bounds
        (global_env_with_local_bounds env bounds)
        (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body)
      with (typed_env_roots_shadow_safe
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (fn_body_ctx fdef))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body);
      exact Htyped).
Qed.

Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_synthetic_direct_call_ready :
  forall env fdef,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef ->
    exists fname args synthetic_body,
      direct_call_target_expr (fn_body fdef) =
        Some (fname, args, synthetic_body) /\
      synthetic_body = ECall fname args /\
      preservation_direct_call_ready_expr synthetic_body.
Proof.
  intros env fdef Hsummary.
  destruct Hsummary as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _ & Hbody & Htarget & Hsynthetic &
      Hsafe_args & _).
  subst raw_body synthetic_body.
  exists fname, args, (ECall fname args).
  repeat split; try exact Htarget.
  apply PDCR_Call.
  eapply store_safe_function_value_call_args_preservation_ready.
  exact Hsafe_args.
Qed.

Lemma callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component :
  forall env fdef,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary env fdef.
Proof.
  intros env fdef Hsummary.
  destruct Hsummary as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _ & Hbody & Htarget & Hsynthetic &
      Hsafe_args & _ & _ & _ & Hnodup & Htyped & Hcompat & Hroots & Henv).
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_synthetic_direct_call_ready_at.
  subst raw_body.
  exists fname, args, synthetic_body, T_body, Gamma_out, R_body, roots_body.
  repeat split; try assumption.
  rewrite Hsynthetic.
  apply PDCR_Call.
  eapply store_safe_function_value_call_args_preservation_ready.
  exact Hsafe_args.
Qed.

Lemma callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component :
  forall env fdef,
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef ->
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      env fdef.
Proof.
  intros env fdef Hsummary.
  destruct Hsummary as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _ & Hbody & Htarget & Hsynthetic &
      Hsafe_args & _ & _ & _ & Hnodup & Htyped & Hcompat & Hroots & Henv).
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_store_safe_synthetic_direct_call_ready_at.
  subst raw_body.
  exists fname, args, synthetic_body, T_body, Gamma_out, R_body, roots_body.
  repeat split; try assumption.
  rewrite Hsynthetic.
  apply PDCR_Call.
  eapply store_safe_function_value_call_args_preservation_ready.
  exact Hsafe_args.
Qed.


Lemma subst_type_params_trait_ref_nil : forall tr,
  subst_type_params_trait_ref [] tr = tr.
Proof.
  intros tr. destruct tr as [name args].
  unfold subst_type_params_trait_ref. simpl.
  rewrite map_subst_type_params_ty_nil. reflexivity.
Qed.

Lemma subst_type_params_trait_bound_nil : forall b,
  subst_type_params_trait_bound [] b = b.
Proof.
  intros b. destruct b as [idx traits].
  unfold subst_type_params_trait_bound. simpl.
  f_equal.
  induction traits as [| tr traits IH]; simpl; auto.
  rewrite subst_type_params_trait_ref_nil, IH. reflexivity.
Qed.

Lemma subst_type_params_trait_bounds_nil : forall bounds,
  subst_type_params_trait_bounds [] bounds = bounds.
Proof.
  induction bounds as [| b bounds IH]; simpl; auto.
  rewrite subst_type_params_trait_bound_nil, IH. reflexivity.
Qed.

Lemma callee_body_root_shadow_captured_call_generic_direct_instantiated_nil_fuel :
  forall env fdef,
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10001 fdef [].
Proof.
  intros env fdef Hsummary.
  destruct Hsummary as
    (fname & type_args & args & raw_body & synthetic_body & fcallee &
      T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
      Hsynthetic & Hsafe & Hin & Hname & Harity & Hbounds & Hcallee_ready &
      Hcallee_summary & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
  eapply CBRSSNI_GenericDirect with
    (raw_body := raw_body) (synthetic_body := synthetic_body)
    (fcallee := fcallee) (T_body := T_body) (Gamma_out := Gamma_out)
    (R_body := R_body) (roots_body := roots_body).
  - rewrite subst_type_params_expr_nil. symmetry. exact Hbody.
  - exact Htarget.
  - exact Hsynthetic.
  - exact Hsafe.
  - exact Hin.
  - exact Hname.
  - exact Harity.
  - rewrite subst_type_params_trait_bounds_nil. exact Hbounds.
  - exact Hcallee_summary.
  - rewrite apply_type_params_nil. exact Hnodup.
  - rewrite subst_type_params_trait_bounds_nil.
    rewrite subst_type_params_ctx_nil.
    exact Htyped.
  - rewrite subst_type_params_ty_nil. exact Hcompat.
  - rewrite apply_type_params_nil. exact Hexcl_roots.
  - rewrite apply_type_params_nil. exact Hexcl_env.
Qed.

Definition callee_body_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_captured_call_provenance_summary env fdef \/
  callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_let_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_if_literal_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_local_fn_value_generic_direct_narrow_store_safe_summary
    env fdef \/
  exists T_body Gamma_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_store_safe_narrow_summary_checked env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_generic_direct_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef.
Proof.
  intros env fdef Hgeneric.
  unfold check_fn_root_shadow_generic_direct_store_safe_summary in Hgeneric.
  destruct (generic_direct_call_target_expr (fn_body fdef))
    as [[[[fname type_args] args] synthetic_body] |] eqn:Htarget;
    try discriminate.
  apply andb_true_iff in Hgeneric as [Hsafe_args Hgeneric].
  destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
    try discriminate.
  apply andb_true_iff in Hgeneric as [Htype_params Hgeneric].
  apply Nat.eqb_eq in Htype_params.
  destruct (check_struct_bounds
    (global_env_with_local_bounds env (fn_bounds fdef))
    (fn_bounds fcallee) type_args)
    as [bounds_err |] eqn:Hbounds; try discriminate.
  remember (global_env_with_local_bounds env
    (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
    as callee_body_env.
  destruct (infer_core_env_roots_shadow_safe callee_body_env
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
    (fn_with_body fdef synthetic_body)
    (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hgeneric.
  destruct Hgeneric as
    [[[[[[[Hcallee_ready Hcallee_expr] Hcallee_compat] Hcallee_roots]
         Hcallee_env_excl] Hcompat] Hroots] Henv].
  apply lookup_fn_b_sound in Hlookup_b.
  destruct Hlookup_b as [Hin_callee Hname_callee].
  pose proof
    (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
      env fcallee type_args Hcallee_expr) as Hcallee_summary.
  pose proof (infer_env_roots_shadow_safe_sound env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
  unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
  destruct Htyped_fn as
    (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
  exists fname, type_args, args, (fn_body fdef), synthetic_body, fcallee,
    T_body_actual, Gamma_out_actual, R_body, roots_body.
  split; [reflexivity |].
  split; [exact Htarget |].
  split.
  { unfold generic_direct_call_target_expr in Htarget.
    destruct (fn_body fdef); try discriminate.
    inversion Htarget. reflexivity. }
  split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
  split; [exact Hin_callee |].
  split; [exact Hname_callee |].
  split; [exact Htype_params |].
  split; [exact Hbounds |].
  split.
  { apply preservation_ready_expr_b_sound. exact Hcallee_ready. }
  split; [exact Hcallee_summary |].
  split.
  { change (NoDup
      (ctx_names
        (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
    eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
  split; [exact Htyped_body |].
  split; [exact Hcompat_body |].
  split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
  apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
    in Hcheck.
  destruct (fn_captures fdef) as [| capture captures] eqn:Hcaptures;
    try discriminate.
  destruct (direct_call_target_expr (fn_body fdef))
    as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
  apply andb_true_iff in Hcheck as [Hsafe_args Hcheck].
  destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
    try discriminate.
  destruct (fn_captures fcallee) as [| callee_capture callee_captures]
    eqn:Hcallee_captures; try discriminate.
  destruct (infer_env_roots_shadow_safe env
    (fn_with_body fdef synthetic_body)
    (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hcompat Hroots] Henv].
  apply lookup_fn_b_sound in Hlookup_b.
  destruct Hlookup_b as [Hin_callee Hname_callee].
  pose proof (infer_env_roots_shadow_safe_sound env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
  unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
  destruct Htyped_fn as
    (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
  exists fname, args, (fn_body fdef), synthetic_body, fcallee,
    T_body_actual, Gamma_out_actual, R_body, roots_body.
  split; [exact Hcaptures |].
  split; [reflexivity |].
  split; [exact Htarget |].
  split.
  { unfold direct_call_target_expr in Htarget.
    destruct (fn_body fdef); try discriminate.
    - inversion Htarget. reflexivity.
    - destruct e; try discriminate.
      inversion Htarget. reflexivity. }
  split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
  split; [exact Hin_callee |].
  split; [exact Hname_callee |].
  split; [exact Hcallee_captures |].
  split.
  { change (NoDup
      (ctx_names
        (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
    eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
  split; [exact Htyped_body |].
  split; [exact Hcompat_body |].
  split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
  apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary :
  forall env fdef,
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef = true ->
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      env fdef.
Proof.
  intros env fdef Hcheck.
  apply callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  apply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
  exact Hcheck.
Qed.

Lemma check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_store_safe_synthetic_direct_call_ready_summary_when_not_captured :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env fdef = true ->
    check_fn_root_shadow_captured_call_store_safe_summary env fdef = false ->
    callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary
      env fdef.
Proof.
  intros env fdef Hcombined Hcaptured.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined.
  rewrite Hcaptured in Hcombined.
  simpl in Hcombined.
  eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary.
  exact Hcombined.
Qed.

Lemma check_fn_root_shadow_captured_call_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_store_safe_summary in Hcheck.
  apply orb_true_iff in Hcheck as [Hprefix_local | Hnarrow].
  - apply orb_true_iff in Hprefix_local as [Hprefix_if | Hlocal].
    { apply orb_true_iff in Hprefix_if as [Hprefix_let | Hif].
      - apply orb_true_iff in Hprefix_let as [Hprefix | Hlet].
        + apply orb_true_iff in Hprefix as [Hhead | Hgeneric].
      { apply orb_true_iff in Hhead as [Hold | Hdirect].
        * left. apply check_fn_root_shadow_captured_call_provenance_summary_sound.
        exact Hold.
        * right. left.
      destruct (direct_call_target_expr (fn_body fdef))
        as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
      apply andb_true_iff in Hdirect as [Hready_args Hdirect].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee))
        as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
        eqn:Hcallee_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fcallee
        (initial_root_env_for_fn fcallee))
        as [[[[T_callee_env Gamma_callee_env] R_callee_env]
              roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hdirect.
      destruct Hdirect as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      destruct (check_expr_root_shadow_store_safe_narrow_summary_sound
        env (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee) T_callee Gamma_callee R_callee roots_callee
        Hcallee_core Hcallee_expr) as [ret_roots_callee Hcallee_summary].
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split.
      { unfold direct_call_target_expr in Htarget.
        destruct (fn_body fdef); try discriminate.
        - inversion Htarget. reflexivity.
        - destruct e; try discriminate.
          inversion Htarget. reflexivity. }
      split; [apply store_safe_function_value_call_args_b_sound; exact Hready_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split.
      { exists T_callee, Gamma_callee, R_callee, roots_callee,
          ret_roots_callee.
        repeat split.
        - eapply infer_env_roots_shadow_safe_params_nodup.
          exact Hcallee_env.
        - exact Hcallee_summary.
        - exact Hcallee_compat.
        - apply fn_params_roots_exclude_b_sound. exact Hcallee_roots.
        - apply fn_params_root_env_excludes_b_sound. exact Hcallee_env_excl. }
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
      }
      { right. right. left.
        eapply check_fn_root_shadow_generic_direct_store_safe_summary_sound.
        exact Hgeneric.
      }
        + right. right. right. left.
      destruct (let_bound_generic_direct_call_target_expr (fn_body fdef))
        as [[[[[fname type_args] args] T_hidden] synthetic_body] |]
        eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hlet as [Hsafe_args Hlet].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      apply andb_true_iff in Hlet as [Htype_params Hlet].
      apply Nat.eqb_eq in Htype_params.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fcallee) type_args)
        as [bounds_err |] eqn:Hbounds; try discriminate.
      remember (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
        as callee_body_env.
      destruct (infer_core_env_roots_shadow_safe callee_body_env
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
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hlet.
      destruct Hlet as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env fcallee type_args Hcallee_expr) as Hcallee_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, type_args, args, T_hidden, (fn_body fdef), synthetic_body,
        fcallee, T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split; [exact Htype_params |].
      split; [exact Hbounds |].
      split; [exact Hcallee_summary |].
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
      - right. right. right. right. left.
      destruct (if_literal_generic_direct_call_target_expr (fn_body fdef))
        as [[[[[[[[b fname_then] type_args_then] args_then] fname_else]
                type_args_else] args_else] synthetic_body] |] eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hif as [Hsafes Hif].
      apply andb_true_iff in Hsafes as [Hsafe_then Hsafe_else].
      destruct (lookup_fn_b fname_then (env_fns env)) as [fthen |]
        eqn:Hlookup_then; try discriminate.
      destruct (lookup_fn_b fname_else (env_fns env)) as [felse |]
        eqn:Hlookup_else; try discriminate.
      apply andb_true_iff in Hif as [Htype_params_pair Hif].
      apply andb_true_iff in Htype_params_pair as
        [Htype_params_then Htype_params_else].
      apply Nat.eqb_eq in Htype_params_then.
      apply Nat.eqb_eq in Htype_params_else.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fthen) type_args_then) as [bounds_then |]
        eqn:Hbounds_then; try discriminate.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds felse) type_args_else) as [bounds_else |]
        eqn:Hbounds_else; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fthen) (fn_lifetimes fthen)
        (initial_root_env_for_fn fthen)
        (subst_type_params_ctx type_args_then (fn_body_ctx fthen))
        (subst_type_params_expr type_args_then (fn_body fthen)))
        as [[[[T_then Gamma_then] R_then] roots_then] | err]
        eqn:Hthen_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fthen
        (initial_root_env_for_fn fthen))
        as [[[[T_then_env Gamma_then_env] R_then_env]
              roots_then_env] | err] eqn:Hthen_env; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives felse) (fn_lifetimes felse)
        (initial_root_env_for_fn felse)
        (subst_type_params_ctx type_args_else (fn_body_ctx felse))
        (subst_type_params_expr type_args_else (fn_body felse)))
        as [[[[T_else Gamma_else] R_else] roots_else] | err]
        eqn:Helse_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env felse
        (initial_root_env_for_fn felse))
        as [[[[T_else_env Gamma_else_env] R_else_env]
              roots_else_env] | err] eqn:Helse_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hif.
      destruct Hif as
        [[[[[[[[[[Hthen_expr Hthen_compat] Hthen_roots]
                Hthen_env_excl] Helse_expr] Helse_compat] Helse_roots]
            Helse_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_then.
      destruct Hlookup_then as [Hin_then Hname_then].
      apply lookup_fn_b_sound in Hlookup_else.
      destruct Hlookup_else as [Hin_else Hname_else].
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env fthen type_args_then Hthen_expr) as Hthen_summary.
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env felse type_args_else Helse_expr) as Helse_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists b, fname_then, type_args_then, args_then, fname_else,
        type_args_else, args_else, (fn_body fdef), synthetic_body, fthen,
        felse, T_body_actual, Gamma_out_actual, R_body, roots_body.
      repeat split; try reflexivity; try eassumption;
        try (apply store_safe_function_value_call_args_b_sound; eassumption);
        try (apply fn_params_roots_exclude_b_sound; eassumption);
        try (apply fn_params_root_env_excludes_b_sound; eassumption).
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
    }
    { right. right. right. right. right. left.
      destruct (local_fn_value_call_target_expr_with_binder (fn_body fdef))
        as [[[[x fname] args] synthetic_body] |] eqn:Htarget; try discriminate.
      repeat rewrite andb_true_iff in Hlocal.
      destruct Hlocal as [[[Hsafe_args Hnot_free_b] Hnot_local_b] Hlocal].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
        eqn:Hlookup_b; try discriminate.
      apply andb_true_iff in Hlocal as [Hcallee_generic Hlocal].
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hlocal.
      destruct Hlocal as [[Hcompat Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      pose proof
        (check_fn_root_shadow_generic_direct_store_safe_summary_sound
          env fcallee Hcallee_generic) as Hcallee_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists x, fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
      split.
      { rewrite <- args_free_vars_checker_eq.
        apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnot_free_b. }
      split.
      { apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnot_local_b. }
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split; [exact Hcallee_summary |].
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
    }
  - right. right. right. right. right. right.
    destruct (infer_core_env_roots_shadow_safe_checked env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef))
      as [[[[T_body Gamma_body] R_body] roots_body] | err] eqn:Hcore;
      try discriminate.
    destruct (infer_env_roots_shadow_safe_checked env fdef
      (initial_root_env_for_fn fdef))
      as [[[[T_env Gamma_env] R_env] roots_env] | err] eqn:Hinfer_env;
      try discriminate.
    repeat rewrite andb_true_iff in Hnarrow.
    destruct Hnarrow as [[[Hexpr Hcompat] Hroots] Henv].
    destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_sound
      env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef)
      T_body Gamma_body R_body roots_body Hcore Hexpr)
      as [ret_roots Hsummary].
    exists T_body, Gamma_body, R_body, roots_body, ret_roots.
    repeat split.
    + eapply infer_env_roots_shadow_safe_checked_params_nodup.
      exact Hinfer_env.
    + exact Hsummary.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Definition env_fns_root_shadow_captured_call_store_safe_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.

Lemma check_env_root_shadow_captured_call_store_safe_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_store_safe_summary env = true ->
    env_fns_root_shadow_captured_call_store_safe_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_store_safe_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
  exact Hcheck.
Qed.

Definition env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef.

Definition callee_body_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_captured_call_store_safe_summary env fdef \/
  callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
    env fdef.

Definition env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env fdef.

Lemma check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env fdef = true ->
    callee_body_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcheck.
  apply orb_true_iff in Hcheck as [Hcaptured | Hcomponent].
  - left. apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
    exact Hcaptured.
  - right.
    apply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
    exact Hcomponent.
Qed.

Lemma check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_sound.
  exact Hcheck.
Qed.

Definition env_fns_no_capture_direct_call_component_synthetic_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    exists call_name args synthetic_body,
      direct_call_target_expr (fn_body fdef) =
        Some (call_name, args, synthetic_body) /\
      synthetic_body = ECall call_name args /\
      preservation_direct_call_ready_expr synthetic_body.

Lemma env_fns_no_capture_direct_call_component_synthetic_ready_of_summary :
  forall env,
    env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready
      env ->
    env_fns_no_capture_direct_call_component_synthetic_ready env.
Proof.
  intros env Hsummary fname fdef Hlookup.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_synthetic_direct_call_ready.
  eapply Hsummary. exact Hlookup.
Qed.

Lemma env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_no_capture_direct_call_component :
  forall env,
    env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready
      env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env.
Proof.
  intros env Hsummary fname fdef Hlookup.
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  eapply Hsummary. exact Hlookup.
Qed.

Lemma env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_of_no_capture_direct_call_component :
  forall env,
    env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready
      env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env.
Proof.
  intros env Hsummary fname fdef Hlookup.
  eapply callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  eapply Hsummary. exact Hlookup.
Qed.

Lemma component_body_store_safe_synthetic_direct_call_ready_summary_provider_of_store_safe_summary_evidence :
  forall env,
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider env.
Proof.
  intros env Hsummary f_component _Hcomponent.
  eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  exact Hsummary.
Qed.

Lemma component_body_store_safe_synthetic_direct_call_ready_summary_provider_of_no_capture_direct_call_component_ready :
  forall env,
    env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready
      env ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider env.
Proof.
  intros env Hready f_component _Hcomponent fname fdef Hlookup.
  eapply callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_global_env_with_local_bounds.
  eapply callee_body_root_shadow_store_safe_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  eapply Hready. exact Hlookup.
Qed.


Lemma check_fn_root_shadow_no_capture_direct_call_component_closure_seen_head_sound :
  forall fuel seen env fdef,
    check_fn_root_shadow_no_capture_direct_call_component_closure_seen
      fuel seen env fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef.
Proof.
  intros fuel seen env fdef Hcheck Hnot_seen.
  destruct fuel as [| fuel']; simpl in Hcheck; try discriminate.
  destruct (CheckerOrdinary.ident_in_b (fn_name fdef) seen) eqn:Hseen;
    try discriminate; try rewrite Hseen in Hnot_seen; try discriminate.
  apply andb_true_iff in Hcheck as [Hcomponent _].
  eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
  exact Hcomponent.
Qed.

Lemma check_fn_root_shadow_no_capture_direct_call_component_closure_head_sound :
  forall env fdef,
    check_fn_root_shadow_no_capture_direct_call_component_closure env fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_no_capture_direct_call_component_closure in Hcheck.
  eapply check_fn_root_shadow_no_capture_direct_call_component_closure_seen_head_sound.
  - exact Hcheck.
  - reflexivity.
Qed.

Lemma check_fn_root_shadow_no_capture_direct_call_component_closure_seen_callee :
  forall fuel seen env fdef fname args synthetic_body fcallee,
    check_fn_root_shadow_no_capture_direct_call_component_closure_seen
      fuel seen env fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    direct_call_target_expr (fn_body fdef) = Some (fname, args, synthetic_body) ->
    lookup_fn_b fname (env_fns env) = Some fcallee ->
    exists fuel',
      fuel = S fuel' /\
      check_fn_root_shadow_no_capture_direct_call_component_closure_seen
        fuel' (fn_name fdef :: seen) env fcallee = true.
Proof.
  intros fuel seen env fdef fname args synthetic_body fcallee Hcheck
    Hnot_seen Htarget Hlookup.
  destruct fuel as [| fuel']; simpl in Hcheck; try discriminate.
  destruct (CheckerOrdinary.ident_in_b (fn_name fdef) seen) eqn:Hseen;
    try discriminate; try rewrite Hseen in Hnot_seen; try discriminate.
  apply andb_true_iff in Hcheck as [_ Hcallee].
  rewrite Htarget in Hcallee.
  rewrite Hlookup in Hcallee.
  exists fuel'. split; [reflexivity | exact Hcallee].
Qed.


Lemma component_body_no_capture_direct_call_component_target_in_provider_of_closure_check_provider :
  forall env,
    fn_env_unique_by_name env ->
    component_body_no_capture_direct_call_component_closure_check_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env.
Proof.
  intros env Hunique Hprovider f_component fname args synthetic_body
    Hin_component Hcomponent Htarget fdef Hlookup.
  change (lookup_fn fname (env_fns env) = Some fdef) in Hlookup.
  pose proof (lookup_fn_b_of_lookup_fn fname (env_fns env) fdef Hlookup)
    as Hlookup_b.
  pose proof (Hprovider f_component Hcomponent) as Hcheck.
  unfold check_fn_root_shadow_no_capture_direct_call_component_closure in Hcheck.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_closure_seen_callee
              10001 [] env f_component fname args synthetic_body fdef
              Hcheck eq_refl Htarget Hlookup_b)
    as (fuel' & Hfuel & Hcallee_check).
  inversion Hfuel; subst fuel'; clear Hfuel.
  destruct (CheckerOrdinary.ident_in_b (fn_name fdef) [fn_name f_component])
    eqn:Hseen.
  - assert (Hsame_name : fn_name fdef = fn_name f_component).
    { simpl in Hseen.
      destruct (ident_eqb (fn_name fdef) (fn_name f_component)) eqn:Hname;
        try discriminate.
      apply ident_eqb_eq in Hname. exact Hname. }
    destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
      as [Hin_fdef _Hname_fdef].
    assert (Hsame_def : fdef = f_component).
    { eapply Hunique; eassumption. }
    subst fdef.
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
    + exact Hunique.
    + exact Hcomponent.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
    + exact Hunique.
    + eapply check_fn_root_shadow_no_capture_direct_call_component_closure_seen_head_sound.
      * exact Hcallee_check.
      * exact Hseen.
Qed.

Lemma component_body_synthetic_direct_call_ready_summary_at_in_provider_of_closure_check_provider :
  forall env,
    fn_env_unique_by_name env ->
    component_body_no_capture_direct_call_component_closure_check_provider env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env.
Proof.
  intros env Hunique Hprovider f_component fname args synthetic_body
    Hin_component Hcomponent Htarget fdef Hlookup.
  change (lookup_fn fname (env_fns env) = Some fdef) in Hlookup.
  pose proof (lookup_fn_b_of_lookup_fn fname (env_fns env) fdef Hlookup)
    as Hlookup_b.
  pose proof (Hprovider f_component Hcomponent) as Hcheck.
  unfold check_fn_root_shadow_no_capture_direct_call_component_closure in Hcheck.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_closure_seen_callee
              10001 [] env f_component fname args synthetic_body fdef
              Hcheck eq_refl Htarget Hlookup_b)
    as (fuel' & Hfuel & Hcallee_check).
  inversion Hfuel; subst fuel'; clear Hfuel.
  destruct (CheckerOrdinary.ident_in_b (fn_name fdef) [fn_name f_component])
    eqn:Hseen.
  - assert (Hsame_name : fn_name fdef = fn_name f_component).
    { simpl in Hseen.
      destruct (ident_eqb (fn_name fdef) (fn_name f_component)) eqn:Hname;
        try discriminate.
      apply ident_eqb_eq in Hname. exact Hname. }
    destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
      as [Hin_fdef _Hname_fdef].
    assert (Hsame_def : fdef = f_component).
    { eapply Hunique; eassumption. }
    subst fdef.
    eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_global_env_with_local_bounds.
    eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
    exact Hcomponent.
  - eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_global_env_with_local_bounds.
    eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
    eapply check_fn_root_shadow_no_capture_direct_call_component_closure_seen_head_sound.
    + exact Hcallee_check.
    + exact Hseen.
Qed.

Lemma check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
      env fdef = true ->
    callee_body_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
    in Hcheck.
  apply orb_true_iff in Hcheck as [Hcaptured | Hclosure].
  - left. apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
    exact Hcaptured.
  - right.
    eapply check_fn_root_shadow_no_capture_direct_call_component_closure_head_sound.
    exact Hclosure.
Qed.

Lemma check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
      env = true ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
    in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_ready :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready
      env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
    in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_body_store_safe_provider :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider env.
Proof.
  intros env Hcheck.
  eapply component_body_store_safe_synthetic_direct_call_ready_summary_provider_of_no_capture_direct_call_component_ready.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_ready.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_synthetic_direct_call_ready_summary_evidence :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env.
Proof.
  intros env Hcheck.
  apply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_of_no_capture_direct_call_component.
  apply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_ready.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary_evidence :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env.
Proof.
  intros env Hcheck.
  apply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_of_no_capture_direct_call_component.
  apply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_ready.
  exact Hcheck.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_summary_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_store_safe_summary_fuel] in Hcheck.
    rewrite Hinfer in Hcheck.
    repeat (apply orb_true_iff in Hcheck as [Hcheck | Hcheck]).
    + destruct (check_expr_root_shadow_captured_call_provenance_summary_fuel_sound
        (S fuel') env Omega n R Σ e T Σ' R' roots Hinfer Hcheck)
        as [ret_roots Hexact].
      exists ret_roots. apply ERSS_Exact. exact Hexact.
    + destruct e; try discriminate.
      apply andb_true_iff in Hcheck as [Hready_args Hsupported].
      pose proof
        (check_supported_non_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hinfer_callee & Hcallee_shape).
      subst e.
      exists roots.
      eapply ERSS_FunctionValueCall.
      * apply preservation_ready_args_b_sound. exact Hready_args.
      * exact Hinfer_callee.
      * exact Hcallee_shape.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2i Sigma2i] R2i] roots2i] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[[Hfreei_ret Hsctx_oki] Hroots2i] Henv2i]
        Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i t m Σ1) e2 T2i Sigma2i R2i roots2i Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_oki, Hroots2i, Henv2i in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSS_Let.
      * exact Hbound_summary.
      * exact Hcompat.
      * exact Hlookup_x.
      * apply roots_exclude_b_sound. exact Hroots1.
      * apply root_env_excludes_b_sound. exact Henv1.
      * exact Hbody_summary.
      * exact Hfreei_ret.
      * exact Hsctx_oki.
      * apply roots_exclude_b_sound. exact Hroots2i.
      * apply root_env_excludes_b_sound. exact Henv2i.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err]
        eqn:Hcond; try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans) eqn:Hcond_core;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Helse_check].
      apply andb_true_iff in Hhead as [Hhead Hthen_check].
      apply andb_true_iff in Hhead as [Hcond_bool Hready_cond].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e2) as [[[[T2i Sigma2i] R2i] roots2i] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e3) as [[[[T3 Sigma3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2i) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2i R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Sigma2i) (ctx_of_sctx Sigma3))
        as [Sigma4 |] eqn:Hmerge; try discriminate.
      destruct (IH env Omega n R1 Σ1 e2 T2i Sigma2i R2i roots2i Hthen
        Hthen_check) as [ret_roots2i Hthen_summary].
      destruct (IH env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      exists (root_set_union ret_roots2i ret_roots3).
      eapply ERSS_If.
      * apply provenance_ready_expr_b_sound. exact Hready_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true. exact Hroot_eq.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_summary
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_summary,
    infer_core_env_roots_shadow_safe.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Omega n R
    (sctx_of_ctx Gamma) e) as [[[[T0 Sigma0] R0] roots0] | err]
    eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_summary_fuel_sound;
    eassumption.
Qed.

