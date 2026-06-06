From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeValidatorFacts.
From Facet.TypeSystem Require Export EnvRuntimeInitialFacts.
From Facet.TypeSystem Require Export EnvRuntimeFunctionValueCallFacts.
From Facet.TypeSystem Require Export EnvRuntimeNarrowSummaryFacts.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectCallFacts.
From Facet.TypeSystem Require Export EnvRuntimeNarrowCheckerFacts.
From Facet.TypeSystem Require Export EnvRuntimeFunctionValueRuntimeFacts.
From Facet.TypeSystem Require Export EnvRuntimeLocalBoundsBridgeFacts.
From Facet.TypeSystem Require Export EnvRuntimeNarrowRuntimePackage.
From Facet.TypeSystem Require Export EnvRuntimeDirectCallStoreSafeFacts.
From Facet.TypeSystem Require Export EnvRuntimeCheckedPrefixRuntimePackage.
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

Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_final_store_eq_prefix_named :
  forall env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
      roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys param_tys) Sigma' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      exists s_fn s_args vs fname,
        eval env s (EVar x) s_fn (VClosure fname []) /\
        eval_args env s_fn args s_args vs /\
        s' = s_args.
Proof.
  intros env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary Heval_call Hunique.
  dependent destruction Heval_call.
  match goal with
  | Hcallee_eval : eval env s (EVar x) s_fn (VClosure fname captured) |- _ =>
      rename Hcallee_eval into Heval_callee
  end.
  match goal with
  | Hlookup_fn : lookup_fn fname (env_fns env) = Some fdef |- _ =>
      rename Hlookup_fn into Hlookup
  end.
  match goal with
  | Hargs_eval : eval_args env s_fn args s_args vs |- _ =>
      rename Hargs_eval into Heval_args
  end.
  match goal with
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
      rename Halpha into Hrename
  end.
  match goal with
  | Hbody_eval : eval env (bind_params (fn_params fcall) vs (captured ++ s_args)) (fn_body fcall) s_body ret |- _ =>
      rename Hbody_eval into Heval_body
  end.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Sigma (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (typed_env_roots_shadow_safe_evar_store_named
    env Omega n R Sigma x (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed s Htyped_callee Hnamed Hkeys)
    as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    (PRE_Var x)) as Hcallee_names.
  assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
  { eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
  { eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  destruct (value_has_type_empty_closure_plain_tfn_non_generic
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique)
    as [Htype_params Hlifetimes].
  destruct (value_has_type_empty_closure_tfn_components
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique
    Htype_params Hlifetimes) as [Hcaps_fdef Hbridge].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
      env Omega n R1 Sigma1 Sigma' R' arg_roots args fdef fcall
      param_tys ret_ty s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Hargs.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  pose proof (eval_call_expr_tfn_components_final_store_eq_route_prefix_start
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_callee
    Htyped_args Hunique Htype_params Hlifetimes Hcallee_route) as Heq_final.
  exists s_fn, s_args, vs, fname.
  repeat split; assumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_final_store_eq_prefix_named :
  forall env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
      Sigma1 R1 roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty sigma ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives sigma bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      exists s_fn s_args vs fname,
        eval env s (EVar x) s_fn (VClosure fname []) /\
        eval_args env s_fn args s_args vs /\
        s' = s_args.
Proof.
  intros env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Hbody_shape
    Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary Heval_call Hunique.
  dependent destruction Heval_call.
  match goal with
  | Hcallee_eval : eval env s (EVar x) s_fn (VClosure fname captured) |- _ =>
      rename Hcallee_eval into Heval_callee
  end.
  match goal with
  | Hlookup_fn : lookup_fn fname (env_fns env) = Some fdef |- _ =>
      rename Hlookup_fn into Hlookup
  end.
  match goal with
  | Hargs_eval : eval_args env s_fn args s_args vs |- _ =>
      rename Hargs_eval into Heval_args
  end.
  match goal with
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
      rename Halpha into Hrename
  end.
  match goal with
  | Hbody_eval : eval env (bind_params (fn_params fcall) vs (captured ++ s_args)) (fn_body fcall) s_body ret |- _ =>
      rename Hbody_eval into Heval_body
  end.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Sigma (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (typed_env_roots_shadow_safe_evar_store_named
    env Omega n R Sigma x (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed s Htyped_callee Hnamed Hkeys)
    as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    (PRE_Var x)) as Hcallee_names.
  assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
  { eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
  { eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  destruct (value_has_type_empty_closure_tforall_tfn_components
    env s_fn fname fdef u m bounds body_ty param_tys ret_ty sigma
    Hv_callee Hlookup Hunique Hbody_shape) as [Htype_params [Hcaps_fdef Hbridge]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
      env Omega n R1 Sigma1 Sigma' R' arg_roots args fdef fcall
      (map (open_bound_ty sigma) param_tys) (open_bound_ty sigma ret_ty)
      s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Hargs.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  pose proof (eval_evar_call_expr_lifetime_forall_tfn_components_final_store_eq_prefix_start
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty sigma
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route) as Heq_final.
  exists s_fn, s_args, vs, fname.
  repeat split; assumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_frame_scope_prefix_named :
  forall env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
      roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys param_tys) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_frame_scope ps Sigma s frame ->
      store_frame_static_fresh Sigma frame ->
      frame_scope_roots_ready_result ps R' Sigma' s' frame.
Proof.
  intros env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope Hfresh.
  destruct (expr_root_shadow_store_safe_narrow_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1 roots_callee_typed
    arg_roots Sigma' R' Hargs Htyped_callee Htyped_args s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TFn param_tys ret_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hroots Hshadow Hrn
    Hscope Hfresh) as
    [Hcover_fn [Hroots_fn [Hshadow_fn [Hrn_fn [Hscope_fn Hfresh_fn]]]]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  pose proof (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys param_tys) Sigma' R' arg_roots ps frame
    Hprov_args Htyped_args_roots Hcover_fn Hroots_fn Hshadow_fn Hrn_fn
    Hscope_fn Hfresh_fn) as Hframe_args.
  rewrite Heq_final. exact Hframe_args.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_frame_scope_prefix_named :
  forall env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
      Sigma1 R1 roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty sigma ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives sigma bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_frame_scope ps Sigma s frame ->
      store_frame_static_fresh Sigma frame ->
      frame_scope_roots_ready_result ps R' Sigma' s' frame.
Proof.
  intros env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope Hfresh.
  destruct (expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TForall m bounds body_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hroots Hshadow Hrn
    Hscope Hfresh) as
    [Hcover_fn [Hroots_fn [Hshadow_fn [Hrn_fn [Hscope_fn Hfresh_fn]]]]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  pose proof (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots
    ps frame Hprov_args Htyped_args_roots Hcover_fn Hroots_fn Hshadow_fn
    Hrn_fn Hscope_fn Hfresh_fn) as Hframe_args.
  rewrite Heq_final. exact Hframe_args.
Qed.


Lemma store_safe_function_value_call_args_roots_shadow_safe_preserves_param_cover :
  forall env Omega n R Sigma args params Sigma' R' roots ps,
    store_safe_function_value_call_args env args ->
    typed_args_roots_shadow_safe env Omega n R Sigma args params
      Sigma' R' roots ->
    root_env_covers_params ps R ->
    root_env_covers_params ps R'.
Proof.
  intros env Omega n R Sigma args params Sigma' R' roots ps Hsafe.
  revert R Sigma params Sigma' R' roots ps.
  induction Hsafe as [| arg rest Harg Hsafe IH];
    intros R Sigma params Sigma' R' roots ps Htyped Hcover.
  - dependent destruction Htyped. exact Hcover.
  - dependent destruction Htyped.
    assert (Hcover1 : root_env_covers_params ps R1).
    { destruct Harg; dependent destruction H; exact Hcover. }
    eapply IH; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_param_scope_prefix_named :
  forall env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
      roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys param_tys) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope.
  destruct (expr_root_shadow_store_safe_narrow_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TFn param_tys ret_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hscope)
    as [frame_fn Hscope_fn].
  assert (Hcover_fn : root_env_covers_params ps R1).
  { dependent destruction Htyped_callee.
    all: exact Hcover. }
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_param_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys param_tys) Sigma' R' arg_roots ps frame_fn
    Hprov_args Htyped_args_roots Hcover_fn Hscope_fn) as [frame_args Hscope_args].
  rewrite Heq_final. exists frame_args. exact Hscope_args.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_param_scope_prefix_named :
  forall env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
      Sigma1 R1 roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty sigma ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives sigma bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope.
  destruct (expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TForall m bounds body_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hscope)
    as [frame_fn Hscope_fn].
  assert (Hcover_fn : root_env_covers_params ps R1).
  { dependent destruction Htyped_callee.
    all: exact Hcover. }
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_param_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots
    ps frame_fn Hprov_args Htyped_args_roots Hcover_fn Hscope_fn)
    as [frame_args Hscope_args].
  rewrite Heq_final. exists frame_args. exact Hscope_args.
Qed.


Lemma eval_expr_root_shadow_store_safe_narrow_summary_value_function_closure_targets_summary_prefix_named :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    env_fns_root_shadow_provenance_summary_evidence env ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      value_function_closure_targets_summary env ret.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hevidence Hsummary
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Heval Hunique.
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    env Omega n R Σ e T Σ' R' roots ret_roots Hsummary
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Heval Hunique)
    as [_ [Hv _]].
  eapply value_has_type_function_closure_targets_summary; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T
      Sigma' R' roots ret_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_frame_scope ps Sigma s frame ->
      store_frame_static_fresh Sigma frame ->
      frame_scope_roots_ready_result ps R' Sigma' s' frame.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret ps frame Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hcover Hscope Hfresh.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_frame_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_frame_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    dependent destruction H6.
    match goal with
    | Hcallee_eval : eval env s (EVar x) s_fn (VClosure fname captured) |- _ =>
        rename Hcallee_eval into Heval_callee
    end.
    match goal with
    | Hlookup_fn : lookup_fn fname (env_fns env) = Some fdef |- _ =>
        rename Hlookup_fn into Hlookup
    end.
    match goal with
    | Hargs_eval : eval_args env s_fn args s_args vs |- _ =>
        rename Hargs_eval into Heval_args
    end.
    match goal with
    | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
        rename Halpha into Hrename
    end.
    match goal with
    | Hbody_eval : eval env
        (bind_params (apply_type_params type_args (fn_params fcall)) vs
          (captured ++ s_args))
        (subst_type_params_expr type_args (fn_body fcall)) s_body ret |- _ =>
        rename Hbody_eval into Heval_body
    end.
    match goal with
    | Htyped_callee_call : typed_env_roots_shadow_safe _ _ _ _ _
        (EVar x) (MkTy _ (TTypeForall _ _ _)) _ _ _ |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          _ _ _ _ H3 Htyped_callee_call) as Hcore
    end.
    assert (Harity_call : Datatypes.length type_args = type_params).
    { eapply H5. rewrite Hcore. reflexivity. }
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 H6) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
    destruct (typed_env_roots_shadow_safe_evar_store_named
      env Omega n R Σ x (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 s H6 Hnamed Hkeys)
      as [Hnamed_fn_s [_ Hkeys_fn_s]].
    pose proof (proj1 preservation_ready_eval_store_names_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      (PRE_Var x)) as Hcallee_names.
    assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
    { eapply root_env_store_roots_named_store_names_eq; eassumption. }
    assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
    { eapply root_env_store_keys_named_store_names_eq; eassumption. }
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TTypeForall type_params bounds body_ty)) Hv_callee)
      as Hcaptured_nil.
    subst captured.
    simpl in Hrename, Heval_body.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary_store Heval_callee Hlookup)
      as Hcallee_summary.
    destruct (value_has_type_empty_closure_ttypeforall_tfn_components_closed
      env s_fn fname fdef u type_params bounds body_ty param_tys ret_inner
      type_args H0 Hv_callee Hlookup Hunique H7)
      as [Htype_params [_ [Hcaps_fdef Hbridge]]].
    assert (Harity_fdef : Datatypes.length type_args = fn_type_params fdef).
    { rewrite Htype_params. exact Harity_call. }
    pose proof (lookup_fn_in fname (env_fns env) fdef Hlookup) as Hin_fdef.
    pose proof
      (check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound
        inst_fuel env type_args H2 fdef Hin_fdef Harity_fdef)
      as Hnarrow_fdef.
    pose proof (typed_args_roots_shadow_safe_roots
      env Omega n R1 Σ1 args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots H9) as Htyped_args_roots.
    pose proof (preservation_ready_args_implies_provenance_ready_closure
      args (store_safe_function_value_call_args_preservation_ready env args H))
      as Hprov_args.
    assert (Hcallee_route :
        callee_body_root_shadow_provenance_ready_at_result_subset env
          (fn_subst_type_params type_args fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R')
          (root_sets_union arg_roots)).
    { eapply (generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_instantiated_narrow_tfn_with_result_subset_prefix_named
        env Omega n R1 Σ1 Σ' R' arg_roots args type_args fdef fcall
        (map (subst_type_params_ty type_args) param_tys)
        (subst_type_params_ty type_args ret_inner) s_fn s_args vs used').
      - exact Hcallee_summary.
      - exact Hnarrow_fdef.
      - exact Hcaps_fdef.
      - exact Hbridge.
      - exact H.
      - exact Htyped_args_roots.
      - exact Heval_args.
      - exact Hprov_args.
      - exact Hstore_fn.
      - exact Hroots_fn.
      - exact Hshadow_fn.
      - exact Hrn_fn.
      - exact Hnamed_fn.
      - exact Hkeys_fn.
      - exact Hrename. }
    pose proof (eval_call_expr_generic_ttypeforall_tfn_components_final_store_eq_route_prefix_start
      env s s_fn s_args s_body (EVar x) type_args args fname [] fdef fcall vs ret used'
      Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      type_params bounds body_ty param_tys ret_inner
      H0 (store_safe_function_value_call_args_preservation_ready env args H)
      (ProvReady_Var x)
      Hstore Hroots Hshadow Hrn H6 H7 H9 Hunique Hcallee_route) as Heq_final.
    destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
      env s (EVar x) s_fn (VClosure fname []) Heval_callee
      Omega n R Σ (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 ps frame
      (ProvReady_Var x) Htyped_callee_roots Hcover Hroots Hshadow Hrn
      Hscope Hfresh) as
      [Hcover_fn [Hroots_fn_frame [Hshadow_fn_frame
        [Hrn_fn_frame [Hscope_fn Hfresh_fn]]]]].
    destruct (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
      env s_fn args s_args vs Heval_args Omega n R1 Σ1
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots ps frame Hprov_args Htyped_args_roots Hcover_fn
      Hroots_fn_frame Hshadow_fn_frame Hrn_fn_frame Hscope_fn Hfresh_fn) as
      [Hcover_args [Hroots_args [Hshadow_args [Hrn_args [Hscope_args Hfresh_args]]]]].
    rewrite Heq_final.
    repeat split; assumption.
  - dependent destruction Heval.
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1
      s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
      Heval1 Hunique)
      as [Hstore1 [Hv1 [Hpres1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]]].
    destruct (IHHsummary1 s s1 v1 ps frame Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Hsummary_store Heval1 Hunique Hcover Hscope Hfresh)
      as [Hcover1 [Hroots1_frame [Hshadow1_frame
        [Hrn1_frame [Hscope1 Hfresh1]]]]].
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H1) as Hnotin.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hnot_frame : ~ In x (store_names frame))
      by (eapply store_frame_scope_lookup_absent_in_frame; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply store_add_roots_within.
      - exact Hroots1_runtime.
      - exact H1.
      - exact Hv1_roots. }
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_roots_named_add_env_store_add.
      - exact Hnamed1.
      - exact Hroots1_named. }
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_keys_named_add_env_store_add.
      - exact Hkeys1. }
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function.
      - exact Hsummary1_store.
      - exact Hv1_hidden.
      - exact H0. }
    assert (Hcover_add :
      root_env_covers_params ps (root_env_add x roots1 R1))
      by (apply root_env_covers_params_add; exact Hcover1).
    assert (Hscope_add :
      store_frame_scope ps (sctx_add x T_hidden m Σ1)
        (store_add x T_hidden v1 s1) frame).
    { eapply store_frame_scope_add_weaken.
      - exact Hnotin.
      - simpl. left. reflexivity.
      - intros y Hy. simpl. right. exact Hy.
      - exact Hscope1. }
    assert (Hfresh_add :
      store_frame_static_fresh (sctx_add x T_hidden m Σ1) frame).
    { eapply store_frame_static_fresh_add.
      - exact Hfresh1.
      - exact Hnot_frame. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2 ps frame
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique Hcover_add Hscope_add Hfresh_add)
      as [Hcover2 [Hroots2 [Hshadow2 [Hrn2 [Hscope2 Hfresh2]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2)).
    { eapply store_remove_roots_within.
      - exact Hroots2.
      - exact Hremove_names. }
    assert (Hin_x_Sigma2 : In x (ctx_names Sigma2)).
    { pose proof (expr_root_shadow_store_safe_narrow_summary_typed
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2
        ret_roots Hsummary2) as Htyped_body.
      pose proof (typed_env_structural_same_bindings env Omega n
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2
        (typed_env_roots_structural env Omega n
          (root_env_add x roots1 R1) (sctx_add x T_hidden m Σ1)
          e2 T2 Sigma2 R2 roots2
          (typed_env_roots_shadow_safe_roots env Omega n
            (root_env_add x roots1 R1) (sctx_add x T_hidden m Σ1)
            e2 T2 Sigma2 R2 roots2 Htyped_body))) as Hsame_body.
      pose proof (sctx_same_bindings_names_alpha
        (sctx_add x T_hidden m Σ1) Sigma2 Hsame_body) as Hnames.
      rewrite Hnames. simpl. left. reflexivity. }
    repeat split.
    + eapply root_env_covers_params_remove_non_param.
      * exact Hcover2.
      * exact Hnotin.
    + exact Hroots_removed.
    + apply store_no_shadow_remove. exact Hshadow2.
    + apply root_env_no_shadow_remove. exact Hrn2.
    + eapply store_frame_scope_remove_non_param_sctx_remove.
      * exact Hin_x_Sigma2.
      * exact Hshadow2.
      * exact Hfresh2.
      * exact Hscope2.
      * exact Hnotin.
    + apply store_frame_static_fresh_remove. exact Hfresh2.
  - dependent destruction Heval.
  - inversion Heval; subst.
    inversion H; subst; try congruence;
      repeat split; try exact Hcover; try exact Hroots; try exact Hshadow;
      try exact Hrn; try exact Hscope; try exact Hfresh.
  - inversion Heval; subst.
    inversion H; subst; try congruence;
      repeat split; try exact Hcover; try exact Hroots; try exact Hshadow;
      try exact Hrn; try exact Hscope; try exact Hfresh.
  - inversion Heval; subst.
    inversion H; subst; try congruence;
      repeat split; try exact Hcover; try exact Hroots; try exact Hshadow;
      try exact Hrn; try exact Hscope; try exact Hfresh.
  - assert (Hempty_shape : Σ' = Σ /\ R' = R).
    { inversion H1; subst; try congruence.
      match goal with
      | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          dependent destruction Hfields
      end.
      repeat split; reflexivity. }
    destruct Hempty_shape as [HSigma HR]. subst Σ' R'.
    assert (Hs_eq : s' = s).
    { inversion Heval; subst.
      eapply eval_struct_fields_empty_exprs_store_eq; eassumption. }
    subst s'.
    repeat split; try exact Hcover; try exact Hroots; try exact Hshadow;
      try exact Hrn; try exact Hscope; try exact Hfresh.
  - destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
      env Omega n R Σ (EAssign p (ELit lit)) T Σ' R' roots roots
      (ERSSN_AssignLit env Omega n R Σ p lit T Σ' R' roots H)
      s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
      Heval Hunique)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hrootset_named
        [Hshadow' [Hrn' [Hnamed' [Hkeys' Hsummary']]]]]]]]]].
    inversion Heval; subst;
      match goal with
      | Hlit : eval _ _ (ELit _) _ _ |- _ => inversion Hlit; subst
      end;
      inversion H; subst; try congruence;
      match goal with
      | Hlit_typed : typed_env_roots_shadow_safe _ _ _ _ _ (ELit _) _ _ _ _ |- _ =>
          inversion Hlit_typed; subst
      end;
      repeat split;
      try (apply root_env_covers_params_update; exact Hcover);
      try exact Hroots'; try exact Hshadow'; try exact Hrn'; try exact Hfresh.
    all: try solve [eapply store_frame_scope_update_val; try eassumption;
      eapply sctx_lookup_mut_in_ctx_names; eassumption].
    all: try solve [eapply store_frame_scope_update_path; try eassumption;
      eapply sctx_lookup_mut_in_ctx_names; eassumption].
    all: try solve [eapply store_frame_scope_update_val; try eassumption;
      match goal with
      | Htyped_place : typed_place_env_structural _ _ (PVar ?xv) _ |- In ?xv _ =>
          inversion Htyped_place; subst; eapply sctx_lookup_in_ctx_names; eassumption
      | Htyped_place : typed_place_env_structural _ _ ?p0 _,
        Hpath : place_path ?p0 = Some (?x0, _) |- In ?x0 _ =>
          rewrite <- (place_path_root_provenance_place_name p0 x0 _ Hpath);
          eapply typed_place_root_name_in_ctx_names; exact Htyped_place
      end].
    all: try solve [
      match goal with
      | Heval_place : eval_place _ ?p0 ?xv ?pathv,
        Hpath : place_path ?p0 = Some (?x0, ?path0) |- _ =>
          destruct (eval_place_matches_place_path _ _ _ _ _ _ Heval_place Hpath)
            as [Hxv Hpathv]; subst xv pathv
      | Heval_place : eval_place _ ?p0 ?xv ?pathv,
        Htarget : place_resolved_write_target ?Rtarget ?p0 = Some ?x0 |- _ =>
          assert (Hxv : xv = x0) by
            (eapply eval_place_resolved_write_target_matches_root;
             [exact Hroots | exact Heval_place | exact Htarget]);
          subst xv
      end;
      eapply store_frame_scope_update_path; try eassumption;
      match goal with
      | Htyped_place : typed_place_env_structural _ _ ?p0 _,
        Hpath : place_path ?p0 = Some (?x0, _) |- In ?x0 _ =>
          rewrite <- (place_path_root_provenance_place_name p0 x0 _ Hpath);
          eapply typed_place_root_name_in_ctx_names; exact Htyped_place
      | Hmut : sctx_lookup_mut ?x0 _ = Some MMutable |- In ?x0 _ =>
          eapply sctx_lookup_mut_in_ctx_names; exact Hmut
      end].
  - assert (Hnarrow : expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EAssign (PVar x) (ECallGeneric fname type_args []))
        T Σ' R' roots roots).
    { eapply ERSSN_AssignGenericDirect; eassumption. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
      env Omega n R Σ (EAssign (PVar x) (ECallGeneric fname type_args []))
      T Σ' R' roots roots Hnarrow s s' ret Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Hsummary_store Heval Hunique)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hrootset_named
        [Hshadow' [Hrn' [Hnamed' [Hkeys' Hsummary']]]]]]]]]].
    assert (Hassign_in : In x (ctx_names Σ)).
    { inversion H10; subst; simpl in *; try congruence.
      match goal with
      | Htyped_place : typed_place_env_structural _ _ (PVar x) _ |- _ =>
          inversion Htyped_place; subst;
          eapply sctx_lookup_in_ctx_names; eassumption
      end. }
    inversion H10; subst; simpl in *; try congruence.
    match goal with
    | Hcall_typed : typed_env_roots_shadow_safe _ _ _ _ _
        (ECallGeneric _ _ []) _ _ _ _ |- _ =>
        destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
          _ _ _ _ _ _ _ _ _ _ _ _ Hcall_typed)
          as (_f & _sigma & _arg_roots & _Hin & _Hname & _Hcaps & _Harity &
              _Hbounds & Hargs_typed & _Houtlives & _Hret & _Hroots);
        dependent destruction Hargs_typed;
        subst; simpl in *
    end.
    inversion Heval; subst; try discriminate;
      repeat match goal with
      | Hcall_eval : eval env ?s_base
          (ECallGeneric (fn_name fcallee) type_args []) ?s_call ?v_call |- _ =>
          destruct (eval_call_generic_empty_struct_no_params_store_eq
            env s_base s_call (fn_name fcallee) type_args fcallee
            sname lts tys v_call Hunique H eq_refl H3 H5 Hcall_eval)
            as [Hcall_store Hcall_value];
          subst s_call; subst v_call; clear Hcall_eval
      end;
      repeat match goal with
      | Hplace : eval_place ?s_eval ?p_eval ?x_eval ?path_eval |- _ => inversion Hplace; subst; clear Hplace
      end;
      repeat match goal with
      | Hupd_path : store_update_path ?xv [] ?v ?s0 = Some ?s1 |- _ =>
          rewrite store_update_path_nil_update_val in Hupd_path
      end;
      repeat split;
      try (apply root_env_covers_params_update; exact Hcover);
      try exact Hroots'; try exact Hshadow'; try exact Hrn'; try exact Hfresh.
    all: match goal with
      | Hupdate_val : store_update_val ?xv _ _ = Some _ |- _ =>
          eapply store_frame_scope_update_val with (x := xv); try eassumption
      end.
    all: exact Hassign_in.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) T Σ' R' roots H) as Htyped_roots.
    eapply (proj1 eval_preserves_frame_scope_roots_ready_mutual);
      try eassumption.
    apply ProvReady_Var.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots H) as Htyped_roots.
    eapply (proj1 eval_preserves_frame_scope_roots_ready_mutual);
      try eassumption.
    apply ProvReady_Drop. eapply ProvReady_Place_Direct. exact H0.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_preserves_param_cover :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T
      Sigma' R' roots ret_roots ->
    forall ps,
      root_env_covers_params ps R ->
      root_env_covers_params ps R'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary; intros ps Hcover.
  - dependent destruction H2;
      match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          _ _ ?R_args _,
        Htyped_args : typed_args_roots_shadow_safe _ _ _ ?R_args _ args
          _ _ ?R_final _ |- root_env_covers_params _ ?R_final =>
          assert (Hcover_args : root_env_covers_params ps R_args)
            by (dependent destruction Htyped_callee; exact Hcover);
          eapply store_safe_function_value_call_args_roots_shadow_safe_preserves_param_cover;
            [exact H | exact Htyped_args | exact Hcover_args]
      end.
  - dependent destruction H6.
    assert (Hcover_args : root_env_covers_params ps R1).
    { inversion H6; subst; try exact Hcover. }
    eapply store_safe_function_value_call_args_roots_shadow_safe_preserves_param_cover;
      [exact H | eassumption | exact Hcover_args].
  - pose proof (IHHsummary1 ps Hcover) as Hcover1.
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H1) as Hnotin.
    pose proof (root_env_covers_params_add
      ps R1 x roots1 Hcover1) as Hcover_add.
    pose proof (IHHsummary2 ps Hcover_add) as Hcover2.
    eapply root_env_covers_params_remove_non_param; eassumption.
  - pose proof (IHHsummary1 ps Hcover) as Hcover1.
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H0) as Hnotin.
    pose proof (root_env_covers_params_add
      ps R1 x roots1 Hcover1) as Hcover_add.
    pose proof (IHHsummary2 ps Hcover_add) as Hcover2.
    eapply root_env_covers_params_remove_non_param; eassumption.
  - inversion H; subst; try congruence; exact Hcover.
  - inversion H; subst; try congruence; exact Hcover.
  - inversion H; subst; try congruence; exact Hcover.
  - inversion H1; subst; try congruence.
    match goal with
    | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        dependent destruction Hfields
    end.
    exact Hcover.
  - inversion H; subst; try congruence;
      match goal with
      | Hlit_typed : typed_env_roots_shadow_safe _ _ _ _ _ (ELit _) _ _ _ _ |- _ =>
          inversion Hlit_typed; subst
      end;
      apply root_env_covers_params_update; exact Hcover.
  - inversion H10; subst; simpl in *; try congruence.
    match goal with
    | Hcall_typed : typed_env_roots_shadow_safe _ _ _ _ _
        (ECallGeneric _ _ []) _ _ _ _ |- _ =>
        destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
          _ _ _ _ _ _ _ _ _ _ _ _ Hcall_typed)
          as (_f & _sigma & _arg_roots & _Hin & _Hname & _Hcaps & _Harity &
              _Hbounds & Hargs_typed & _Houtlives & _Hret & _Hroots);
        dependent destruction Hargs_typed;
        subst; simpl in *
    end.
    apply root_env_covers_params_update. exact Hcover.
  - inversion H; subst; try congruence; exact Hcover.
  - inversion H; subst; try congruence.
    match goal with
    | Hplace_typed : typed_env_roots_shadow_safe _ _ _ _ _ (EPlace _) _ _ _ _ |- _ =>
        inversion Hplace_typed; subst; try congruence; exact Hcover
    end.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T Sigma' R' roots ret_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma -> store_roots_within R s -> store_no_shadow s -> root_env_no_shadow R ->
      root_env_store_roots_named R s -> root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s -> eval env s e s' ret -> fn_env_unique_by_name env ->
      root_env_covers_params ps R -> store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret ps frame Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hcover Hscope.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_param_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_param_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    dependent destruction H6.
    match goal with
    | Hcallee_eval : eval env s (EVar x) s_fn (VClosure fname captured) |- _ =>
        rename Hcallee_eval into Heval_callee
    end.
    match goal with
    | Hlookup_fn : lookup_fn fname (env_fns env) = Some fdef |- _ =>
        rename Hlookup_fn into Hlookup
    end.
    match goal with
    | Hargs_eval : eval_args env s_fn args s_args vs |- _ =>
        rename Hargs_eval into Heval_args
    end.
    match goal with
    | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
        rename Halpha into Hrename
    end.
    match goal with
    | Hbody_eval : eval env
        (bind_params (apply_type_params type_args (fn_params fcall)) vs
          (captured ++ s_args))
        (subst_type_params_expr type_args (fn_body fcall)) s_body ret |- _ =>
        rename Hbody_eval into Heval_body
    end.
    match goal with
    | Htyped_callee_call : typed_env_roots_shadow_safe _ _ _ _ _
        (EVar x) (MkTy _ (TTypeForall _ _ _)) _ _ _ |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          _ _ _ _ H3 Htyped_callee_call) as Hcore
    end.
    assert (Harity_call : Datatypes.length type_args = type_params).
    { eapply H5. rewrite Hcore. reflexivity. }
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 H6) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
    destruct (typed_env_roots_shadow_safe_evar_store_named
      env Omega n R Σ x (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 s H6 Hnamed Hkeys)
      as [Hnamed_fn_s [_ Hkeys_fn_s]].
    pose proof (proj1 preservation_ready_eval_store_names_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      (PRE_Var x)) as Hcallee_names.
    assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
    { eapply root_env_store_roots_named_store_names_eq; eassumption. }
    assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
    { eapply root_env_store_keys_named_store_names_eq; eassumption. }
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TTypeForall type_params bounds body_ty)) Hv_callee)
      as Hcaptured_nil.
    subst captured.
    simpl in Hrename, Heval_body.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary_store Heval_callee Hlookup)
      as Hcallee_summary.
    destruct (value_has_type_empty_closure_ttypeforall_tfn_components_closed
      env s_fn fname fdef u type_params bounds body_ty param_tys ret_inner
      type_args H0 Hv_callee Hlookup Hunique H7)
      as [Htype_params [_ [Hcaps_fdef Hbridge]]].
    assert (Harity_fdef : Datatypes.length type_args = fn_type_params fdef).
    { rewrite Htype_params. exact Harity_call. }
    pose proof (lookup_fn_in fname (env_fns env) fdef Hlookup) as Hin_fdef.
    pose proof
      (check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound
        inst_fuel env type_args H2 fdef Hin_fdef Harity_fdef)
      as Hnarrow_fdef.
    pose proof (typed_args_roots_shadow_safe_roots
      env Omega n R1 Σ1 args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots H9) as Htyped_args_roots.
    pose proof (preservation_ready_args_implies_provenance_ready_closure
      args (store_safe_function_value_call_args_preservation_ready env args H))
      as Hprov_args.
    assert (Hcallee_route :
        callee_body_root_shadow_provenance_ready_at_result_subset env
          (fn_subst_type_params type_args fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R')
          (root_sets_union arg_roots)).
    { eapply (generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_instantiated_narrow_tfn_with_result_subset_prefix_named
        env Omega n R1 Σ1 Σ' R' arg_roots args type_args fdef fcall
        (map (subst_type_params_ty type_args) param_tys)
        (subst_type_params_ty type_args ret_inner) s_fn s_args vs used').
      - exact Hcallee_summary.
      - exact Hnarrow_fdef.
      - exact Hcaps_fdef.
      - exact Hbridge.
      - exact H.
      - exact Htyped_args_roots.
      - exact Heval_args.
      - exact Hprov_args.
      - exact Hstore_fn.
      - exact Hroots_fn.
      - exact Hshadow_fn.
      - exact Hrn_fn.
      - exact Hnamed_fn.
      - exact Hkeys_fn.
      - exact Hrename. }
    pose proof (eval_call_expr_generic_ttypeforall_tfn_components_final_store_eq_route_prefix_start
      env s s_fn s_args s_body (EVar x) type_args args fname [] fdef fcall vs ret used'
      Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      type_params bounds body_ty param_tys ret_inner
      H0 (store_safe_function_value_call_args_preservation_ready env args H)
      (ProvReady_Var x)
      Hstore Hroots Hshadow Hrn H6 H7 H9 Hunique Hcallee_route) as Heq_final.
    destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
      env s (EVar x) s_fn (VClosure fname []) Heval_callee
      Omega n R Σ (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 ps frame
      (ProvReady_Var x) Htyped_callee_roots Hcover Hscope)
      as [frame_fn Hscope_fn].
    assert (Hcover_fn : root_env_covers_params ps R1).
    { inversion H6; subst; try exact Hcover. }
    destruct (proj1 (proj2 eval_preserves_param_scope_roots_ready_mutual)
      env s_fn args s_args vs Heval_args Omega n R1 Σ1
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots ps frame_fn Hprov_args Htyped_args_roots
      Hcover_fn Hscope_fn) as [frame_args Hscope_args].
    rewrite Heq_final. exists frame_args. exact Hscope_args.
  - dependent destruction Heval.
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1
      s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
      Heval1 Hunique)
      as [Hstore1 [Hv1 [Hpres1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]]].
    pose proof (expr_root_shadow_store_safe_narrow_summary_preserves_param_cover
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1
      ps Hcover) as Hcover1.
    destruct (IHHsummary1 s s1 v1 ps frame Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Hsummary_store Heval1 Hunique Hcover Hscope)
      as [frame1 Hscope1].
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H1) as Hnotin.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply store_add_roots_within.
      - exact Hroots1_runtime.
      - exact H1.
      - exact Hv1_roots. }
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_roots_named_add_env_store_add.
      - exact Hnamed1.
      - exact Hroots1_named. }
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_keys_named_add_env_store_add.
      - exact Hkeys1. }
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function.
      - exact Hsummary1_store.
      - exact Hv1_hidden.
      - exact H0. }
    assert (Hcover_add :
      root_env_covers_params ps (root_env_add x roots1 R1))
      by (apply root_env_covers_params_add; exact Hcover1).
    assert (Hscope_add :
      store_param_scope ps (store_add x T_hidden v1 s1) frame1).
    { eapply store_param_scope_add.
      - exact Hnotin.
      - exact Hscope1. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2 ps frame1
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique Hcover_add Hscope_add) as [frame2 Hscope2].
    eapply store_param_scope_remove_non_param; eassumption.
  - dependent destruction Heval.
  - inversion Heval; subst. exists frame. inversion H; subst; try congruence; exact Hscope.
  - inversion Heval; subst. exists frame. inversion H; subst; try congruence; exact Hscope.
  - inversion Heval; subst. exists frame. inversion H; subst; try congruence; exact Hscope.
  - assert (Hs_eq : s' = s).
    { inversion Heval; subst.
      eapply eval_struct_fields_empty_exprs_store_eq; eassumption. }
    subst s'. exists frame. exact Hscope.
  - inversion Heval; subst;
      match goal with
      | Hlit : eval _ _ (ELit _) _ _ |- _ => inversion Hlit; subst
      end.
    all: eauto using store_param_scope_update_val, store_param_scope_update_path.
  - inversion Heval; subst; try discriminate;
      repeat match goal with
      | Hcall_eval : eval env ?s_base
          (ECallGeneric (fn_name fcallee) type_args []) ?s_call ?v_call |- _ =>
          destruct (eval_call_generic_empty_struct_no_params_store_eq
            env s_base s_call (fn_name fcallee) type_args fcallee
            sname lts tys v_call Hunique H eq_refl H3 H5 Hcall_eval)
            as [Hcall_store Hcall_value];
          subst s_call; subst v_call; clear Hcall_eval
      end;
      repeat match goal with
      | Hplace : eval_place ?s_eval ?p_eval ?x_eval ?path_eval |- _ =>
          inversion Hplace; subst; clear Hplace
      end;
      repeat match goal with
      | Hupd_path : store_update_path ?xv [] ?v ?s0 = Some ?s1 |- _ =>
          rewrite store_update_path_nil_update_val in Hupd_path
      end;
      eauto using store_param_scope_update_val.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) T Σ' R' roots H) as Htyped_roots.
    eapply (proj1 eval_preserves_param_scope_roots_ready_mutual);
      try eassumption.
    apply ProvReady_Var.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots H) as Htyped_roots.
    eapply (proj1 eval_preserves_param_scope_roots_ready_mutual);
      try eassumption.
    apply ProvReady_Drop. eapply ProvReady_Place_Direct. exact H0.
Qed.


Lemma eval_direct_call_store_safe_narrow_summary_value_prefix_named :
  forall env Omega n R Sigma fname args sigma Sigma_args R_args arg_roots
      s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary env fdef ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECall fname args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    fn_type_params fdef = 0 ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret (apply_lt_ty sigma (fn_ret fdef)).
Proof.
  intros env Omega n R Sigma fname args sigma Sigma_args R_args arg_roots
    s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef Hcaps_fdef
    Htype_params Htyped_args Houtlives.
  dependent destruction Heval_call.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  | Hlookup_fn : lookup_fn ?fname_call ?fns = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  end.
  match goal with
  | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
      rename H into Heval_args;
      rename s_args0 into s_args;
      rename vs0 into vs
  end.
  match goal with
  | H : alpha_rename_fn_def (store_names s_args) fdef =
        (?fcall0, ?used0) |- _ =>
      rename H into Hrename;
      rename fcall0 into fcall;
      rename used0 into used'
  end.
  match goal with
  | H : eval _ (bind_params (fn_params fcall) vs s_args)
        (fn_body fcall) ?s_body0 ret |- _ =>
      rename H into Heval_body;
      rename s_body0 into s_body
  end.
  pose proof (typed_args_roots_params_of_tys_map_param_ty
    env Omega n R Sigma args (apply_lt_params sigma (fn_params fdef))
    Sigma_args R_args arg_roots Htyped_args) as Htyped_args_param_tys.
  pose proof (runtime_tfn_signature_bridge_apply_lt_params
    sigma (fn_params fdef) (fn_ret fdef)) as Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
    env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args Hready_args) as Hprov_args.
  destruct (direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    (map param_ty (apply_lt_params sigma (fn_params fdef)))
    (apply_lt_ty sigma (fn_ret fdef)) s s_args vs used'
    Hsummary Hcaps_fdef Hbridge Hsafe_args Htyped_args_param_tys Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
    as [Hstore_args [Hargs_values_sigma [Hpres_args
        [Hroots_args [_ [Hshadow_args Hrn_args]]]]]].
  assert (Hargs_values_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_values_sigma. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hargs_values_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Omega n R Sigma
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots (fn_params fcall) Heval_args Hprov_args Htyped_args
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_values_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hsummary_bind :
    store_function_closure_targets_summary env
      (bind_params (fn_params fcall) vs s_args)).
  { eapply store_safe_function_value_call_args_bind_params_summary;
      eassumption. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Hsummary_body_env :
    expr_root_shadow_store_safe_narrow_summary body_env
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots).
  { subst body_env.
    eapply expr_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds.
    - exact Hunique.
    - exact Hsummary_body. }
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hsummary_bind_body_env :
    store_function_closure_targets_summary body_env
      (bind_params (fn_params fcall) vs s_args)).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    exact Hsummary_bind. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R_args)
    (sctx_of_ctx (params_ctx (fn_params fcall)))
    (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots
    Hsummary_body_env
    (bind_params (fn_params fcall) vs s_args) s_body ret
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
      [Hrootset_body [Hshadow_body [Hrn_body [Hnamed_body
        [Hkeys_body Hsummary_body_store]]]]]]]]]].
  assert (Hframe_start :
    store_param_scope (fn_params fcall)
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_param_scope_bind_params. exact Hargs_values_fcall. }
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R_args)
    (sctx_of_ctx (params_ctx (fn_params fcall)))
    (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots
    Hsummary_body_env
    (bind_params (fn_params fcall) vs s_args) s_body ret
    (fn_params fcall) s_args Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Hsummary_bind_body_env
    Heval_body_body_env Hunique_body_env Hcover_bind Hframe_start)
    as [frame_final Hscope_body].
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret_alpha. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              (fn_params fcall) s_body frame_final R_body roots_body ret
              Hscope_body Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty sigma (fn_ret fdef))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  exact Hv_final.
Qed.

Definition callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_store_safe_narrow_summary env fcallee /\
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

Inductive callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (env : global_env) : nat -> fn_def -> list Ty -> Prop :=
  | CBRSSNI_Expr : forall fuel fdef type_args T_body Gamma_out R_body
      roots_body ret_roots,
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) ->
      expr_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots ->
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true ->
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body ->
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env fuel fdef type_args
  | CBRSSNI_GenericDirect : forall fuel fdef type_args fname
      nested_type_args args raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
      raw_body = subst_type_params_expr type_args (fn_body fdef) ->
      generic_direct_call_target_expr raw_body =
        Some (fname, nested_type_args, args, synthetic_body) ->
      synthetic_body = ECallGeneric fname nested_type_args args ->
      store_safe_function_value_call_args env args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      Datatypes.length nested_type_args = fn_type_params fcallee ->
      check_struct_bounds
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_bounds fcallee) nested_type_args = None ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env fuel fcallee nested_type_args ->
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) ->
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true ->
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body ->
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env (S fuel) fdef type_args.

Lemma check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound :
  forall fuel env fdef type_args,
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      fuel env fdef type_args = true ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args.
Proof.
  induction fuel as [| fuel' IH]; intros env fdef type_args Hcheck.
  - simpl in Hcheck. discriminate.
  - cbn [check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel]
      in Hcheck.
    remember (subst_type_params_ctx type_args (fn_body_ctx fdef)) as body_ctx.
    remember (subst_type_params_expr type_args (fn_body fdef)) as body.
    remember (apply_type_params type_args (fn_params fdef)) as params.
    remember (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef))) as body_env.
    destruct (infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef))
      as [[[[T_env Gamma_env] R_env] roots_env] | err_env] eqn:Henv;
      try discriminate.
    apply orb_true_iff in Hcheck as [Hexact | Hgeneric].
    + destruct (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel_exact_sound
        (S fuel') env fdef type_args Hexact) as
        (T_body & Gamma_out & R_body & roots_body & ret_roots & Hnodup &
          Hsummary & Hcompat & Hroots & Hroot_env).
      eapply CBRSSNI_Expr; eassumption.
    + destruct (generic_direct_call_target_expr body)
        as [[[[fname nested_type_args] args] synthetic_body] |] eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hgeneric as [Hsafe_args Hgeneric].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      apply andb_true_iff in Hgeneric as [Harity Hgeneric].
      apply Nat.eqb_eq in Harity.
      destruct (check_struct_bounds body_env
        (fn_bounds fcallee) nested_type_args) as [bounds_err |] eqn:Hbounds;
        try discriminate.
      destruct (infer_core_env_roots_shadow_safe body_env
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef) body_ctx synthetic_body)
        as [[[[T_body Gamma_out] R_body] roots_body] | err_body]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hgeneric.
      destruct Hgeneric as [[[Hrecursive Hcompat] Hroots] Hroot_env].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      specialize (IH env fcallee nested_type_args Hrecursive).
      pose proof (infer_core_env_roots_shadow_safe_sound body_env
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef) body_ctx synthetic_body
        T_body Gamma_out R_body roots_body Hbody_env) as Htyped_body.
      subst body_ctx params body_env.
      eapply CBRSSNI_GenericDirect with
        (raw_body := body) (synthetic_body := synthetic_body)
        (fcallee := fcallee) (T_body := T_body)
        (Gamma_out := Gamma_out) (R_body := R_body)
        (roots_body := roots_body).
      * subst body. reflexivity.
      * exact Htarget.
      * subst body. unfold generic_direct_call_target_expr in Htarget.
        destruct (subst_type_params_expr type_args (fn_body fdef));
          try discriminate.
        inversion Htarget. reflexivity.
      * apply store_safe_function_value_call_args_b_sound. exact Hsafe_args.
      * exact Hin_callee.
      * exact Hname_callee.
      * exact Harity.
      * exact Hbounds.
      * exact IH.
      * rewrite params_ctx_apply_type_params.
        rewrite ctx_names_subst_type_params_ctx.
        eapply infer_env_roots_shadow_safe_params_nodup. exact Henv.
      * exact Htyped_body.
      * exact Hcompat.
      * apply fn_params_roots_exclude_b_sound. exact Hroots.
      * apply fn_params_root_env_excludes_b_sound. exact Hroot_env.
Qed.

Lemma check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound :
  forall env fdef type_args,
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args = true ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fdef type_args.
Proof.
  intros env fdef type_args Hcheck.
  unfold check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
    in Hcheck.
  eapply check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound.
  exact Hcheck.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds :
  forall env bounds fuel fdef type_args,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      (global_env_with_local_bounds env bounds) fuel fdef type_args.
Proof.
  intros env bounds fuel fdef type_args Hunique Hsummary.
  revert bounds.
  induction Hsummary; intros bounds.
  - eapply CBRSSNI_Expr.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
  - eapply CBRSSNI_GenericDirect with
      (raw_body := raw_body) (synthetic_body := synthetic_body)
      (fcallee := fcallee) (T_body := T_body)
      (Gamma_out := Gamma_out) (R_body := R_body)
      (roots_body := roots_body).
    + exact H.
    + exact H0.
    + exact H1.
    + apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact H2.
    + change (env_fns (global_env_with_local_bounds env bounds))
        with (env_fns env).
      exact H3.
    + exact H4.
    + exact H5.
    + change (check_struct_bounds
        (global_env_with_local_bounds
          (global_env_with_local_bounds env bounds)
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_bounds fcallee) nested_type_args)
        with (check_struct_bounds
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
          (fn_bounds fcallee) nested_type_args).
      exact H6.
    + apply IHHsummary.
    + exact H7.
    + change (typed_env_roots_shadow_safe
        (global_env_with_local_bounds
          (global_env_with_local_bounds env bounds)
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body)
        with (typed_env_roots_shadow_safe
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
          (fn_outlives fdef) (fn_lifetimes fdef)
          (initial_root_env_for_fn fdef)
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
          synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body).
      exact H8.
    + exact H9.
    + exact H10.
    + exact H11.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases :
  forall env fuel fdef type_args,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    (exists T_body Gamma_out R_body roots_body ret_roots,
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) /\
      expr_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots /\
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true /\
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body /\
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body) \/
    (exists fuel' fname nested_type_args args raw_body synthetic_body fcallee
        T_body Gamma_out R_body roots_body,
      fuel = S fuel' /\
      raw_body = subst_type_params_expr type_args (fn_body fdef) /\
      generic_direct_call_target_expr raw_body =
        Some (fname, nested_type_args, args, synthetic_body) /\
      synthetic_body = ECallGeneric fname nested_type_args args /\
      store_safe_function_value_call_args env args /\
      In fcallee (env_fns env) /\
      fn_name fcallee = fname /\
      Datatypes.length nested_type_args = fn_type_params fcallee /\
      check_struct_bounds
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_bounds fcallee) nested_type_args = None /\
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env fuel' fcallee nested_type_args /\
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) /\
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true /\
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body /\
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body).
Proof.
  intros env fuel fdef type_args Hsummary.
  inversion Hsummary; subst.
  - left. repeat eexists; repeat split; eauto.
  - right. repeat eexists; repeat split; eauto.
Qed.


Lemma generic_direct_call_target_expr_preservation_ready_false :
  forall e fname type_args args synthetic_body,
    generic_direct_call_target_expr e =
      Some (fname, type_args, args, synthetic_body) ->
    preservation_ready_expr e ->
    False.
Proof.
  intros e fname type_args args synthetic_body Htarget Hready.
  unfold generic_direct_call_target_expr in Htarget.
  destruct e; try discriminate.
  dependent destruction Hready.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_ready :
  forall env fuel fdef type_args,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fdef)) ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args.
Proof.
  intros env fuel fdef type_args Hsummary Hready.
  destruct (callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases
    env fuel fdef type_args Hsummary) as [Hexpr | Hgeneric].
  - exact Hexpr.
  - destruct Hgeneric as (fuel' & fname & nested_type_args & args & raw_body &
      synthetic_body & fcallee & T_body & Gamma_out & R_body & roots_body &
      Hfuel & Hbody & Htarget & Hsynthetic & Hsafe & Hin & Hname & Harity &
      Hbounds & Hnested & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
    subst raw_body.
    exfalso.
    eapply generic_direct_call_target_expr_preservation_ready_false;
      eassumption.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero :
  forall env fdef type_args,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 0 fdef type_args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args.
Proof.
  intros env fdef type_args Hsummary.
  inversion Hsummary; subst; try discriminate.
  unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated.
  repeat eexists; repeat split; eauto.
Qed.

Lemma generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args type_args fdef fcall param_tys ret_ty s s_args vs used' seed,
      callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fdef type_args ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (apply_type_params type_args (fn_params fdef)))
        (subst_type_params_ty type_args (fn_ret fdef)) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      (forall y, In y (store_names s_args) -> In y seed) ->
      alpha_rename_fn_def seed fdef = (fcall, used') ->
      exists T_body Sigma_out R_body roots_body ret_roots,
        expr_root_shadow_store_safe_narrow_summary
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall)))
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R_args)
          (sctx_of_ctx (params_ctx
            (apply_type_params type_args (fn_params fcall))))
          (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
          R_body roots_body ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body
          (subst_type_params_ty type_args (fn_ret fcall)) = true /\
        roots_exclude_params (apply_type_params type_args (fn_params fcall))
          roots_body /\
        root_env_excludes_params
          (apply_type_params type_args (fn_params fcall)) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args type_args
    fdef fcall param_tys ret_ty s s_args vs used' seed Hsummary Hcaps Hbridge
    Hsafe_args Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hseed_names Hrename.
  set (body_env := global_env_with_local_bounds env
    (subst_type_params_trait_bounds type_args (fn_bounds fdef))).
  set (fdefT := fn_subst_type_params type_args fdef).
  set (fcallT := fn_subst_type_params type_args fcall).
  destruct (alpha_rename_fn_def_static_fields seed fdef fcall used' Hrename)
    as [_ [_ [_ [_ [_ [_ Hbounds]]]]]].
  assert (HsummaryT :
    callee_body_root_shadow_store_safe_narrow_summary body_env fdefT).
  { subst body_env fdefT.
    unfold callee_body_root_shadow_store_safe_narrow_summary.
    unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated in Hsummary.
    destruct Hsummary as (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup & Hbody & Hcompat & Hexcl_roots & Hexcl_env).
    exists T_body, Gamma_out, R_body, roots_body, ret_roots.
    simpl. repeat split; try assumption.
    - rewrite initial_root_env_for_fn_fn_subst_type_params.
      rewrite fn_body_ctx_fn_subst_type_params.
      exact Hbody. }
  assert (HcapsT : fn_captures fdefT = []).
  { subst fdefT. simpl. rewrite Hcaps. reflexivity. }
  assert (HrenameT :
    alpha_rename_fn_def seed fdefT = (fcallT, used')).
  { subst fdefT fcallT.
    apply alpha_rename_fn_def_subst_type_params. exact Hrename. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Htyped_args_body :
    typed_args_roots body_env Omega n R Sigma args
      (params_of_tys param_tys) Sigma_args R_args arg_roots).
  { subst body_env.
    eapply typed_args_roots_store_safe_global_env_with_local_bounds;
      eassumption. }
  assert (Heval_args_body : eval_args body_env s args s_args vs).
  { subst body_env. apply eval_args_global_env_with_local_bounds. exact Heval_args. }
  assert (Hstore_body : store_typed_prefix body_env s Sigma).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore. }
  destruct (direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed
    body_env Omega n R Sigma Sigma_args R_args arg_roots args fdefT fcallT
    param_tys ret_ty s s_args vs used' seed HsummaryT HcapsT Hbridge
    Hsafe_args_body Htyped_args_body Heval_args_body Hprov_args Hstore_body
    Hroots Hshadow Hrn Hnamed Hkeys Hseed_names HrenameT)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
      Hbody & Hcompat & Hexcl_roots & Hexcl_env & Hsubset).
  subst fcallT body_env. simpl in *.
  exists T_body, Sigma_out, R_body, roots_body, ret_roots.
  rewrite Hbounds.
  repeat split; try assumption.
Qed.


Lemma generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args type_args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fdef type_args ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (apply_type_params type_args (fn_params fdef)))
        (subst_type_params_ty type_args (fn_ret fdef)) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      exists T_body Sigma_out R_body roots_body ret_roots,
        expr_root_shadow_store_safe_narrow_summary
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall)))
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R_args)
          (sctx_of_ctx (params_ctx
            (apply_type_params type_args (fn_params fcall))))
          (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
          R_body roots_body ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body
          (subst_type_params_ty type_args (fn_ret fcall)) = true /\
        roots_exclude_params (apply_type_params type_args (fn_params fcall))
          roots_body /\
        root_env_excludes_params
          (apply_type_params type_args (fn_params fcall)) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros.
  eapply generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed;
    try eassumption.
  intros y Hy. exact Hy.
Qed.

Lemma generic_direct_call_cleanup_value_from_body_package :
  forall env sigma type_args ps_runtime fdef fcall s_body ret T_body R_body
      roots_body frame_final,
    value_has_type env s_body ret T_body ->
    ty_compatible_b (fn_outlives fcall) T_body
      (subst_type_params_ty type_args (fn_ret fcall)) = true ->
    alpha_rename_fn_def [] fdef = (fcall, []) \/
      fn_ret fcall = fn_ret fdef ->
    store_param_scope ps_runtime s_body frame_final ->
    store_roots_within R_body s_body ->
    value_roots_within roots_body ret ->
    store_no_shadow s_body ->
    NoDup (ctx_names (params_ctx ps_runtime)) ->
    roots_exclude_params ps_runtime roots_body ->
    root_env_excludes_params ps_runtime R_body ->
    (fn_ret fcall = fn_ret fdef) ->
    value_has_type env (store_remove_params ps_runtime s_body) ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env sigma type_args ps_runtime fdef fcall s_body ret T_body R_body
    roots_body frame_final Hv_body Hcompat _ Hscope Hroots Hret_roots Hshadow
    Hnodup Hexclude_roots Hexclude_env Hret_eq.
  assert (Hv_ret_fcall :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fcall))).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat. }
  assert (Hv_ret_fdef :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fdef))).
  { rewrite <- Hret_eq. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              ps_runtime s_body frame_final R_body roots_body ret
              Hscope Hroots Hret_roots Hshadow Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  apply value_has_type_apply_lt_ty.
  eapply value_has_type_store_remove_params_excluding.
  - exact Hv_ret_fdef.
  - exact Hret_exclude.
Qed.

Record generic_direct_call_runtime_package
    (env : global_env) (s s' : store) (ret : value)
    (Sigma_args : sctx) (R_args : root_env) (arg_roots : list root_set)
    (ret_ty : Ty) : Prop := {
  generic_direct_call_package_store :
    store_typed_prefix env s' Sigma_args;
  generic_direct_call_package_value :
    value_has_type env s' ret ret_ty;
  generic_direct_call_package_preserved :
    store_ref_targets_preserved env s s';
  generic_direct_call_package_roots :
    store_roots_within R_args s';
  generic_direct_call_package_value_roots :
    value_roots_within (root_sets_union arg_roots) ret;
  generic_direct_call_package_shadow :
    store_no_shadow s';
  generic_direct_call_package_root_shadow :
    root_env_no_shadow R_args;
  generic_direct_call_package_roots_named :
    root_env_store_roots_named R_args s';
  generic_direct_call_package_keys_named :
    root_env_store_keys_named R_args s';
  generic_direct_call_package_closure_summary :
    store_function_closure_targets_summary env s'
}.


Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_expr :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  dependent destruction Heval_call.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  | Hlookup_fn : lookup_fn ?fname_call ?fns = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  end.
  match goal with
  | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
      rename H into Heval_args;
      rename s_args0 into s_args;
      rename vs0 into vs
  end.
  match goal with
  | H : alpha_rename_fn_def (store_names s_args) fdef =
        (?fcall0, ?used0) |- _ =>
      rename H into Hrename;
      rename fcall0 into fcall;
      rename used0 into used'
  end.
  match goal with
  | H : eval _
        (bind_params (apply_type_params type_args (fn_params fcall)) vs s_args)
        (subst_type_params_expr type_args (fn_body fcall)) ?s_body0 ret |- _ =>
      rename H into Heval_body;
      rename s_body0 into s_body
  end.
  pose proof (typed_args_roots_params_of_tys_map_param_ty
    env Omega n R Sigma args
    (apply_lt_params sigma
      (apply_type_params type_args (fn_params fdef)))
    Sigma_args R_args arg_roots Htyped_args) as Htyped_args_param_tys.
  pose proof (runtime_tfn_signature_bridge_apply_lt_params
    sigma (apply_type_params type_args (fn_params fdef))
    (subst_type_params_ty type_args (fn_ret fdef))) as Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
    env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args Hready_args) as Hprov_args.
  destruct (generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args type_args fdef fcall
    (map param_ty
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef))))
    (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
    s s_args vs used' Hsummary Hcaps_fdef Hbridge Hsafe_args
    Htyped_args_param_tys Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
  pose (ps_runtime := apply_type_params type_args (fn_params fcall)).
  destruct (generic_direct_call_args_bind_type_params_runtime_package
    env Omega n R Sigma args type_args sigma fdef fcall used'
    s s_args vs Sigma_args R_args arg_roots Hsafe_args Heval_args
    Htyped_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hunique
    Hsummary_store Hrename)
    as (Hstore_bind & Hroots_bind & Hshadow_bind & Hrn_bind & Hcover_bind &
        Hnamed_bind & Hkeys_bind & Hsummary_bind & Hframe_start).
  fold ps_runtime in Hstore_bind, Hroots_bind, Hshadow_bind, Hrn_bind,
    Hcover_bind, Hnamed_bind, Hkeys_bind, Hsummary_bind, Hframe_start.
  assert (Hnodup : NoDup (ctx_names (params_ctx ps_runtime))).
  { subst ps_runtime.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  pose (body_env := global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall))).
  fold body_env in Hsummary_body.
  fold ps_runtime in Hsummary_body.
  rename Hsummary_body into Hsummary_body_env.
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params ps_runtime vs s_args)
      (sctx_of_ctx (params_ctx ps_runtime))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params ps_runtime vs s_args)
      (subst_type_params_expr type_args (fn_body fcall)) s_body ret).
  { subst body_env ps_runtime.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hsummary_bind_body_env :
    store_function_closure_targets_summary body_env
      (bind_params ps_runtime vs s_args)).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    exact Hsummary_bind. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret Hstore_bind_body_env
    Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind
    Hsummary_bind_body_env Heval_body_body_env Hunique_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
      [Hrootset_body [Hshadow_body [Hrn_body [Hnamed_body
        [Hkeys_body Hsummary_body_store]]]]]]]]]].
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret ps_runtime s_args
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env
    Hcover_bind Hframe_start)
    as [frame_final Hscope_body].
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fcall))).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hv_ret_fdef :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fdef))).
  { rewrite Hret_alpha. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              ps_runtime s_body frame_final R_body roots_body ret
              Hscope_body Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params ps_runtime s_body) ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  exact Hv_final.
Qed.



Lemma alpha_rename_store_safe_call_args_hidden_seed_excludes :
  forall env rho used args argsr used' x,
    store_safe_function_value_call_args env args ->
    (forall y, In y (rename_range rho) -> y <> x) ->
    ~ In x (args_free_vars_ts args) ->
    ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr rho used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used args) = (argsr, used') ->
    ~ In x (args_free_vars_ts argsr) /\
    ~ In x (args_local_store_names argsr).
Proof.
  intros env rho used args argsr used' x Hsafe Hrange Hfree Hrename.
  revert used argsr used' Hfree Hrename.
  induction Hsafe as [| arg rest Harg Hsafe_rest IH];
    intros used argsr used' Hfree Hrename; simpl in Hrename.
  - injection Hrename as <- _. simpl. split; intros Hin; contradiction.
  - destruct Harg as [| lit | y | fname0 fdef0 Hin0 Hname0 Hsummary0]; simpl in Hrename.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. right. exact Hin.
      * exact Hrest.
      * split.
        -- simpl. intros Hin. destruct Hin as [Heq | Hin].
           ++ destruct (lookup_rename_in_range_or_self rho y)
                as [Hin_range | Hself].
              ** apply (Hrange (lookup_rename y rho) Hin_range).
                 exact Heq.
              ** apply Hfree. simpl. left.
                 rewrite Hself in Heq. exact Heq.
           ++ apply Hfree_rest. exact Hin.
        -- simpl. exact Hlocal_rest.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
Qed.

Lemma generic_direct_call_target_alpha_rename_runtime_args_hidden_seed_excludes :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body argsr x,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    In x used ->
    ~ In x (args_free_vars_ts args) ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    subst_type_params_expr type_args (fn_body fcall) =
      ECallGeneric fname nested_type_args argsr ->
    ~ In x (args_free_vars_ts argsr) /\
    ~ In x (args_local_store_names argsr).
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body argsr x Hbody Htarget Hsynthetic Hsafe Hused
    Hfree Hrename Hbody_runtime.
  subst raw_body synthetic_body.
  destruct fdef as [fname_def lifetimes outs captures ps ret body].
  simpl in *.
  unfold generic_direct_call_target_expr in Htarget.
  destruct (subst_type_params_expr type_args body) eqn:Hsubst;
    try discriminate.
  inversion Htarget; subst i l l0; clear Htarget.
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr rho] used_params] eqn:Hparams.
  destruct (alpha_rename_expr rho used_params body) as [bodyr used_body]
    eqn:Hbody_rename.
  inversion Hrename; subst fcall used_body; clear Hrename.
  pose proof (alpha_rename_expr_subst_type_params_expr type_args rho
    used_params body bodyr used' Hbody_rename) as Hbody_subst_rename.
  rewrite Hsubst in Hbody_subst_rename.
  simpl in Hbody_subst_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used_params args) as [argsr0 used_args] eqn:Hargsr.
  injection Hbody_subst_rename as Hexpr_eq.
  simpl in Hbody_runtime.
  rewrite <- Hexpr_eq in Hbody_runtime.
  injection Hbody_runtime as Hargs_eq.
  assert (Hrange_fresh : forall y,
    In y (rename_range rho) -> y <> x).
  { intros y Hrange Hy.
    subst y.
    eapply alpha_rename_params_range_fresh_used_nil.
    - exact Hparams.
    - exact Hrange.
    - apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. right. exact Hused. }
  destruct (alpha_rename_store_safe_call_args_hidden_seed_excludes
    env rho used_params args argsr0 used_args x Hsafe Hrange_fresh Hfree Hargsr)
    as [Hfree_runtime Hlocal_runtime].
  split.
  - rewrite <- Hargs_eq. exact Hfree_runtime.
  - rewrite <- Hargs_eq. exact Hlocal_runtime.
Qed.


Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    exists argsr,
      subst_type_params_expr type_args (fn_body fcall) =
        ECallGeneric fname nested_type_args argsr /\
      store_safe_function_value_call_args env argsr.
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body Hbody Htarget Hsynthetic Hsafe Hrename.
  subst raw_body synthetic_body.
  unfold generic_direct_call_target_expr in Htarget.
  destruct (subst_type_params_expr type_args (fn_body fdef)) eqn:Hsubst;
    try discriminate.
  inversion Htarget; subst i l l0; clear Htarget.
  destruct (alpha_rename_fn_def_params_body used fdef fcall used' Hrename)
    as (rho & used_params & Hparams & Hbody_rename).
  pose proof (alpha_rename_expr_subst_type_params_expr type_args rho
    used_params (fn_body fdef) (fn_body fcall) used' Hbody_rename)
    as Hbody_subst_rename.
  rewrite Hsubst in Hbody_subst_rename.
  simpl in Hbody_subst_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used_params args) as [argsr used_args] eqn:Hargsr.
  inversion Hbody_subst_rename; subst.
  exists argsr.
  split; [reflexivity |].
  eapply store_safe_function_value_call_args_alpha_rename_call_go;
    eassumption.
Qed.





Lemma generic_direct_call_target_alpha_rename_runtime_body_free_vars_hidden_seed_excludes :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body x,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    In x used ->
    ~ In x (args_free_vars_ts args) ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body x Hbody Htarget Hsynthetic Hsafe Hused Hfree
    Hrename.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime
    env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body Hbody Htarget Hsynthetic Hsafe Hrename)
    as [argsr [Hbody_runtime Hsafe_runtime]].
  rewrite Hbody_runtime. simpl.
  destruct (generic_direct_call_target_alpha_rename_runtime_args_hidden_seed_excludes
    env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body argsr x Hbody Htarget Hsynthetic Hsafe Hused
    Hfree Hrename Hbody_runtime) as [Hfree_runtime _].
  exact Hfree_runtime.
Qed.


Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body T_body Gamma_out R_body roots_body,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    NoDup (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fdef)))) ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
    roots_exclude_params (apply_type_params type_args (fn_params fdef))
      roots_body ->
    exists argsr fcallee (sigma : list lifetime),
      exists arg_roots Sigma_out_r R_body_r roots_body_r,
      subst_type_params_expr type_args (fn_body fcall) =
        ECallGeneric fname nested_type_args argsr /\
      store_safe_function_value_call_args env argsr /\
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        (ECallGeneric fname nested_type_args argsr)
        T_body Sigma_out_r R_body_r roots_body_r /\
      typed_args_roots
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        argsr
        (apply_lt_params sigma
          (apply_type_params nested_type_args (fn_params fcallee)))
        Sigma_out_r R_body_r arg_roots /\
      In fcallee (env_fns
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))) /\
      fn_name fcallee = fname /\
      roots_exclude_params (apply_type_params type_args (fn_params fcall))
        roots_body_r.
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body T_body Gamma_out R_body roots_body Hbody Htarget
    Hsynthetic Hsafe Hcaps Hrename Hnodup_applied Htyped Hexcl_roots.
  subst raw_body synthetic_body.
  rewrite params_ctx_apply_type_params in Hnodup_applied.
  rewrite ctx_names_subst_type_params_ctx in Hnodup_applied.
  destruct (alpha_rename_fn_def_initial_support_facts
              used fdef fcall used' Hrename Hnodup_applied)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields used fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [_ [_ Hbounds]]]]]].
  unfold generic_direct_call_target_expr in Htarget.
  destruct (subst_type_params_expr type_args (fn_body fdef)) eqn:Hsubst;
    try discriminate.
  inversion Htarget; subst i l l0; clear Htarget.
  pose proof (alpha_rename_expr_subst_type_params_expr type_args rho
    used_params (fn_body fdef) (fn_body fcall) used' Hbody_rename)
    as Hbody_subst_rename.
  rewrite Hsubst in Hbody_subst_rename.
  simpl in Hbody_subst_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used_params args) as [argsr used_args] eqn:Hargsr.
  inversion Hbody_subst_rename; subst used_args; clear Hbody_subst_rename.
  assert (Htyped_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (ECallGeneric fname nested_type_args args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
    exact Htyped. }
  assert (Hctx_alpha_subst :
    ctx_alpha rho
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall))))).
  { apply ctx_alpha_subst_type_params_ctx. exact Halpha_params. }
  assert (Hkeys_initial_subst :
    root_env_sctx_keys_named (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))).
  { unfold root_env_sctx_keys_named, root_env_keys_named in *.
    intros x Hin. unfold sctx_of_ctx.
    rewrite ctx_names_subst_type_params_ctx.
    apply Hkeys_initial. exact Hin. }
  assert (Hroots_initial_subst :
    root_env_sctx_roots_named (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))).
  { unfold root_env_sctx_roots_named in *.
    intros x roots z Hlookup Hin.
    change (In z (ctx_names (subst_type_params_ctx type_args
      (params_ctx (fn_params fdef))))).
    rewrite ctx_names_subst_type_params_ctx.
    eapply Hroots_initial; eassumption. }
  assert (Hkeys_body :
    root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_params.
    - exact Hrn_initial. }
  assert (Hnodup_apply :
    NoDup (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fdef))))).
  { rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx. exact Hnodup_applied. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_params. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support
      with (ps := apply_type_params type_args (fn_params fdef))
           (psr := apply_type_params type_args (fn_params fcall))
           (Σ := sctx_of_ctx Gamma_out).
    - rewrite params_ctx_apply_type_params.
      rewrite params_ctx_apply_type_params. exact Hctx_alpha_subst.
    - rewrite params_ctx_apply_type_params. exact Hsame_body.
    - exact Hnodup_apply.
    - exact Hkeys_body. }
  assert (Hrename_call_expr :
    alpha_rename_expr rho used_params
      (ECallGeneric fname nested_type_args args) =
    (ECallGeneric fname nested_type_args argsr, used')).
  { simpl. rewrite Hargsr. reflexivity. }
  assert (Hctx_used_subst :
    forall x,
      In x (ctx_names (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall))))) ->
      In x used_params).
  { intros x Hin. unfold sctx_of_ctx in Hin.
    rewrite ctx_names_subst_type_params_ctx in Hin.
    apply Hctx_used. exact Hin. }
  assert (Hdisj_subst :
    disjoint_names
      (free_vars_expr (ECallGeneric fname nested_type_args args))
      (rename_range rho)).
  { rewrite <- Hsubst.
    rewrite expr_names_subst_type_params_expr.
    exact Hdisj. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env
                (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (subst_type_params_ctx type_args
                (params_ctx (fn_params fdef))))
              (sctx_of_ctx (subst_type_params_ctx type_args
                (params_ctx (fn_params fcall))))
              (ECallGeneric fname nested_type_args args)
              (ECallGeneric fname nested_type_args argsr)
              used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_params Hctx_alpha_subst Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial_subst Hroots_initial_subst
              Hnocoll_initial Hnocoll_body Hctx_used_subst Hrange_used Hdisj_subst
              Hrename_call_expr)
    as (Sigma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & _ & _ & Hroots_equiv).
  assert (Hsame_body_apply :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx
        (apply_type_params type_args (fn_params fdef))))
      (sctx_of_ctx Gamma_out)).
  { rewrite params_ctx_apply_type_params. exact Hsame_body. }
  assert (Hexcl_roots_r :
    roots_exclude_params (apply_type_params type_args (fn_params fcall))
      roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support
      with (rho := rho)
           (ps := apply_type_params type_args (fn_params fdef))
           (Σ := sctx_of_ctx Gamma_out)
           (roots := roots_body).
    - rewrite params_ctx_apply_type_params.
      rewrite params_ctx_apply_type_params.
      exact Hctx_alpha_subst.
    - exact Halpha_out.
    - exact Hsame_body_apply.
    - exact Hnodup_apply.
    - exact Hroots_equiv.
    - exact Hroots_set_body.
    - exact Hexcl_roots. }
  assert (Hbody_runtime :
    subst_type_params_expr type_args (fn_body fcall) =
      ECallGeneric fname nested_type_args argsr).
  { exact (eq_sym H0). }
  assert (Hsafe_runtime :
    store_safe_function_value_call_args env argsr).
  { eapply store_safe_function_value_call_args_alpha_rename_call_go;
      eassumption. }
  assert (Htyped_renamed_body_ctx :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
      (ECallGeneric fname nested_type_args argsr)
      T_body Sigma_out_r R_body_r roots_body_r).
  { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
    - exact Htyped_renamed.
    - rewrite <- Hcaps.
      eapply alpha_rename_fn_def_captures. exact Hrename. }
  destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
    (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
    (fn_outlives fdef) (fn_lifetimes fdef)
    (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
    (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
    fname nested_type_args argsr T_body Sigma_out_r R_body_r roots_body_r
    Htyped_renamed_body_ctx)
    as (fcallee & sigma & arg_roots & Hin & Hname & _ & _ & _ &
        Htyped_args & _ & _ & _).
  exists argsr, fcallee, sigma, arg_roots, Sigma_out_r, R_body_r,
    roots_body_r.
  repeat split; try assumption.
Qed.
Lemma typed_generic_direct_call_args_roots_call_frame_from_origin :
  forall env Omega n ps_orig ps_call outer_arg_roots R_args Sigma
      fname type_args argsr T Sigma_out R_body roots_body,
    params_alpha ps_orig ps_call ->
    NoDup (ctx_names (params_ctx ps_orig)) ->
    List.length outer_arg_roots = List.length ps_orig ->
    root_subst_images_exclude_names
      (expr_local_store_names (ECallGeneric fname type_args argsr))
      (root_subst_of_params ps_orig outer_arg_roots) ->
    root_env_no_shadow
      (initial_root_env_for_params_origin ps_orig ps_call) ->
    root_env_no_shadow
      (call_param_root_env ps_call outer_arg_roots []) ->
    root_env_tail_fresh_names
      (root_env_remove_params ps_call R_args)
      (expr_local_store_names (ECallGeneric fname type_args argsr)) ->
    typed_env_roots_shadow_safe env Omega n
      (initial_root_env_for_params_origin ps_orig ps_call) Sigma
      (ECallGeneric fname type_args argsr) T Sigma_out R_body roots_body ->
    Sigma = sctx_of_ctx (params_ctx ps_call) ->
    roots_exclude_params ps_call roots_body ->
    (forall x,
      In x (ctx_names (params_ctx ps_call)) ->
      root_subst_images_exclude x
        (root_subst_of_params ps_orig outer_arg_roots)) ->
    exists fcallee sigma arg_roots Sigma_args R_args_out,
      typed_args_roots env Omega n
        (call_param_root_env ps_call outer_arg_roots R_args) Sigma argsr
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fcallee)))
        Sigma_args R_args_out arg_roots /\
      In fcallee (env_fns env) /\
      fn_name fcallee = fname /\
      fn_captures fcallee = [] /\
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fcallee)) /\
      T = apply_lt_ty sigma
        (subst_type_params_ty type_args (fn_ret fcallee)) /\
      roots_exclude_params ps_call (root_sets_union arg_roots) /\
      root_set_stores_subset (root_sets_union arg_roots)
        (root_sets_union outer_arg_roots).
Proof.
  intros env Omega n ps_orig ps_call outer_arg_roots R_args Sigma fname
    type_args argsr T Sigma_out R_body roots_body Halpha Hnodup Hlen
    Hsubst_fresh Hrn_origin Hrn_call_empty Htail_fresh Htyped_origin
    Hsigma_eq Hexcl_roots Himages_exclude.
  subst Sigma.
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params ps_orig outer_arg_roots)
        (initial_root_env_for_params_origin ps_orig ps_call))
      (call_param_root_env ps_call outer_arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env Omega n
              (root_subst_of_params ps_orig outer_arg_roots)
              (initial_root_env_for_params_origin ps_orig ps_call)
              (sctx_of_ctx (params_ctx ps_call))
              (ECallGeneric fname type_args argsr) T Sigma_out R_body
              roots_body (call_param_root_env ps_call outer_arg_roots [])
              Htyped_origin Hsubst_fresh Hrn_origin Hrn_call_empty)
    as (R_body_inst & roots_body_inst & Htyped_inst & Hrn_body_inst &
        Hbody_inst_equiv & Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  pose proof (typed_env_roots_shadow_safe_tail_frame
    env Omega n (root_env_remove_params ps_call R_args)
    (call_param_root_env ps_call outer_arg_roots [])
    (sctx_of_ctx (params_ctx ps_call))
    (ECallGeneric fname type_args argsr) T Sigma_out R_body_inst
    roots_body_inst Htyped_inst Htail_fresh) as Htyped_tail.
  rewrite <- call_param_root_env_app_tail in Htyped_tail.
  destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
    env Omega n (call_param_root_env ps_call outer_arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_call)) fname type_args argsr T Sigma_out
    (R_body_inst ++ root_env_remove_params ps_call R_args)
    roots_body_inst Htyped_tail)
    as (fcallee & sigma & arg_roots & Hin & Hname & Hcaps & _ & _ &
        Htyped_args & Houtlives & Hret & Hroots_eq).
  exists fcallee, sigma, arg_roots, Sigma_out,
    (R_body_inst ++ root_env_remove_params ps_call R_args).
  assert (Hexcl_roots_inst :
    roots_exclude_params ps_call roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate; eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union outer_arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  repeat split; try assumption.
  - rewrite <- Hroots_eq. exact Hexcl_roots_inst.
  - rewrite <- Hroots_eq. exact Hsubset_inst.
Qed.

Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args_call_frame :
  forall env Omega n R Sigma Sigma_args R_args outer_arg_roots outer_args
      type_args sigma_outer fdef fcall used' fname nested_type_args args
      raw_body synthetic_body T_body Gamma_out R_body roots_body s s_args vs,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    NoDup (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fdef)))) ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
    roots_exclude_params (apply_type_params type_args (fn_params fdef))
      roots_body ->
    typed_args_roots env Omega n R Sigma outer_args
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots ->
    store_safe_function_value_call_args env outer_args ->
    eval_args env s outer_args s_args vs ->
    provenance_ready_args outer_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    exists argsr fcallee sigma_nested nested_arg_roots Sigma_nested R_nested,
      subst_type_params_expr type_args (fn_body fcall) =
        ECallGeneric fname nested_type_args argsr /\
      store_safe_function_value_call_args env argsr /\
      typed_args_roots
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (call_param_root_env (apply_type_params type_args (fn_params fcall))
          outer_arg_roots R_args)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        argsr
        (apply_lt_params sigma_nested
          (apply_type_params nested_type_args (fn_params fcallee)))
        Sigma_nested R_nested nested_arg_roots /\
      In fcallee (env_fns
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))) /\
      fn_name fcallee = fname /\
      fn_captures fcallee = [] /\
      Forall (fun '(a, b) => outlives (fn_outlives fdef) a b)
        (apply_lt_outlives sigma_nested (fn_outlives fcallee)) /\
      T_body = apply_lt_ty sigma_nested
        (subst_type_params_ty nested_type_args (fn_ret fcallee)) /\
      roots_exclude_params (apply_type_params type_args (fn_params fcall))
        (root_sets_union nested_arg_roots) /\
      root_set_stores_subset (root_sets_union nested_arg_roots)
        (root_sets_union outer_arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args outer_arg_roots outer_args
    type_args sigma_outer fdef fcall used' fname nested_type_args args
    raw_body synthetic_body T_body Gamma_out R_body roots_body s s_args vs
    Hbody Htarget Hsynthetic Hsafe Hcaps Hrename Hnodup_applied Htyped_body
    Hexcl_roots Htyped_outer_args Hsafe_outer_args Heval_outer_args Hprov_outer_args Hstore Hroots Hshadow
    Hrn Hnamed Hkeys.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args
    env type_args (store_names s_args) fdef fcall used' fname
    nested_type_args args raw_body synthetic_body T_body Gamma_out R_body
    roots_body Hbody Htarget Hsynthetic Hsafe Hcaps Hrename Hnodup_applied
    Htyped_body Hexcl_roots)
    as (argsr & fcallee & sigma_nested & nested_arg_roots & Sigma_origin &
        R_origin & roots_origin & Hbody_runtime & Hsafe_runtime &
        Htyped_origin & Htyped_args_origin & Hin_nested & Hname_nested &
        Hexcl_roots_origin).
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hparams_alpha_applied :
    params_alpha (apply_type_params type_args (fn_params fdef))
      (apply_type_params type_args (fn_params fcall))).
  { apply params_alpha_apply_type_compat. exact Hparams_alpha. }
  assert (Hlen_outer_roots :
    List.length outer_arg_roots =
    List.length (apply_type_params type_args (fn_params fdef))).
  { pose proof (typed_args_roots_arg_roots_length
      env Omega n R Sigma outer_args
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots Htyped_outer_args) as Hlen.
    rewrite apply_lt_params_length in Hlen. exact Hlen. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args)
      outer_arg_roots).
  { destruct (store_safe_function_value_call_args_typed_roots_store_named
      env Omega n R Sigma outer_args
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots s s_args vs
      Hsafe_outer_args Htyped_outer_args Heval_outer_args Hnamed Hkeys)
      as [_ [Hroots_named _]].
    exact Hroots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names
      (expr_local_store_names (ECallGeneric fname nested_type_args argsr))
      (root_subst_of_params (apply_type_params type_args (fn_params fdef))
        outer_arg_roots)).
  { rewrite root_subst_of_params_apply_type_params.
    rewrite <- Hbody_runtime.
    rewrite expr_local_store_names_subst_type_params_expr.
    eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  assert (Hrn_origin_applied :
    root_env_no_shadow
      (initial_root_env_for_params_origin
        (apply_type_params type_args (fn_params fdef))
        (apply_type_params type_args (fn_params fcall)))).
  { rewrite initial_root_env_for_params_origin_apply_type_params.
    apply initial_root_env_for_params_origin_no_shadow.
    - apply params_alpha_length. exact Hparams_alpha.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hrn_call_empty :
    root_env_no_shadow
      (call_param_root_env (apply_type_params type_args (fn_params fcall))
        outer_arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - rewrite params_ctx_apply_type_params.
      rewrite ctx_names_subst_type_params_ctx.
      eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (apply_type_params type_args (fn_params fcall)))) ->
      root_subst_images_exclude x
        (root_subst_of_params (apply_type_params type_args (fn_params fdef))
          outer_arg_roots)).
  { intros x Hin_x.
    rewrite params_ctx_apply_type_params in Hin_x.
    rewrite ctx_names_subst_type_params_ctx in Hin_x.
    rewrite root_subst_of_params_apply_type_params.
    apply root_subst_of_params_images_exclude.
    assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
    { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
    assert (Harg_roots_exclude :
      Forall (roots_exclude_params (fn_params fcall)) outer_arg_roots).
    { eapply root_sets_store_roots_named_excludes_params; eassumption. }
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (apply_type_params type_args (fn_params fcall))
        R_args)
      (expr_local_store_names (ECallGeneric fname nested_type_args argsr))).
  { rewrite root_env_remove_params_apply_type_params.
    rewrite <- Hbody_runtime.
    rewrite expr_local_store_names_subst_type_params_expr.
    eapply (eval_args_root_tail_fresh_names_for_fresh_call_prefix_named
      env Omega n R Sigma
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots outer_args s s_args vs
      fdef fcall used'); eassumption. }
  assert (Htyped_origin_applied :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin
        (apply_type_params type_args (fn_params fdef))
        (apply_type_params type_args (fn_params fcall)))
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
      (ECallGeneric fname nested_type_args argsr)
      T_body Sigma_origin R_origin roots_origin).
  { rewrite initial_root_env_for_params_origin_apply_type_params.
    exact Htyped_origin. }
  assert (Hsigma_origin_eq :
    sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)) =
    sctx_of_ctx (params_ctx (apply_type_params type_args (fn_params fcall)))).
  { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
    - rewrite params_ctx_apply_type_params. reflexivity.
    - rewrite <- Hcaps.
      eapply alpha_rename_fn_def_captures. exact Hrename. }
  destruct (typed_generic_direct_call_args_roots_call_frame_from_origin
    (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
    (fn_outlives fdef) (fn_lifetimes fdef)
    (apply_type_params type_args (fn_params fdef))
    (apply_type_params type_args (fn_params fcall))
    outer_arg_roots R_args
    (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
    fname nested_type_args argsr T_body Sigma_origin R_origin roots_origin
    Hparams_alpha_applied Hnodup_applied Hlen_outer_roots Hsubst_fresh
    Hrn_origin_applied Hrn_call_empty Htail_fresh Htyped_origin_applied
    Hsigma_origin_eq Hexcl_roots_origin Himages_exclude)
    as (fcallee_frame & sigma_frame & nested_arg_roots_frame &
        Sigma_frame & R_frame & Htyped_frame & Hin_frame & Hname_frame &
        Hcaps_frame & Houtlives_frame & Hret_frame & Hexcl_nested_roots &
        Hnested_roots_subset).
  exists argsr, fcallee_frame, sigma_frame, nested_arg_roots_frame,
    Sigma_frame, R_frame.
  repeat split; try assumption.
Qed.

Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime_eval :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body s s' ret,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    eval env s (subst_type_params_expr type_args (fn_body fcall)) s' ret ->
    exists argsr,
      store_safe_function_value_call_args env argsr /\
      eval env s (ECallGeneric fname nested_type_args argsr) s' ret.
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body s s' ret Hbody Htarget Hsynthetic Hsafe Hrename
    Heval.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime
    env type_args used fdef fcall used' fname nested_type_args args raw_body
    synthetic_body Hbody Htarget Hsynthetic Hsafe Hrename)
    as [argsr [Hbody_runtime Hsafe_runtime]].
  exists argsr.
  split; [exact Hsafe_runtime |].
  rewrite <- Hbody_runtime.
  exact Heval.
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  dependent destruction Heval_call.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  | Hlookup_fn : lookup_fn ?fname_call ?fns = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  end.
  match goal with
  | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
      rename H into Heval_args;
      rename s_args0 into s_args;
      rename vs0 into vs
  end.
  match goal with
  | H : alpha_rename_fn_def (store_names s_args) fdef =
        (?fcall0, ?used0) |- _ =>
      rename H into Hrename;
      rename fcall0 into fcall;
      rename used0 into used'
  end.
  match goal with
  | H : eval _
        (bind_params (apply_type_params type_args (fn_params fcall)) vs s_args)
        (subst_type_params_expr type_args (fn_body fcall)) ?s_body0 ret |- _ =>
      rename H into Heval_body;
      rename s_body0 into s_body
  end.
  pose proof (typed_args_roots_params_of_tys_map_param_ty
    env Omega n R Sigma args
    (apply_lt_params sigma
      (apply_type_params type_args (fn_params fdef)))
    Sigma_args R_args arg_roots Htyped_args) as Htyped_args_param_tys.
  pose proof (runtime_tfn_signature_bridge_apply_lt_params
    sigma (apply_type_params type_args (fn_params fdef))
    (subst_type_params_ty type_args (fn_ret fdef))) as Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
    env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args Hready_args) as Hprov_args.
  destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
    env Omega n R Sigma args
    (apply_lt_params sigma
      (apply_type_params type_args (fn_params fdef)))
    Sigma_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
    Heval_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store)
    as (Hstore_args & Hargs_values_sigma & Hpres_args & Hroots_args &
        Harg_roots_values & Hshadow_args & Hrn_args & Hnamed_args &
        Hkeys_args & Hsummary_args).
  destruct (generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args type_args fdef fcall
    (map param_ty
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef))))
    (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
    s s_args vs used' Hsummary Hcaps_fdef Hbridge Hsafe_args
    Htyped_args_param_tys Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
  pose (ps_runtime := apply_type_params type_args (fn_params fcall)).
  destruct (generic_direct_call_args_bind_type_params_runtime_package
    env Omega n R Sigma args type_args sigma fdef fcall used'
    s s_args vs Sigma_args R_args arg_roots Hsafe_args Heval_args
    Htyped_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hunique
    Hsummary_store Hrename)
    as (Hstore_bind & Hroots_bind & Hshadow_bind & Hrn_bind & Hcover_bind &
        Hnamed_bind & Hkeys_bind & Hsummary_bind & Hframe_start).
  fold ps_runtime in Hstore_bind, Hroots_bind, Hshadow_bind, Hrn_bind,
    Hcover_bind, Hnamed_bind, Hkeys_bind, Hsummary_bind, Hframe_start.
  assert (Hnodup : NoDup (ctx_names (params_ctx ps_runtime))).
  { subst ps_runtime.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  pose (body_env := global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall))).
  fold body_env in Hsummary_body.
  fold ps_runtime in Hsummary_body.
  rename Hsummary_body into Hsummary_body_env.
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params ps_runtime vs s_args)
      (sctx_of_ctx (params_ctx ps_runtime))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params ps_runtime vs s_args)
      (subst_type_params_expr type_args (fn_body fcall)) s_body ret).
  { subst body_env ps_runtime.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hsummary_bind_body_env :
    store_function_closure_targets_summary body_env
      (bind_params ps_runtime vs s_args)).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    exact Hsummary_bind. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret Hstore_bind_body_env
    Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind
    Hsummary_bind_body_env Heval_body_body_env Hunique_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
      [Hrootset_body [Hshadow_body [Hrn_body [Hnamed_body
        [Hkeys_body Hsummary_body_store]]]]]]]]]].
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret ps_runtime s_args
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env
    Hcover_bind Hframe_start)
    as [frame_final Hscope_body].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hargs_values_fdef_type :
    eval_args_values_have_types env Omega s_args vs
      (apply_type_params type_args (fn_params fdef))).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_values_sigma. }
  assert (Hargs_values_fcall_type :
    eval_args_values_have_types env Omega s_args vs ps_runtime).
  { subst ps_runtime.
    eapply eval_args_values_have_types_params_alpha.
    - apply params_alpha_apply_type_compat. exact Hparams_alpha.
    - exact Hargs_values_fdef_type. }
  assert (Hfresh : params_fresh_in_store ps_runtime s_args).
  { subst ps_runtime.
    unfold params_fresh_in_store.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hframe_scope_start :
    store_frame_scope ps_runtime (sctx_of_ctx (params_ctx ps_runtime))
      (bind_params ps_runtime vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_values_fcall_type. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh (sctx_of_ctx (params_ctx ps_runtime)) s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret ps_runtime s_args
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env
    Hcover_bind Hframe_scope_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope_body Hframe_fresh_body]]]]].
  assert (Hsame_body :
    sctx_same_bindings (sctx_of_ctx (params_ctx ps_runtime)) Sigma_out).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots.
    eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_body_env. }
  assert (Hscope_body_args : store_param_scope ps_runtime s_body s_args).
  { eapply store_frame_scope_param_scope. exact Hframe_scope_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fcall))).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fdef))).
  { rewrite Hret_alpha. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              ps_runtime s_body s_args R_body roots_body ret
              Hscope_body_args Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params ps_runtime s_body) ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  assert (Hremoved_exact : store_remove_params ps_runtime s_body = s_args).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - exact Hscope_body_args.
    - exact Hframe_scope_body. }
  fold ps_runtime.
  rewrite Hremoved_exact.
  split.
  - constructor.
    + exact Hstore_args.
    + rewrite <- Hremoved_exact. exact Hv_final.
    + exact Hpres_args.
    + exact Hroots_args.
    + eapply direct_call_value_roots_within_store_subset; eassumption.
    + exact Hshadow_args.
    + exact Hrn_args.
    + exact Hnamed_args.
    + exact Hkeys_args.
    + exact Hsummary_args.
  - exists s_args, vs.
    split; [exact Heval_args | reflexivity].
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_package_prefix_named_expr :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros.
  destruct (eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr
    env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef) as [Hpkg _]; eauto.
Qed.


Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros.
  eapply eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_expr;
    eassumption.
Qed.

Lemma store_hidden_frame_rel_remove_base :
  forall x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    store_remove x s_with = s_without.
Proof.
  intros x T hidden s_with s_without Hrel.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH]; simpl.
  - rewrite ident_eqb_refl. reflexivity.
  - destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst. contradiction.
    + rewrite IH. reflexivity.
Qed.

Lemma store_hidden_frame_rel_store_names_base_subset :
  forall x T hidden s_with s_without y,
    store_hidden_frame_rel x T hidden s_with s_without ->
    In y (store_names s_without) ->
    In y (store_names s_with).
Proof.
  intros x T hidden s_with s_without y Hrel.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH]; simpl; intros Hy.
  - right. exact Hy.
  - destruct Hy as [Hy | Hy].
    + left. exact Hy.
    + right. apply IH. exact Hy.
Qed.

Lemma store_hidden_frame_rel_name_in :
  forall x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    In x (store_names s_with).
Proof.
  intros x T hidden s_with s_without Hrel.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH].
  - unfold store_add. simpl. left. reflexivity.
  - simpl. right. exact IH.
Qed.

Lemma store_hidden_frame_rel_params_fresh_in_store_base :
  forall x T hidden s_with s_without ps,
    store_hidden_frame_rel x T hidden s_with s_without ->
    params_fresh_in_store ps s_with ->
    params_fresh_in_store ps s_without.
Proof.
  intros x T hidden s_with s_without ps Hrel Hfresh.
  unfold params_fresh_in_store in *.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH];
    intros y Hy Hin.
  - apply (Hfresh y Hy). unfold store_add. simpl. right. exact Hin.
  - simpl in Hin. destruct Hin as [Hy_head | Hin_tail].
    + apply (Hfresh y Hy). simpl. left. exact Hy_head.
    + apply (IH (fun z Hz Hzin => Hfresh z Hz (or_intror Hzin)) y Hy Hin_tail).
Qed.

Lemma eval_args_values_have_types_store_remove_excluding_root :
  forall env Omega s root vs ps,
    eval_args_values_have_types env Omega s vs ps ->
    Forall (value_refs_exclude_root root) vs ->
    eval_args_values_have_types env Omega (store_remove root s) vs ps.
Proof.
  intros env Omega s root vs ps Hargs Hrefs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - constructor.
  - inversion Hrefs; subst.
    eapply AHT_Cons with (T_actual := T_actual).
    + eapply value_has_type_store_remove_excluding_root; eassumption.
    + exact Hcompat.
    + apply IH. assumption.
Qed.

Lemma alpha_rename_fn_def_used_name_fresh_params_and_body_locals :
  forall used fdef fcall used' type_args x,
    alpha_rename_fn_def used fdef = (fcall, used') ->
    In x used ->
    ~ In x (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fcall)))) /\
    ~ In x (expr_local_store_names
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros used fdef fcall used' type_args x Hrename Hused.
  split.
  - rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    intro Hin.
    eapply alpha_rename_fn_def_params_fresh_used; eassumption.
  - rewrite expr_local_store_names_subst_type_params_expr.
    intro Hlocal.
    pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
      used fdef fcall used' Hrename) as Hfresh.
    rewrite Forall_forall in Hfresh.
    specialize (Hfresh x Hlocal).
    exact (Hfresh Hused).
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_ready_free_vars_ctx_names :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Sigma e T Sigma' R' roots ret_roots ->
    preservation_ready_expr e ->
    forall x, In x (free_vars_expr e) -> In x (ctx_names Sigma).
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary Hready.
  inversion Hsummary; subst; intros y Hy; simpl in Hy;
    try contradiction.
  - dependent destruction Hready.
  - dependent destruction Hready.
  - dependent destruction Hready.
  - dependent destruction Hready.
  - first
      [ destruct Hy as [Heq | Htail]; [ rewrite <- Heq | contradiction ]
      | rewrite <- Hy
      | rewrite Hy ];
    dependent destruction H;
    solve [eauto using typed_place_root_name_in_ctx_names].
  - first
      [ destruct Hy as [Heq | Htail]; [ rewrite <- Heq | contradiction ]
      | rewrite <- Hy
      | rewrite Hy ];
    dependent destruction H;
    solve [eauto using typed_place_root_name_in_ctx_names].
  - first
      [ destruct Hy as [Heq | Htail]; [ rewrite <- Heq | contradiction ]
      | rewrite <- Hy
      | rewrite Hy ];
    dependent destruction H;
      match goal with
      | Hplace : typed_place_env_structural _ _ ?p _ |- In (place_name ?p) _ =>
          exact (typed_place_root_name_in_ctx_names _ _ _ _ Hplace)
      end.
  - dependent destruction Hready.
    dependent destruction Hready.
  - inversion Hy as [Heq | Hnil]; [subst y | contradiction].
    dependent destruction H;
      match goal with
      | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
          inversion Hplace; subst; eapply sctx_lookup_in_ctx_names; eassumption
      end.
  - dependent destruction Hready.
    inversion Hy as [Heq | Hnil]; [subst y | contradiction].
    dependent destruction H.
    dependent destruction H.
    all: solve [eauto using typed_place_root_name_in_ctx_names].
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_alpha_renamed_ready_body_free_vars_hidden_seed_excludes :
  forall env fuel fdef type_args fcall used' x T hidden s_hidden s_base,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def (store_names s_hidden) fdef = (fcall, used') ->
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcall)) ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros env fuel fdef type_args fcall used' x T hidden s_hidden s_base
    Hsummary Hcaps Hrename Hrel Hready Hin_free.
  pose proof (store_hidden_frame_rel_name_in x T hidden s_hidden s_base Hrel)
    as Hused.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    (store_names s_hidden) fdef fcall used' type_args x Hrename Hused)
    as [Hnot_params _].
  destruct (callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases
    env fuel fdef type_args Hsummary) as [Hexpr | Hgeneric].
  - destruct Hexpr as (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup & Hnarrow & Hcompat & Hexcl_roots & Hexcl_env).
    rewrite params_ctx_apply_type_params in Hnodup.
    rewrite ctx_names_subst_type_params_ctx in Hnodup.
    destruct (alpha_rename_fn_def_initial_support_facts
      (store_names s_hidden) fdef fcall used' Hrename Hnodup)
      as (rho & used_params & Hparams_rename & Hbody_rename &
          Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
          Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
          Hrange_used & Hdisj).
    assert (Hsummary_params :
      expr_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots).
    { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
      exact Hnarrow. }
    assert (Htyped_body :
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body).
    { eapply expr_root_shadow_store_safe_narrow_summary_typed.
      exact Hsummary_params. }
    assert (Hkeys_initial_subst :
      root_env_sctx_keys_named (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))).
    { unfold root_env_sctx_keys_named, root_env_keys_named in *.
      intros y Hin. unfold sctx_of_ctx.
      rewrite ctx_names_subst_type_params_ctx.
      apply Hkeys_initial. exact Hin. }
    assert (Hroots_initial_subst :
      root_env_sctx_roots_named (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))).
    { unfold root_env_sctx_roots_named in *.
      intros y roots0 z Hlookup Hin.
      change (In z (ctx_names (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))).
      rewrite ctx_names_subst_type_params_ctx.
      eapply Hroots_initial; eassumption. }
    assert (Hctx_alpha_subst :
      ctx_alpha rho
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fcall))))).
    { apply ctx_alpha_subst_type_params_ctx. exact Halpha_params. }
    assert (Hctx_used_subst :
      forall y,
        In y (ctx_names (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fcall))))) ->
        In y used_params).
    { intros y Hy. unfold sctx_of_ctx in Hy.
      rewrite ctx_names_subst_type_params_ctx in Hy.
      apply Hctx_used. exact Hy. }
    assert (Hdisj_subst :
      disjoint_names (free_vars_expr
        (subst_type_params_expr type_args (fn_body fdef)))
        (rename_range rho)).
    { rewrite expr_names_subst_type_params_expr. exact Hdisj. }
    assert (Hbody_rename_subst :
      alpha_rename_expr rho used_params
        (subst_type_params_expr type_args (fn_body fdef)) =
      (subst_type_params_expr type_args (fn_body fcall), used')).
    { apply alpha_rename_expr_subst_type_params_expr. exact Hbody_rename. }
    assert (Hkeys_body :
      root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                  (global_env_with_local_bounds env
                    (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
                  (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
      eapply Hkeys_expr; eassumption. }
    assert (Hrn_body : root_env_no_shadow R_body).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
      - exact Hrn_initial. }
    assert (Hsame_body :
      sctx_same_bindings
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (sctx_of_ctx Gamma_out)).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
    assert (Hnodup_apply :
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef))))).
    { rewrite params_ctx_apply_type_params.
      rewrite ctx_names_subst_type_params_ctx. exact Hnodup. }
    assert (Hctx_alpha_apply :
      ctx_alpha rho
        (sctx_of_ctx (params_ctx
          (apply_type_params type_args (fn_params fdef))))
        (sctx_of_ctx (params_ctx
          (apply_type_params type_args (fn_params fcall))))).
    { rewrite params_ctx_apply_type_params.
      rewrite params_ctx_apply_type_params. exact Hctx_alpha_subst. }
    assert (Hsame_body_apply :
      sctx_same_bindings
        (sctx_of_ctx (params_ctx
          (apply_type_params type_args (fn_params fdef))))
        (sctx_of_ctx Gamma_out)).
    { rewrite params_ctx_apply_type_params. exact Hsame_body. }
    assert (Hnocoll_body :
      rename_no_collision_on rho (root_env_names R_body)).
    { eapply rename_no_collision_on_root_env_names_from_typed_support.
      - exact Hctx_alpha_apply.
      - exact Hsame_body_apply.
      - exact Hnodup_apply.
      - exact Hkeys_body. }
    destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (subst_type_params_expr type_args (fn_body fdef))
      T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots
      Hsummary_params rho
      (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall))))
      (subst_type_params_expr type_args (fn_body fcall))
      used_params used' Hctx_alpha_subst Hrn_initial Hrn_initial_r
      Hinitial_equiv Hkeys_initial_subst Hroots_initial_subst Hnocoll_initial
      Hnocoll_body Hctx_used_subst Hrange_used Hdisj_subst Hbody_rename_subst)
      as (Gamma_out_r & R_body_r & roots_body_r & ret_roots_r &
          Hsummary_renamed & _).
    apply Hnot_params.
    assert (Hfree_ctx :
      In x (ctx_names (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall)))))).
    { eapply expr_root_shadow_store_safe_narrow_summary_ready_free_vars_ctx_names.
      - exact Hsummary_renamed.
      - exact Hready.
      - exact Hin_free. }
    unfold sctx_of_ctx in Hfree_ctx.
    rewrite <- params_ctx_apply_type_params in Hfree_ctx.
    exact Hfree_ctx.
  - destruct Hgeneric as (fuel' & fname & nested_type_args & args & raw_body &
      synthetic_body & fcallee & T_body & Gamma_out & R_body & roots_body &
      Hfuel & Hbody & Htarget & Hsynthetic & Hsafe & Hin & Hname & Harity &
      Hbounds & Hnested & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
    destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime
      env type_args (store_names s_hidden) fdef fcall used' fname
      nested_type_args args raw_body synthetic_body Hbody Htarget Hsynthetic
      Hsafe Hrename)
      as (argsr & Hbody_runtime & Hsafe_runtime).
    rewrite Hbody_runtime in Hready.
    dependent destruction Hready.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_generic_direct_alpha_renamed_body_free_vars_hidden_seed_excludes :
  forall env fuel fdef type_args fname nested_type_args args raw_body
      synthetic_body fcallee T_body Gamma_out R_body roots_body fcall used'
      x T hidden s_hidden s_base,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fcallee nested_type_args ->
    NoDup (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fdef)))) ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
    roots_exclude_params (apply_type_params type_args (fn_params fdef))
      roots_body ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def (store_names s_hidden) fdef = (fcall, used') ->
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros env fuel fdef type_args fname nested_type_args args raw_body
    synthetic_body fcallee T_body Gamma_out R_body roots_body fcall used' x T
    hidden s_hidden s_base Hbody Htarget Hsynthetic Hsafe _ Hnodup Htyped
    Hexcl_roots Hcaps Hrename Hrel.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args
    env type_args (store_names s_hidden) fdef fcall used' fname
    nested_type_args args raw_body synthetic_body T_body Gamma_out R_body
    roots_body Hbody Htarget Hsynthetic Hsafe Hcaps Hrename Hnodup Htyped
    Hexcl_roots)
    as (argsr & fcallee_runtime & sigma & arg_roots & Sigma_out &
        R_out & roots_out & Hbody_runtime & Hsafe_runtime & Htyped_runtime &
        Htyped_args & _ & _ & _).
  rewrite Hbody_runtime. simpl.
  intros Hin.
  pose proof (store_hidden_frame_rel_name_in x T hidden s_hidden s_base Hrel)
    as Hused.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    (store_names s_hidden) fdef fcall used' type_args x Hrename Hused)
    as [Hnot_params _].
  assert (Hfree_ctx :
    In x (ctx_names (sctx_of_ctx
      (subst_type_params_ctx type_args (fn_body_ctx fcall))))).
  { eapply store_safe_function_value_call_args_typed_roots_free_vars_ctx_names.
    - eapply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_runtime.
    - exact Htyped_args.
    - exact Hin. }
  apply Hnot_params.
  rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall) in Hfree_ctx.
  - unfold sctx_of_ctx in Hfree_ctx.
    rewrite <- params_ctx_apply_type_params in Hfree_ctx.
    exact Hfree_ctx.
  - rewrite <- Hcaps.
    eapply alpha_rename_fn_def_captures. exact Hrename.
Qed.





Lemma hidden_frame_eval_strip_alpha_renamed_fn_body :
  forall env used fdef fcall used' type_args x T hidden s_with s_base
      s_body_with ret,
    alpha_rename_fn_def used fdef = (fcall, used') ->
    In x used ->
    eval env s_with
      (subst_type_params_expr type_args (fn_body fcall)) s_body_with ret ->
    store_hidden_frame_rel x T hidden s_with s_base ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcall)) ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))) ->
    store_refs_exclude_root x s_base ->
    exists s_body_base,
      store_hidden_frame_rel x T hidden s_body_with s_body_base /\
      eval env s_base
        (subst_type_params_expr type_args (fn_body fcall)) s_body_base ret /\
      store_refs_exclude_root x s_body_base /\
      value_refs_exclude_root x ret.
Proof.
  intros env used fdef fcall used' type_args x T hidden s_with s_base
    s_body_with ret Hrename Hused Heval Hrel Hready Hnot_free Hrefs.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    used fdef fcall used' type_args x Hrename Hused)
    as [_ Hnot_local].
  eapply (proj1 hidden_frame_eval_strip_rel_mutual); eassumption.
Qed.

Lemma eval_generic_direct_call_hidden_frame_args_strip :
  forall env x T hidden s_hidden s_base s_hidden' fname type_args args ret,
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s_base ->
    eval env s_hidden (ECallGeneric fname type_args args) s_hidden' ret ->
    exists fdef fcall used' s_args_hidden s_args vs s_body_hidden,
      lookup_fn fname (env_fns env) = Some fdef /\
      fn_captures fdef = [] /\
      store_hidden_frame_rel x T hidden s_args_hidden s_args /\
      eval_args env s_hidden args s_args_hidden vs /\
      eval_args env s_base args s_args vs /\
      store_refs_exclude_root x s_args /\
      Forall (value_refs_exclude_root x) vs /\
      alpha_rename_fn_def (store_names s_args_hidden) fdef =
        (fcall, used') /\
      eval env
        (bind_params (apply_type_params type_args (fn_params fcall))
          vs s_args_hidden)
        (subst_type_params_expr type_args (fn_body fcall))
        s_body_hidden ret /\
      s_hidden' =
        store_remove_params
          (apply_type_params type_args (fn_params fcall)) s_body_hidden.
Proof.
  intros env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    Hrel Hready Hnot_free Hnot_local Hrefs Heval.
  inversion Heval; subst; clear Heval.
  match goal with
  | Heval_args : eval_args env s_hidden args s_args vs |- _ =>
      destruct (proj1 (proj2 hidden_frame_eval_strip_rel_mutual)
        env s_hidden args s_args vs Heval_args x T hidden s_base Hrel Hready
        Hnot_free Hnot_local Hrefs)
        as (s_args_base & Hrel_args & Heval_args_base & Hrefs_args & Hvs_refs)
  end.
  exists fdef, fcall, used', s_args, s_args_base, vs, s_body.
  repeat split; try eassumption; reflexivity.
Qed.

Lemma eval_generic_direct_call_hidden_frame_expr_body_strip :
  forall env x T hidden s_hidden s_base s_hidden' fname type_args args ret
      fdef fcall used' s_args_hidden s_args vs s_body_hidden,
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s_base ->
    eval env s_hidden (ECallGeneric fname type_args args) s_hidden' ret ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_captures fdef = [] ->
    store_hidden_frame_rel x T hidden s_args_hidden s_args ->
    eval_args env s_base args s_args vs ->
    store_refs_exclude_root x s_args ->
    Forall (value_refs_exclude_root x) vs ->
    alpha_rename_fn_def (store_names s_args_hidden) fdef =
      (fcall, used') ->
    eval env
      (bind_params (apply_type_params type_args (fn_params fcall))
        vs s_args_hidden)
      (subst_type_params_expr type_args (fn_body fcall))
      s_body_hidden ret ->
    s_hidden' =
      store_remove_params
        (apply_type_params type_args (fn_params fcall)) s_body_hidden ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcall)) ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))) ->
    exists s_body_base s_final_base,
      store_hidden_frame_rel x T hidden s_body_hidden s_body_base /\
      eval env
        (bind_params (apply_type_params type_args (fn_params fcall))
          vs s_args)
        (subst_type_params_expr type_args (fn_body fcall))
        s_body_base ret /\
      store_refs_exclude_root x s_body_base /\
      value_refs_exclude_root x ret /\
      s_final_base =
        store_remove_params
          (apply_type_params type_args (fn_params fcall)) s_body_base /\
      store_hidden_frame_rel x T hidden s_hidden' s_final_base /\
      store_remove x s_hidden' = s_final_base.
Proof.
  intros env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    fdef fcall used' s_args_hidden s_args vs s_body_hidden Hrel Hready
    Hnot_free Hnot_local Hrefs Heval Hlookup Hcaps Hrel_args Heval_args
    Hrefs_args Hvs_refs Hrename Heval_body Hfinal Hready_body Hbody_not_free.
  pose proof (store_hidden_frame_rel_name_in x T hidden s_args_hidden s_args
    Hrel_args) as Hused.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    (store_names s_args_hidden) fdef fcall used' type_args x Hrename Hused)
    as [Hnotin_params Hnotin_body_locals].
  pose (ps := apply_type_params type_args (fn_params fcall)).
  assert (Hrel_bind :
    store_hidden_frame_rel x T hidden
      (bind_params ps vs s_args_hidden) (bind_params ps vs s_args)).
  { subst ps. eapply store_hidden_frame_rel_bind_params; eassumption. }
  assert (Hrefs_bind :
    store_refs_exclude_root x (bind_params ps vs s_args)).
  { subst ps. eapply bind_params_refs_exclude_root; eassumption. }
  destruct (hidden_frame_eval_strip_alpha_renamed_fn_body
    env (store_names s_args_hidden) fdef fcall used' type_args x T hidden
    (bind_params ps vs s_args_hidden) (bind_params ps vs s_args)
    s_body_hidden ret Hrename Hused Heval_body Hrel_bind Hready_body
    Hbody_not_free Hrefs_bind)
    as [s_body_base [Hrel_body [Heval_body_base [Hrefs_body Hv_refs]]]].
  exists s_body_base,
    (store_remove_params (apply_type_params type_args (fn_params fcall))
      s_body_base).
  repeat split; try eassumption; try reflexivity.
  - subst ps.
    rewrite Hfinal.
    eapply store_hidden_frame_rel_remove_params; eassumption.
  - eapply store_hidden_frame_rel_remove_base.
    subst ps.
    rewrite Hfinal.
    eapply store_hidden_frame_rel_remove_params; eassumption.
Qed.


Lemma eval_generic_direct_call_hidden_frame_package_from_stripped_body :
  forall env x T hidden s_hidden s_base s_hidden' fname type_args args ret
      Sigma_args R_args arg_roots ret_ty,
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s_base ->
    eval env s_hidden (ECallGeneric fname type_args args) s_hidden' ret ->
    (forall (fdef fcall : fn_def) (used' : list ident)
        (s_args_hidden s_args : store) (vs : list value)
        (s_body_hidden : store),
      lookup_fn fname (env_fns env) = Some fdef ->
      fn_captures fdef = [] ->
      store_hidden_frame_rel x T hidden s_args_hidden s_args ->
      eval_args env s_hidden args s_args_hidden vs ->
      eval_args env s_base args s_args vs ->
      store_refs_exclude_root x s_args ->
      Forall (value_refs_exclude_root x) vs ->
      alpha_rename_fn_def (store_names s_args_hidden) fdef =
        (fcall, used') ->
      eval env
        (bind_params (apply_type_params type_args (fn_params fcall))
          vs s_args_hidden)
        (subst_type_params_expr type_args (fn_body fcall))
        s_body_hidden ret ->
      s_hidden' =
        store_remove_params
          (apply_type_params type_args (fn_params fcall)) s_body_hidden ->
      generic_direct_call_runtime_package env s_base (store_remove x s_hidden')
        ret Sigma_args R_args arg_roots ret_ty) ->
    generic_direct_call_runtime_package env s_base (store_remove x s_hidden')
      ret Sigma_args R_args arg_roots ret_ty.
Proof.
  intros env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    Sigma_args R_args arg_roots ret_ty Hrel Hready Hnot_free Hnot_local Hrefs
    Heval Hpackage_body.
  destruct (eval_generic_direct_call_hidden_frame_args_strip
    env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    Hrel Hready Hnot_free Hnot_local Hrefs Heval)
    as (fdef & fcall & used' & s_args_hidden & s_args & vs &
        s_body_hidden & Hlookup & Hcaps & Hrel_args & Heval_args_hidden &
        Heval_args_base & Hrefs_args & Hvs_refs & Hrename &
        Heval_body_hidden & Hfinal_hidden).
  eapply Hpackage_body; eassumption.
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef fuel,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef fuel Hsafe_args Hsummary Hstore Hroots Hshadow
    Hrn Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  revert env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  induction fuel as [| fuel' IH]; intros env Omega n R Sigma fname type_args
    args sigma Sigma_args R_args arg_roots s s' ret fdef Hsafe_args Hsummary
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store Heval_call Hunique
    Hin_fdef Hname_fdef Hcaps_fdef Htyped_args Houtlives.
  - eapply eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr;
      try eassumption.
    eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero.
    exact Hsummary.
  - destruct (callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases
      env (S fuel') fdef type_args Hsummary) as [Hexpr | Hgeneric].
    + destruct Hexpr as (T_expr & Gamma_expr & R_expr & roots_expr &
        ret_roots_expr & Hnodup_expr & Hexpr_summary & Hcompat_expr &
        Hexcl_roots_expr & Hexcl_env_expr).
      eapply eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr;
        try eassumption.
      unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated.
      repeat eexists; repeat split; eassumption.
    + destruct Hgeneric as (fuel_nested & fname_nested & nested_type_args &
        args_static & raw_body & synthetic_body & fcallee_static & T_body &
        Gamma_out & R_body & roots_body & Hfuel_eq & Hbody & Htarget &
        Hsynthetic & Hsafe_static & Hin_static & Hname_static & Harity_static &
        Hbounds_static & Hsummary_nested & Hnodup_applied & Htyped_synthetic &
        Hcompat_body & Hexcl_roots & Hexcl_env).
      inversion Hfuel_eq; subst fuel_nested; clear Hfuel_eq.
      dependent destruction Heval_call.
      match goal with
      | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
          assert (f_runtime = fdef) as -> by
            (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
      end.
      match goal with
      | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
          rename H into Heval_args;
          rename s_args0 into s_args;
          rename vs0 into vs
      end.
      match goal with
      | H : alpha_rename_fn_def (store_names s_args) fdef =
            (?fcall0, ?used0) |- _ =>
          rename H into Hrename;
          rename fcall0 into fcall;
          rename used0 into used'
      end.
      match goal with
      | H : eval _
            (bind_params (apply_type_params type_args (fn_params fcall)) vs s_args)
            (subst_type_params_expr type_args (fn_body fcall)) ?s_body0 ret |- _ =>
          rename H into Heval_body;
          rename s_body0 into s_body
      end.
      pose proof (store_safe_function_value_call_args_preservation_ready
        env args Hsafe_args) as Hready_args.
      pose proof (preservation_ready_args_implies_provenance_ready_closure
        args Hready_args) as Hprov_args.
      destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
        env Omega n R Sigma args
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fdef)))
        Sigma_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
        Heval_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store)
        as (Hstore_args & Hargs_values_sigma & Hpres_args & Hroots_args &
            Harg_roots_values & Hshadow_args & Hrn_args & Hnamed_args &
            Hkeys_args & Hsummary_args).
      pose (ps_runtime := apply_type_params type_args (fn_params fcall)).
      destruct (generic_direct_call_args_bind_type_params_runtime_package
        env Omega n R Sigma args type_args sigma fdef fcall used'
        s s_args vs Sigma_args R_args arg_roots Hsafe_args Heval_args
        Htyped_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hunique
        Hsummary_store Hrename)
        as (Hstore_bind & Hroots_bind & Hshadow_bind & Hrn_bind & Hcover_bind &
            Hnamed_bind & Hkeys_bind & Hsummary_bind & Hframe_start).
      fold ps_runtime in Hstore_bind, Hroots_bind, Hshadow_bind, Hrn_bind,
        Hcover_bind, Hnamed_bind, Hkeys_bind, Hsummary_bind, Hframe_start.
      pose (body_env := global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef))).
      assert (Hstore_bind_body_env :
        store_typed_prefix body_env (bind_params ps_runtime vs s_args)
          (sctx_of_ctx (params_ctx ps_runtime))).
      { subst body_env.
        eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
        exact Hstore_bind. }
      assert (Heval_body_body_env :
        eval body_env (bind_params ps_runtime vs s_args)
          (subst_type_params_expr type_args (fn_body fcall)) s_body ret).
      { subst body_env ps_runtime.
        eapply direct_call_eval_global_env_with_local_bounds.
        exact Heval_body. }
      assert (Hsummary_bind_body_env :
        store_function_closure_targets_summary body_env
          (bind_params ps_runtime vs s_args)).
      { subst body_env.
        apply store_function_closure_targets_summary_global_env_with_local_bounds.
        exact Hsummary_bind. }
      assert (Hstore_bind_body_env_ctx :
        store_typed_prefix body_env (bind_params ps_runtime vs s_args)
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))).
      { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - rewrite <- params_ctx_apply_type_params.
          exact Hstore_bind_body_env.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hunique_body_env : fn_env_unique_by_name body_env).
      { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
      destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args_call_frame
        env Omega n R Sigma Sigma_args R_args arg_roots args type_args
        sigma fdef fcall used' fname_nested nested_type_args args_static
        raw_body synthetic_body T_body Gamma_out R_body roots_body s s_args vs
        Hbody Htarget Hsynthetic Hsafe_static Hcaps_fdef Hrename
        Hnodup_applied Htyped_synthetic Hexcl_roots Htyped_args Hsafe_args Heval_args
        Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys)
        as (argsr & fcallee_runtime & sigma_nested & nested_arg_roots &
            Sigma_nested & R_nested & Hbody_runtime & Hsafe_runtime &
            Htyped_nested & Hin_nested & Hname_nested_runtime & Hcaps_nested &
            Houtlives_nested & Hret_nested & Hexcl_nested_roots &
            Hnested_roots_subset).
      assert (Heval_nested : eval body_env
        (bind_params ps_runtime vs s_args)
        (ECallGeneric fname_nested nested_type_args argsr) s_body ret).
      { subst body_env ps_runtime.
        rewrite <- Hbody_runtime.
        exact Heval_body_body_env. }
      assert (Hsummary_nested_body_env :
        callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
          body_env fuel' fcallee_runtime nested_type_args).
      { subst body_env.
        assert (fcallee_runtime = fcallee_static) as ->.
        { eapply Hunique.
          - exact Hin_nested.
          - exact Hin_static.
          - rewrite Hname_nested_runtime. exact (eq_sym Hname_static). }
        eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
        - exact Hunique.
        - exact Hsummary_nested. }
      assert (Hsafe_runtime_body :
        store_safe_function_value_call_args body_env argsr).
      { subst body_env.
        eapply store_safe_function_value_call_args_global_env_with_local_bounds.
        exact Hsafe_runtime. }
      destruct (IH body_env (fn_outlives fdef) (fn_lifetimes fdef)
        (call_param_root_env ps_runtime arg_roots R_args)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        fname_nested nested_type_args argsr sigma_nested Sigma_nested R_nested
        nested_arg_roots (bind_params ps_runtime vs s_args) s_body ret
        fcallee_runtime Hsafe_runtime_body Hsummary_nested_body_env
        Hstore_bind_body_env_ctx Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
        Hkeys_bind Hsummary_bind_body_env Heval_nested Hunique_body_env
        Hin_nested Hname_nested_runtime Hcaps_nested Htyped_nested
        Houtlives_nested)
        as [Hpkg_nested [s_nested_args [vs_nested [Heval_nested_args Hbody_eq]]]].
      assert (Hargs_values_fdef_type :
        eval_args_values_have_types env Omega s_args vs
          (apply_type_params type_args (fn_params fdef))).
      { eapply eval_args_values_have_types_apply_lt_params_inv.
        exact Hargs_values_sigma. }
      pose proof (alpha_rename_fn_def_shape (store_names s_args)
                    fdef fcall used' Hrename) as Hshape.
      destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
      assert (Hargs_values_fcall_type :
        eval_args_values_have_types env Omega s_args vs ps_runtime).
      { subst ps_runtime.
        eapply eval_args_values_have_types_params_alpha.
        - apply params_alpha_apply_type_compat. exact Hparams_alpha.
        - exact Hargs_values_fdef_type. }
      assert (Hfresh : params_fresh_in_store ps_runtime s_args).
      { subst ps_runtime.
        unfold params_fresh_in_store.
        rewrite params_ctx_apply_type_params.
        rewrite ctx_names_subst_type_params_ctx.
        eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
      assert (Hframe_scope_start :
        store_frame_scope ps_runtime (sctx_of_ctx (params_ctx ps_runtime))
          (bind_params ps_runtime vs s_args) s_args).
      { eapply store_frame_scope_bind_params. exact Hargs_values_fcall_type. }
      assert (Hframe_fresh_start :
        store_frame_static_fresh (sctx_of_ctx (params_ctx ps_runtime)) s_args).
      { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
      assert (Hframe_scope_start_ctx :
        store_frame_scope ps_runtime
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
          (bind_params ps_runtime vs s_args) s_args).
      { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - rewrite <- params_ctx_apply_type_params.
          exact Hframe_scope_start.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hframe_fresh_start_ctx :
        store_frame_static_fresh
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
          s_args).
      { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - rewrite <- params_ctx_apply_type_params.
          exact Hframe_fresh_start.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hprov_runtime_body : provenance_ready_args argsr).
      { apply preservation_ready_args_implies_provenance_ready_closure.
        eapply store_safe_function_value_call_args_preservation_ready.
        exact Hsafe_runtime_body. }
      destruct (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
        body_env (bind_params ps_runtime vs s_args) argsr s_nested_args
        vs_nested Heval_nested_args (fn_outlives fdef) (fn_lifetimes fdef)
        (call_param_root_env ps_runtime arg_roots R_args)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        (apply_lt_params sigma_nested
          (apply_type_params nested_type_args (fn_params fcallee_runtime)))
        Sigma_nested R_nested nested_arg_roots ps_runtime s_args
        Hprov_runtime_body
        Htyped_nested Hcover_bind Hroots_bind Hshadow_bind Hrn_bind
        Hframe_scope_start_ctx Hframe_fresh_start_ctx)
        as [_ [_ [_ [_ [Hframe_scope_nested Hframe_fresh_nested]]]]].
      assert (Hsame_nested :
        sctx_same_bindings (sctx_of_ctx (params_ctx ps_runtime)) Sigma_nested).
      { subst ps_runtime.
        rewrite params_ctx_apply_type_params.
        rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
        - eapply typed_args_env_structural_same_bindings.
          eapply typed_args_roots_structural. exact Htyped_nested.
        - rewrite <- Hcaps_fdef.
          eapply alpha_rename_fn_def_captures. exact Hrename. }
      assert (Hscope_nested : store_param_scope ps_runtime s_nested_args s_args).
      { eapply store_frame_scope_param_scope. exact Hframe_scope_nested. }
      assert (Hremoved_exact : store_remove_params ps_runtime s_body = s_args).
      { rewrite Hbody_eq.
        eapply store_remove_params_store_frame_scope_exact.
        - exact Hsame_nested.
        - exact Hscope_nested.
        - exact Hframe_scope_nested. }
      fold ps_runtime.
      rewrite Hremoved_exact.
      split.
      * constructor.
        -- exact Hstore_args.
        -- rewrite <- Hremoved_exact.
           rewrite Hbody_eq.
           assert (Hv_nested_env :
             value_has_type env s_nested_args ret
               (apply_lt_ty sigma_nested
                 (subst_type_params_ty nested_type_args
                   (fn_ret fcallee_runtime)))).
           { rewrite <- Hbody_eq.
             subst body_env.
             eapply direct_call_value_has_type_clear_global_env_local_bounds.
             exact (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg_nested). }
           assert (Hv_body : value_has_type env s_nested_args ret T_body).
           { rewrite Hret_nested. exact Hv_nested_env. }
           assert (Hv_fdef_inst :
             value_has_type env s_nested_args ret
               (subst_type_params_ty type_args (fn_ret fdef))).
           { eapply value_has_type_compatible.
             - exact Hv_body.
             - apply ty_compatible_b_sound with (Ω := fn_outlives fdef).
               exact Hcompat_body. }
           assert (Hv_fcall_inst :
             value_has_type env s_nested_args ret
               (subst_type_params_ty type_args (fn_ret fcall))).
           { rewrite <- Hret_alpha. exact Hv_fdef_inst. }
           assert (Hret_exclude : value_refs_exclude_params ps_runtime ret).
           { eapply value_roots_exclude_params.
             - exact (generic_direct_call_package_value_roots
                 _ _ _ _ _ _ _ _ Hpkg_nested).
             - exact Hexcl_nested_roots. }
           apply value_has_type_apply_lt_ty.
           rewrite Hret_alpha.
           eapply value_has_type_store_remove_params_excluding.
           ++ exact Hv_fcall_inst.
           ++ exact Hret_exclude.
        -- exact Hpres_args.
        -- exact Hroots_args.
        -- eapply direct_call_value_roots_within_store_subset.
           ++ exact (generic_direct_call_package_value_roots _ _ _ _ _ _ _ _ Hpkg_nested).
           ++ exact Hnested_roots_subset.
        -- exact Hshadow_args.
        -- exact Hrn_args.
        -- exact Hnamed_args.
        -- exact Hkeys_args.
        -- exact Hsummary_args.
      * exists s_args, vs.
        split; [exact Heval_args | reflexivity].
Qed.


Lemma eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel_zero :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 0 fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps Htyped_args
    Houtlives.
  eapply eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr;
    try eassumption.
  eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero.
  exact Hsummary.
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef fuel,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef fuel Hsafe_args Hsummary Hstore Hroots Hshadow
    Hrn Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps Htyped_args
    Houtlives.
  destruct (eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel
    env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef fuel Hsafe_args Hsummary Hstore Hroots Hshadow
    Hrn Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps
    Htyped_args Houtlives) as [Hpkg _].
  exact (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg).
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel_zero :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 0 fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hin Hname Hcaps Htyped_args
    Houtlives.
  eapply eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named;
    try eassumption.
  eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero.
  exact Hsummary.
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

Lemma initial_root_env_for_params_covers :
  forall ps,
    root_env_covers_params ps (initial_root_env_for_params ps).
Proof.
  induction ps as [| p ps IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Hx | Hin].
    + subst x. exists [RParam (param_name p)].
      simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl.
      destruct (ident_eqb x (param_name p)) eqn:Heq.
      * exists [RParam (param_name p)]. reflexivity.
      * destruct (IH x Hin) as [roots Hlookup].
        exists roots. exact Hlookup.
Qed.

Lemma initial_root_env_for_fn_covers :
  forall f,
    root_env_covers_params (fn_params f) (initial_root_env_for_fn f).
Proof.
  intros f.
  unfold initial_root_env_for_fn.
  apply initial_root_env_for_params_covers.
Qed.

Lemma runtime_struct_expr_true : forall e,
  struct_expr e = true.
Proof.
  fix IH 1.
  intro e.
  destruct e; simpl; try reflexivity.
  - rewrite IH, IH. reflexivity.
  - rewrite IH, IH. reflexivity.
	  - induction l as [| a rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
	  - induction l0 as [| a rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
	  - rewrite IH.
	    induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l0 as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l1 as [| [fname field] rest IHfields]; simpl.
    + reflexivity.
    + rewrite IH, IHfields. reflexivity.
	  - induction l1 as [| payload rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| [[name binders] branch] rest IHbranches]; simpl.
    + reflexivity.
    + rewrite IH, IHbranches. reflexivity.
	  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, IH, IH. reflexivity.
Qed.

Lemma infer_core_env_runtime_structural_sound :
  forall env Ω n Γ e T Γ',
    infer_core_env env Ω n Γ e = infer_ok (T, Γ') ->
    typed_env_structural env Ω n (sctx_of_ctx Γ) e T (sctx_of_ctx Γ').
Proof.
  unfold infer_core_env, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n Γ e T Γ' Hinfer.
  destruct (infer_core_env_state_fuel 10000 env Ω n Γ e) as [[T0 Σ] | err]
    eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_struct_structural_sound.
  - apply runtime_struct_expr_true.
  - exact Hcore.
Qed.

Lemma infer_env_runtime_structural_sound :
  forall env f T Γ',
    infer_env env f = infer_ok (T, Γ') ->
    typed_fn_env_structural env f.
Proof.
  unfold infer_env, typed_fn_env_structural.
  intros env f T Γ' Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env (global_env_with_local_bounds env (fn_bounds f))
              (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
              (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompatible; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_out) eqn:Hparams;
    try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ'.
  repeat split.
  - eapply infer_core_env_runtime_structural_sound. exact Hcore.
  - exact Hcompatible.
  - exact Hparams.
Qed.

Lemma call_body_start_state_param_scope :
  forall env Ω s_args vs ps,
    eval_args_values_have_types env Ω s_args vs ps ->
    store_param_scope ps (bind_params ps vs s_args) s_args /\
    root_env_covers_params ps (initial_root_env_for_params ps).
Proof.
  intros env Ω s_args vs ps Hargs.
  split.
  - eapply store_param_scope_bind_params. exact Hargs.
  - apply initial_root_env_for_params_covers.
Qed.

Theorem infer_full_env_roots_big_step_safe_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed env f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Htyped)
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready
    Hroots Hstore_shadow Hroot_shadow Heval.
  eapply infer_full_env_roots_big_step_safe_ready; eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_structural_ready :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_ready_expr (fn_body f) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v Hinfer Hstore Hready Heval.
  unfold infer_full_env in Hinfer.
  destruct (infer_env (alpha_normalize_global_env env) f)
    as [[T0 Γ0] | err] eqn:Hinfer_env; try discriminate.
  destruct (borrow_check_env (alpha_normalize_global_env env) []
              (fn_body_ctx f) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  eapply typed_fn_env_structural_big_step_safe_ready.
  - eapply infer_env_runtime_structural_sound. exact Hinfer_env.
  - exact Hready.
  - exact (initial_store_for_fn_store_typed (alpha_normalize_global_env env) f s Hstore).
  - exact Heval.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed env f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique_body_env Hfns_ready_body_env
      (direct_call_callee_body_root_evidence_of_check body_env
        Hcallee_body_roots))
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_evidence :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed env f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique_body_env Hfns_ready_body_env Hcallee_body_roots)
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready Hroots
    Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready Hcallee_roots Heval.
  eapply infer_full_env_roots_big_step_safe_direct_call_ready; eassumption.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_direct_call_evidence :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready Hroots
    Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready Hcallee_roots Heval.
  eapply infer_full_env_roots_big_step_safe_direct_call_evidence;
    eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_summary_check_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_summary_bridge
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hsummary
    Hbridge Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_evidence;
    try eassumption.
  eapply direct_call_callee_body_root_evidence_of_summary_bridge.
  - apply env_fns_root_summary_evidence_of_check.
    apply env_fns_root_summary_check_ready_global_env_with_local_bounds.
    exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    direct_call_callee_body_root_shadow_summary_bridge
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hsummary
    Hbridge Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_evidence;
    try eassumption.
  eapply direct_call_callee_body_root_evidence_of_shadow_summary_bridge.
  - exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge_of_unique :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hroots_infer Hsummary
    Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge;
    try eassumption.
  apply direct_call_callee_body_root_shadow_summary_bridge_of_unique.
  exact Hunique.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_shadow_summary_sidecar :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hroots_infer Hsummary
    Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge_of_unique;
    eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_shadow_summary_evidence :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within (initial_root_env_for_fn f) s ->
    store_no_shadow s ->
    root_env_store_roots_named (initial_root_env_for_fn f) s ->
    root_env_store_keys_named (initial_root_env_for_fn f) s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v _ Hsummary Hin Hstore Hready Hroots
    Hstore_shadow Hnamed Hkeys Hunique Hfns_ready Heval.
  destruct (env_fns_root_shadow_summary_evidence_in_unique
              (alpha_normalize_global_env env) Hsummary Hunique
              (fn_name f) f Hin eq_refl)
    as [Hnodup Hbody_summary].
  unfold callee_body_root_shadow_ready_at in Hbody_summary.
  destruct Hbody_summary as
    (T_body & Γ_out & R_body & roots_body &
      _ & _ & Htyped_shadow & Hcompat & _ & _).
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
  pose (body_env :=
    global_env_with_local_bounds (alpha_normalize_global_env env)
      (fn_bounds f)).
  assert (Hstore_body_env :
      store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    exact (initial_store_for_fn_store_typed (alpha_normalize_global_env env) f s Hstore). }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  assert (Hsummary_body :
      env_fns_root_shadow_summary_evidence body_env).
  { subst body_env.
    apply env_fns_root_shadow_summary_evidence_global_env_with_local_bounds.
    exact Hsummary. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
      (typed_env_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
        Htyped_shadow)
      Hunique_body_env Hfns_ready_body_env
      (direct_call_callee_body_root_evidence_of_shadow_summary_bridge
        body_env
        Hsummary_body
        (direct_call_callee_body_root_shadow_summary_bridge_of_unique
          body_env Hunique_body_env)))
    as [_ [Hv _]].
  assert (Hv_env :
      value_has_type (alpha_normalize_global_env env) s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.
