From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots AssocEnvCallStructuralBoundary.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectRuntimePackageBase
  EnvRuntimeCheckedPrefixRuntimePackage.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

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
    { destruct Harg; dependent destruction H; try exact Hcover.
      - match goal with
        | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ [] _ _ _ _ |- _ =>
            dependent destruction Hfields
        end.
        exact Hcover.
      - match goal with
        | Hpayloads : typed_args_roots_shadow_safe _ _ _ _ _ [] _ _ _ _ |- _ =>
            dependent destruction Hpayloads
        end.
        exact Hcover. }
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
  - inversion H; subst; try discriminate;
      inversion Heval; subst;
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
  - inversion H; subst; try discriminate; inversion Heval; subst; exists frame; exact Hscope.
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

Lemma expr_root_shadow_store_safe_narrow_summary_checked_assoc_boundary_preserves_param_scope_cover_prefix_named :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T
      Sigma' R' roots ret_roots ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T
      Sigma' R' roots ->
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
      store_param_scope ps s frame ->
      exists frame',
        store_param_scope ps s' frame' /\ root_env_covers_params ps R'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary
    Hboundary s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary_store Heval Hunique Hcover Hscope.
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary_store Heval Hunique Hcover Hscope) as [frame' Hscope'].
  exists frame'. split.
  - exact Hscope'.
  - eapply typed_env_roots_checked_assoc_boundary_preserves_param_cover;
      eassumption.
Qed.


Lemma eval_direct_call_store_safe_narrow_summary_exact_package_prefix_named :
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
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots (apply_lt_ty sigma (fn_ret fdef)) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
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
  destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
    env Omega n R Sigma args (apply_lt_params sigma (fn_params fdef))
    Sigma_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
    Heval_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store)
    as (Hstore_args & Hargs_values_sigma & Hpres_args & Hroots_args &
        Harg_roots_values & Hshadow_args & Hrn_args & Hnamed_args &
        Hkeys_args & Hsummary_args).
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys)
    as [_ [Harg_roots_named _]].
  destruct (direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    (map param_ty (apply_lt_params sigma (fn_params fdef)))
    (apply_lt_ty sigma (fn_ret fdef)) s s_args vs used'
    Hsummary Hcaps_fdef Hbridge Hsafe_args Htyped_args_param_tys Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
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
  { eapply store_safe_function_value_call_args_bind_params_summary
      with (args := args) (s := s); eassumption. }
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
  assert (Hframe_scope_start :
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_values_fcall. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh (sctx_of_ctx (params_ctx (fn_params fcall)))
      s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R_args)
    (sctx_of_ctx (params_ctx (fn_params fcall)))
    (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots
    Hsummary_body_env
    (bind_params (fn_params fcall) vs s_args) s_body ret
    (fn_params fcall) s_args Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Hsummary_bind_body_env
    Heval_body_body_env Hunique_body_env Hcover_bind Hframe_scope_start
    Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope_body _]]]]].
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall))) Sigma_out).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots.
    eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_body_env. }
  assert (Hscope_body_args : store_param_scope (fn_params fcall) s_body s_args).
  { eapply store_frame_scope_param_scope. exact Hframe_scope_body. }
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
              (fn_params fcall) s_body s_args R_body roots_body ret
              Hscope_body_args Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty sigma (fn_ret fdef))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  assert (Hremoved_exact :
    store_remove_params (fn_params fcall) s_body = s_args).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - exact Hscope_body_args.
    - exact Hframe_scope_body. }
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

Lemma eval_direct_call_store_safe_narrow_summary_package_prefix_named :
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
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots (apply_lt_ty sigma (fn_ret fdef)).
Proof.
  intros.
  destruct (eval_direct_call_store_safe_narrow_summary_exact_package_prefix_named
    env Omega n R Sigma fname args sigma Sigma_args R_args arg_roots s s'
    ret fdef) as [Hpkg _]; eauto.
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

