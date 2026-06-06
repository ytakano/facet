From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeNarrowCheckerFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_store_function_closure_targets_summary :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    env_fns_root_shadow_provenance_summary_evidence env ->
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_function_closure_targets_summary env s'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hevidence Hsummary
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys _ Heval_callee Hunique.
  destruct (eval_expr_root_shadow_captured_call_provenance_summary_exact_package
    env Ω n R Σ e T Σ' R' roots ret_roots Hsummary s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval_callee Hunique)
    as [Hstore' _].
  eapply store_typed_function_closure_targets_summary; eassumption.
Qed.

Lemma eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary :
  forall env s s' x fname fdef,
    store_function_closure_targets_summary env s ->
    eval env s (EVar x) s' (VClosure fname []) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.
Proof.
  intros env s s' x fname fdef Hstore Heval_callee Hlookup.
  inversion Heval_callee; subst;
    match goal with
    | Hlookup_store : store_lookup ?x_lookup ?s_lookup = Some ?se |- _ =>
        pose proof
          (store_function_closure_targets_summary_lookup env s_lookup x_lookup se
            Hstore Hlookup_store) as Hvalue_summary
    end;
    match goal with
    | Hvalue_eq : se_val _ = VClosure _ _ |- _ =>
        rewrite Hvalue_eq in Hvalue_summary
    | Hvalue_eq : VClosure _ _ = se_val _ |- _ =>
        rewrite <- Hvalue_eq in Hvalue_summary
    end;
    simpl in Hvalue_summary;
    destruct Hvalue_summary as (fdef_summary & Hlookup_summary & Hsummary);
    assert (fdef_summary = fdef) as -> by
      (eapply lookup_fn_deterministic; eassumption);
    exact Hsummary.
Qed.

Lemma expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary :
  forall env Omega n R Σ x args T_callee Σ_callee R_callee roots_callee T Σ' R' roots,
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      T_callee Σ_callee R_callee roots_callee ->
    supported_non_type_generic_function_value_call_callee_shape T_callee ->
    typed_env_roots_shadow_safe env Omega n R Σ
      (ECallExpr (EVar x) args) T Σ' R' roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args T_callee Σ_callee R_callee roots_callee T Σ' R' roots Hargs Htyped_callee_summary Hcallee_shape Htyped
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_callee Hunique.
  dependent destruction Heval_callee.
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
  pose proof (store_function_closure_targets_summary_eval_var
    env s s_fn x (VClosure fname captured) Hsummary Heval_callee) as Hsummary_fn.
  pose proof
    (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
      env args s_fn s_args vs Hargs Hsummary_fn Heval_args) as Hsummary_args.
  dependent destruction Htyped.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TFn param_tys ret))
      Σ1 R1 roots_callee0 Htyped) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TFn param_tys ret))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [_ [Hv_callee _]].
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TFn param_tys ret)) Hv_callee) as Hcaptured_nil.
    subst captured.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
    pose proof (eval_call_expr_tfn_components_final_store_eq
      env s s_fn s_args s_body (EVar x) args fname [] fdef fcall
      vs ret0 used' Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      param_tys ret (store_safe_function_value_call_args_preservation_ready env args Hargs)
      (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Htyped H0 Hunique Hcallee_summary) as Heq_final.
    rewrite Heq_final. exact Hsummary_args.
  - pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
      env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
      (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee0
      Htyped_callee_summary Htyped) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape];
      rewrite Hcore in Hshape; simpl in Hshape; discriminate.
  - match goal with
    | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
        ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          T_typed Σ_typed R_typed roots_typed
          Htyped_callee_summary Htyped_callee) as Hcore;
        destruct Hcallee_shape as
          [Tshape params_shape ret_shape Hshape
          | Tshape m_shape bounds_shape body_shape params_shape ret_shape
              Hshape Hbody_shape];
        rewrite Hcore in Hshape; simpl in Hshape;
        first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
    end.
  - pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
      env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
      (MkTy u (TForall m bounds
        (MkTy u_body (TTypeForall type_params type_bounds body_ty))))
      Σ1 R1 roots_callee0 Htyped_callee_summary Htyped) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape].
    + rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + rewrite Hcore in Hshape; simpl in Hshape.
      inversion Hshape; subst.
      simpl in Hbody_shape. discriminate.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 Htyped) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
    destruct (proj1 eval_preserves_root_names_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Hnamed Htyped_callee_roots) as [Hnamed_fn _].
    pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Hkeys Htyped_callee_roots) as Hkeys_fn.
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
    subst captured.
    simpl in Hrename, Heval_body.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
    destruct (value_has_type_empty_closure_tforall_tfn_components
      env s_fn fname fdef u m bounds body_ty param_tys ret σ
      Hv_callee Hlookup Hunique H0) as [Htype_params [Hcaps_fdef Hbridge]].
    pose proof (typed_args_roots_shadow_safe_roots
      env Omega n R1 Σ1 args
      (params_of_tys (map (open_bound_ty σ) param_tys))
      Σ' R' arg_roots H4) as Htyped_args.
    pose proof (preservation_ready_args_implies_provenance_ready_closure
      args (store_safe_function_value_call_args_preservation_ready env args Hargs)) as Hprov_args.
    assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
    { eapply direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset;
        eassumption. }
    pose proof (eval_evar_call_expr_lifetime_forall_tfn_components_final_store_eq
      env s s_fn s_args s_body x args fname [] fdef fcall vs ret0 used'
      Heval_callee Hlookup Heval_args Hrename Heval_body Omega n R Σ Σ1 R1 Σ' R'
      roots_callee0 arg_roots u m bounds body_ty param_tys ret σ (store_safe_function_value_call_args_preservation_ready env args Hargs)
      Hstore Hroots Hshadow Hrn Htyped H0 H4 Htype_params Hcaps_fdef
      Hbridge Hcallee_route) as Heq_final.
    rewrite Heq_final. exact Hsummary_args.
  - pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
      env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
      (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
      Htyped_callee_summary Htyped) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape].
    + rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + rewrite Hcore in Hshape; simpl in Hshape.
      inversion Hshape; subst.
      simpl in Hbody_shape. rewrite H0 in Hbody_shape. discriminate.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package :
  forall env Omega n R Σ x args u param_tys ret_ty Σ1 R1
      roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Σ1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys param_tys) Σ' R' arg_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_typed env s' Σ' /\
      value_has_type env s' ret ret_ty /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u param_tys ret_ty Σ1 R1
    roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TFn param_tys ret_ty))).
  { eapply SFV_TFn. reflexivity. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  pose proof
    (expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary
      env Omega n R Σ x args (MkTy u (TFn param_tys ret_ty)) Σ1 R1
      roots_callee_typed ret_ty Σ' R'
      (root_set_union roots_callee_typed (root_sets_union arg_roots))
      Hargs Htyped_callee Hcallee_shape Htyped_call
      s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call
      Hunique) as Hsummary'.
  inversion Heval_call; subst; clear Heval_call.
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
    env Omega n R Σ (EVar x) (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [_ [Hv_callee _]].
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  destruct (eval_call_expr_tfn_components_preserve_typing_with_callee_summary
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall
    vs ret used' Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped_callee Htyped_args Hunique)
    as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  { eapply eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary.
    - exact Hsummary.
    - exact Heval_callee.
    - exact Hlookup. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed
    env Omega n R Σ (ECallExpr (EVar x) args) ret_ty Σ' R'
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    s (store_remove_params (fn_captures fcall)
         (store_remove_params (fn_params fcall) s_body))
    Hnarrow Hstore Hrn Hnamed Hkeys Hstore' Hrn')
    as [Hnamed' [Hrootset_named Hkeys']].
  repeat split; eassumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package :
  forall env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
      Σ1 R1 roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty σ ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives σ bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_typed env s' Σ' /\
      value_has_type env s' ret (open_bound_ty σ ret_ty) /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
    Σ1 R1 roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Hbody_shape
    Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call
    Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Forall_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Hbody_shape.
    - exact Hret_closed.
    - exact Hbounds_closed.
    - exact Hbounds.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TForall m bounds body_ty))).
  { eapply SFV_TForall_TFn.
    - reflexivity.
    - exact Hbody_shape. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  pose proof
    (expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary
      env Omega n R Σ x args (MkTy u (TForall m bounds body_ty)) Σ1 R1
      roots_callee_typed (open_bound_ty σ ret_ty) Σ' R'
      (root_set_union roots_callee_typed (root_sets_union arg_roots))
      Hargs Htyped_callee Hcallee_shape Htyped_call
      s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call
      Hunique) as Hsummary'.
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
    env Omega n R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (proj1 eval_preserves_root_names_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Hnamed Htyped_callee_roots) as [Hnamed_fn _].
  pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Hkeys Htyped_callee_roots) as Hkeys_fn.
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  destruct (value_has_type_empty_closure_tforall_tfn_components
    env s_fn fname fdef u m bounds body_ty param_tys ret_ty σ
    Hv_callee Hlookup Hunique Hbody_shape) as [Htype_params [Hcaps_fdef Hbridge]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Σ1 args
    (params_of_tys (map (open_bound_ty σ) param_tys))
    Σ' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset
      env Omega n R1 Σ1 Σ' R' arg_roots args fdef fcall
      (map (open_bound_ty σ) param_tys) (open_bound_ty σ ret_ty)
      s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
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
  destruct (eval_evar_call_expr_lifetime_forall_tfn_components_preserve_typing_with_callee_summary_route
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty σ
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route)
    as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed
    env Omega n R Σ (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    s (store_remove_params (fn_captures fcall)
         (store_remove_params (fn_params fcall) s_body))
    Hnarrow Hstore Hrn Hnamed Hkeys Hstore' Hrn')
    as [Hnamed' [Hrootset_named Hkeys']].
  repeat split; eassumption.
Qed.

Lemma store_function_closure_targets_summary_eval_drop_place_direct :
  forall env s s' p ret,
    store_function_closure_targets_summary env s ->
    eval env s (EDrop (EPlace p)) s' ret ->
    store_function_closure_targets_summary env s'.
Proof.
  intros env s s' p ret Hsummary Heval.
  inversion Heval; subst.
  match goal with
  | Hplace : eval env s (EPlace p) s' _ |- _ =>
      inversion Hplace; subst; eauto using store_function_closure_targets_summary_store_consume_path
  end.
Qed.



Lemma eval_struct_fields_empty_exprs_store_eq :
  forall env s defs s' values,
    eval_struct_fields env s [] defs s' values ->
    s' = s.
Proof.
  intros env s defs s' values Heval.
  dependent induction Heval.
  reflexivity.
Qed.

Lemma store_update_path_nil_update_val :
  forall x v s,
    store_update_path x [] v s = store_update_val x v s.
Proof.
  intros x v s.
  induction s as [| se rest IH]; simpl.
  - reflexivity.
  - destruct (ident_eqb x (se_name se)); simpl; rewrite ?IH; try reflexivity.
    rewrite value_update_path_nil. reflexivity.
Qed.

Lemma eval_struct_fields_empty_exprs_values_nil :
  forall env s defs s' values,
    eval_struct_fields env s [] defs s' values ->
    values = [].
Proof.
  intros env s defs s' values Heval.
  dependent induction Heval.
  reflexivity.
Qed.

Lemma alpha_rename_fn_def_subst_empty_struct_body :
  forall used f fr used' type_args sname lts tys,
    fn_params f = [] ->
    subst_type_params_expr type_args (fn_body f) = EStruct sname lts tys [] ->
    alpha_rename_fn_def used f = (fr, used') ->
    fn_params fr = [] /\
    subst_type_params_expr type_args (fn_body fr) = EStruct sname lts tys [].
Proof.
  intros used f fr used' type_args sname lts tys Hparams Hbody Hrename.
  unfold alpha_rename_fn_def in Hrename.
  destruct (alpha_rename_params []
    (param_names (fn_params f) ++ param_names (fn_captures f) ++
      free_vars_expr (fn_body f) ++ used) (fn_params f))
    as [[params_r rho] used1] eqn:Hparams_r.
  rewrite Hparams in Hparams_r. simpl in Hparams_r.
  inversion Hparams_r; subst params_r rho used1; clear Hparams_r.
  simpl in Hrename.
  remember (alpha_rename_expr []
    (param_names (fn_captures f) ++ free_vars_expr (fn_body f) ++ used)
    (fn_body f)) as body_pair eqn:Hbody_r.
  destruct body_pair as [body_r used2]. simpl in Hrename.
  pose proof (alpha_rename_expr_subst_type_params_expr type_args []
    (param_names (fn_captures f) ++ free_vars_expr (fn_body f) ++ used)
    (fn_body f) body_r used2 (eq_sym Hbody_r)) as Hsubst.
  inversion Hrename; subst; clear Hrename. simpl.
  split; [reflexivity |].
  rewrite Hbody in Hsubst. simpl in Hsubst.
  inversion Hsubst. reflexivity.
Qed.

Lemma eval_call_generic_empty_struct_no_params_store_eq :
  forall env s s' fname type_args fcallee sname lts tys ret,
    fn_env_unique_by_name env ->
    In fcallee (env_fns env) ->
    fn_name fcallee = fname ->
    fn_params fcallee = [] ->
    subst_type_params_expr type_args (fn_body fcallee) = EStruct sname lts tys [] ->
    eval env s (ECallGeneric fname type_args []) s' ret ->
    s' = s /\ ret = VStruct sname [].
Proof.
  intros env s s' fname type_args fcallee sname lts tys ret
    Hunique Hin Hname Hparams Hbody Heval.
  inversion Heval; subst; try discriminate.
  match goal with
  | Hargs : eval_args _ _ [] _ _ |- _ => inversion Hargs; subst; clear Hargs
  end.
  match goal with
  | Hlookup : lookup_fn (fn_name fcallee) (env_fns env) = Some ?fdef |- _ =>
      assert (Hfdef : fdef = fcallee);
      [ eapply lookup_fn_unique_by_name;
        [ exact Hlookup | exact Hin | reflexivity | exact Hunique ]
      | subst fdef ]
  end.
  match goal with
  | Hrename : alpha_rename_fn_def (store_names ?s_args) fcallee = (?fcall, ?used') |- _ =>
      destruct (alpha_rename_fn_def_subst_empty_struct_body
        (store_names s_args) fcallee fcall used' type_args sname lts tys
        Hparams Hbody Hrename) as [Hparams_call Hbody_call]
  end.
  match goal with
  | Hbody_eval : eval env
      (bind_params (apply_type_params type_args (fn_params ?fcall)) [] ?s_args)
      (subst_type_params_expr type_args (fn_body ?fcall)) _ _ |- _ =>
      rewrite Hparams_call in Hbody_eval; simpl in Hbody_eval;
      rewrite Hbody_call in Hbody_eval;
      inversion Hbody_eval; subst; try discriminate; clear Hbody_eval
  end.
  rewrite Hparams_call in *; simpl in *.
  match goal with
  | Hfields : eval_struct_fields env ?s_args [] _ ?s_body ?values |- _ =>
      pose proof (eval_struct_fields_empty_exprs_store_eq
        env s_args _ s_body values Hfields) as Hstore_eq;
      pose proof (eval_struct_fields_empty_exprs_values_nil
        env s_args _ s_body values Hfields) as Hvalues_eq;
      subst s_body; subst values
  end.
  simpl in *. repeat split; reflexivity.
Qed.

Lemma empty_struct_value_has_type_from_narrow_summary :
  forall env Omega n R Sigma sname lts tys T Sigma' R' roots ret_roots s,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma
      (EStruct sname lts tys []) T Sigma' R' roots ret_roots ->
    value_has_type env s (VStruct sname []) T.
Proof.
  intros env Omega n R Sigma sname lts tys T Sigma' R' roots ret_roots s Hsummary.
  inversion Hsummary; subst; try congruence.
  match goal with
  | Htyped : typed_env_roots_shadow_safe _ _ _ _ _
      (EStruct _ _ _ []) _ _ _ _ |- _ =>
      inversion Htyped; subst; try congruence
  end.
  match goal with
  | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      dependent destruction Hfields
  end.
  eapply VHT_Struct.
  - eassumption.
  - match goal with
    | Hfields_nil : [] = struct_fields _ |- _ =>
        rewrite <- Hfields_nil; constructor
    end.
Qed.


