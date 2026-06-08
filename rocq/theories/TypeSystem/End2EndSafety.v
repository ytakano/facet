From Facet.TypeSystem Require Import Types Syntax Program RootProvenance TypeChecker EnvRootSoundness EnvRuntimeValidatorFacts EnvRuntimeCapturedSafety.
From Stdlib Require Import List Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* End-to-end checker entrypoint soundness                              *)
(* ------------------------------------------------------------------ *)

Theorem infer_fn_env_end2end_sound :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    checked_fn_env_roots_checked env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end in Hend.
  remember (initial_root_env_for_params (fn_params f ++ fn_captures f))
    as R0 eqn:HR0.
  destruct (infer_full_env_roots_checked env f R0)
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_captured_call_store_safe_summary env f);
    try discriminate.
  injection Hend as <- <- <- <-.
  eapply infer_full_env_roots_checked_sound. exact Hroots.
Qed.

Lemma infer_fns_env_end2end_in_sound :
  forall env fns f,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked env f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env fns.
  induction fns as [| f0 rest IH]; intros f Hinfer Hin.
  - contradiction.
  - simpl in Hinfer, Hin.
    destruct (infer_fn_env_end2end env f0)
      as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hhead; try discriminate.
    destruct Hin as [Heq | Hin].
    + subst f0.
      exists T0, Γ0, R0_out, roots0. split.
      * exact Hhead.
      * eapply infer_fn_env_end2end_sound. exact Hhead.
    + eapply IH; eauto.
Qed.

Theorem infer_program_env_end2end_sound :
  forall env env' f,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_sound; eauto.
Qed.

Theorem check_program_env_end2end_sound :
  forall env env' f,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_sound; eauto.
Qed.

Lemma infer_fn_env_end2end_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_summary env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end in Hend.
  destruct (infer_full_env_roots_checked env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f)))
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_captured_call_store_safe_summary env f)
    eqn:Hgate; try discriminate.
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_check_env_ready :
  forall env fns,
    infer_fns_env_end2end env fns = infer_ok tt ->
    forallb (check_fn_root_shadow_captured_call_store_safe_summary env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_fn_env_end2end_combined_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  rewrite (infer_fn_env_end2end_gate env f T Γ_out R_out roots Hend).
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_combined_check_env_ready :
  forall env fns,
    infer_fns_env_end2end env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_combined_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_fn_env_end2end_closure_combined_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary.
  rewrite (infer_fn_env_end2end_gate env f T Γ_out R_out roots Hend).
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_closure_combined_check_env_ready :
  forall env fns,
    infer_fns_env_end2end env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_closure_combined_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_fn_env_end2end_exact_closure_combined_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary.
  rewrite (infer_fn_env_end2end_gate env f T Γ_out R_out roots Hend).
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_exact_closure_combined_check_env_ready :
  forall env fns,
    infer_fns_env_end2end env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_exact_closure_combined_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready :
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply env_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - apply check_env_root_shadow_captured_call_store_safe_summary_ready.
    unfold check_env_root_shadow_captured_call_store_safe_summary.
    eapply infer_fns_env_end2end_check_env_ready. exact Hfns.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call env env' f s s' v Hprog
    Hcomponent_check Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_routes.
  - exact Hsynthetic_call_route.
  - exact Hscope_call.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_check :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env env' f s s' v Hprog
    Hcomponent_check Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_body_store_safe_provider.
    exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_store_safe_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider
      env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env env' f s s' v Hprog
    Hbody_summary Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hbody_summary.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_body_store_safe_summary_evidence :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider
      env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hprefix Hframe_scope Hparam_scope Hroot_names Hroot_keys Hpackage
    env env' f s s' v Hprog Hbody_summary Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_store_safe_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_package_narrow_core;
      eauto.
  - exact Hprog.
  - exact Hbody_summary.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider
      env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env env' f s s' v Hprog
    Hbody_summary Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hbody_summary.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_exact_package_and_component_body_summary_at_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_provider env' ->
    component_body_synthetic_direct_call_ready_body_env_evidence_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hpackage env env' f s s' v Hprog Hsummary_at_provider
    Hbody_evidence_provider Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_evidence.
  - exact Hpackage.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hsummary_at_provider.
  - exact Hbody_evidence_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_exact_package_and_component_body_summary_at_in_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_body_env_evidence_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hpackage env env' f s s' v Hprog Hsummary_at_provider
    Hbody_evidence_provider Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_in_evidence.
  - exact Hpackage.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hsummary_at_provider.
  - exact Hbody_evidence_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hsummary_at_provider
    Hnested_summary_provider Hnested_body_provider Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hsummary_at_provider.
  - exact Hnested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_summary_at_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_no_capture_direct_call_component_target_in_provider env' ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hsummary_at_provider
    Htarget_provider Halpha_nested_summary_provider Hnested_body_provider
    Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_summary_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_no_capture_direct_call_component_target_in_provider env' ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hsummary_at_provider
    Htarget_provider Halpha_nested_summary_provider Halpha_nested_body_provider
    Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_nested_evidence_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Halpha_nested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.
Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_in_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_no_capture_direct_call_component_target_in_provider env' ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hsummary_at_provider
    Htarget_provider Halpha_nested_summary_provider Hinitial Hin Hstore Heval.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_summary_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto.
  - unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_summary_provider_and_closure_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    component_body_no_capture_direct_call_component_closure_check_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hprovider
    Hclosure_provider Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - eapply component_body_synthetic_direct_call_ready_summary_at_in_provider_of_provider.
    eapply component_body_synthetic_direct_call_ready_summary_at_provider_of_provider.
    exact Hprovider.
  - eapply component_body_no_capture_direct_call_component_target_in_provider_of_closure_check_provider;
      eassumption.
  - eapply component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider_of_provider.
    exact Hprovider.
  - eapply component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider_of_provider;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.
Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_provider_and_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    component_body_no_capture_direct_call_component_closure_check_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hprovider
    Hclosure_provider Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - eapply component_body_synthetic_direct_call_ready_summary_at_in_provider_of_provider.
    eapply component_body_synthetic_direct_call_ready_summary_at_provider_of_provider.
    exact Hprovider.
  - eapply component_body_no_capture_direct_call_component_target_in_provider_of_closure_check_provider;
      eassumption.
  - eapply component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider_of_provider.
    exact Hprovider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_target_provider :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_no_capture_direct_call_component_closure_check_provider env' ->
    component_body_no_capture_direct_call_component_alpha_nested_target_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hclosure_provider
    Halpha_target_provider Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - eapply component_body_synthetic_direct_call_ready_summary_at_in_provider_of_closure_check_provider;
      eassumption.
  - eapply component_body_no_capture_direct_call_component_target_in_provider_of_closure_check_provider;
      eassumption.
  - eapply component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider_of_alpha_target_provider.
    exact Halpha_target_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_no_capture_direct_call_component_closure_check_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hclosure_provider
    Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
    eapply infer_fns_env_end2end_combined_check_env_ready. exact Hfns.
  - eapply component_body_synthetic_direct_call_ready_summary_at_in_provider_of_closure_check_provider;
      eassumption.
  - eapply component_body_no_capture_direct_call_component_target_in_provider_of_closure_check_provider;
      eassumption.
  - eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider_of_closure_check_provider;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_no_capture_direct_call_component_target_in_provider env' ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hstrict_check
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - exact Hstrict_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_lookup_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_and_exact_closure_provider :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    component_body_no_capture_direct_call_component_exact_closure_check_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hstrict_check
    Hexact_provider Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hstrict_check.
  - eapply component_body_synthetic_direct_call_ready_summary_at_in_provider_of_exact_closure_check_provider;
      eassumption.
  - eapply component_body_no_capture_direct_call_component_target_in_provider_of_exact_closure_check_provider;
      eassumption.
  - eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider_of_exact_closure_check_provider;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_component_body_closure_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body) ->
  (forall env fname fdef fcall used used' fname_body args_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, ECall fname_body args_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_no_capture_direct_call_component_closure_check_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hsummary_body_at_all
    Hexact_body_target env env' f s s' v Hprog Hclosure_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_check.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_synthetic_evidence_at_route;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hclosure_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hprovider Hinitial Hin
    Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
      try discriminate.
    destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
      try discriminate.
    destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
      as [[] | err] eqn:Hfns; try discriminate.
    injection Hprog as <-.
    apply andb_true_iff in Hunique_global as [Hunique_top _].
    eapply infer_program_env_alpha_elab_unique_by_name; eauto. }
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - eapply component_body_synthetic_direct_call_ready_summary_at_in_provider_of_provider.
    eapply component_body_synthetic_direct_call_ready_summary_at_provider_of_provider.
    exact Hprovider.
  - eapply component_body_synthetic_direct_call_ready_nested_summary_at_in_provider_of_provider.
    exact Hprovider.
  - eapply component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider_of_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hprovider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_body_summary_evidence :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider
      env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hprefix Hframe_scope Hparam_scope Hroot_names Hroot_keys Hpackage
    env env' f s s' v Hprog Hbody_summary Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_package_narrow_core;
      eauto.
  - exact Hprog.
  - exact Hbody_summary.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_check :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hprefix Hframe_scope Hparam_scope Hroot_names Hroot_keys Hpackage
    env env' f s s' v Hprog Hcomponent_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_check.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_package_narrow_core;
      eauto.
  - exact Hprog.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.
