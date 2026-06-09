From Facet.TypeSystem Require Import Types Syntax Program RootProvenance TypeChecker EnvRootSoundness EnvRuntimeValidatorFacts EnvRuntimeCapturedCallSummaryFacts EnvRuntimeCapturedSafety.
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

Lemma check_program_env_end2end_infer_ok :
  forall env,
    check_program_env_end2end env = true ->
    exists env', infer_program_env_end2end env = infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end in Hcheck.
  destruct (infer_program_env_end2end env) as [env' | err] eqn:Hprog;
    try discriminate.
  exists env'. reflexivity.
Qed.

Theorem infer_fn_env_end2end_strict_exact_closure_sound :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_strict_exact_closure env f = infer_ok (T, Γ_out, R_out, roots) ->
    checked_fn_env_roots_checked env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end_strict_exact_closure in Hend.
  remember (initial_root_env_for_params (fn_params f ++ fn_captures f))
    as R0 eqn:HR0.
  destruct (infer_full_env_roots_checked env f R0)
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
              env f); try discriminate.
  injection Hend as <- <- <- <-.
  eapply infer_full_env_roots_checked_sound. exact Hroots.
Qed.

Lemma infer_fns_env_end2end_strict_exact_closure_in_sound :
  forall env fns f,
    infer_fns_env_end2end_strict_exact_closure env fns = infer_ok tt ->
    In f fns ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_strict_exact_closure env f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked env f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env fns.
  induction fns as [| f0 rest IH]; intros f Hinfer Hin.
  - contradiction.
  - simpl in Hinfer, Hin.
    destruct (infer_fn_env_end2end_strict_exact_closure env f0)
      as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hhead; try discriminate.
    destruct Hin as [Heq | Hin].
    + subst f0.
      exists T0, Γ0, R0_out, roots0. split.
      * exact Hhead.
      * eapply infer_fn_env_end2end_strict_exact_closure_sound. exact Hhead.
    + eapply IH; eauto.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_sound :
  forall env env' f,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_strict_exact_closure env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_strict_exact_closure env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_strict_exact_closure_in_sound; eauto.
Qed.

Lemma check_program_env_end2end_strict_exact_closure_infer_ok :
  forall env,
    check_program_env_end2end_strict_exact_closure env = true ->
    exists env',
      infer_program_env_end2end_strict_exact_closure env = infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_strict_exact_closure in Hcheck.
  destruct (infer_program_env_end2end_strict_exact_closure env)
    as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_strict_exact_closure_sound :
  forall env env' f,
    check_program_env_end2end_strict_exact_closure env = true ->
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_strict_exact_closure env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_strict_exact_closure_sound; eauto.
Qed.

Theorem check_program_env_end2end_strict_exact_closure_sound_exists :
  forall env,
    check_program_env_end2end_strict_exact_closure env = true ->
    exists env',
      infer_program_env_end2end_strict_exact_closure env = infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_strict_exact_closure env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct (check_program_env_end2end_strict_exact_closure_infer_ok env Hcheck)
    as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_strict_exact_closure_sound; eauto.
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

Lemma infer_fn_env_end2end_strict_exact_closure_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_strict_exact_closure env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end_strict_exact_closure in Hend.
  destruct (infer_full_env_roots_checked env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f)))
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
              env f) eqn:Hgate; try discriminate.
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_strict_exact_closure_check_env_ready :
  forall env fns,
    infer_fns_env_end2end_strict_exact_closure env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end_strict_exact_closure env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_strict_exact_closure_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_fn_env_end2end_strict_exact_closure_combined_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_strict_exact_closure env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  pose proof
    (infer_fn_env_end2end_strict_exact_closure_gate
      env f T Γ_out R_out roots Hend) as Hstrict.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  unfold check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
    in Hstrict.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
              env f) eqn:Hcomponent.
  - rewrite orb_true_r. reflexivity.
  - rewrite orb_false_r. exact Hstrict.
Qed.

Lemma infer_fns_env_end2end_strict_exact_closure_combined_check_env_ready :
  forall env fns,
    infer_fns_env_end2end_strict_exact_closure env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end_strict_exact_closure env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_strict_exact_closure_combined_gate.
      exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_program_env_end2end_unique_by_name :
  forall env env',
    infer_program_env_end2end env = infer_ok env' ->
    fn_env_unique_by_name env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  apply andb_true_iff in Hunique_global as [Hunique_top _].
  eapply infer_program_env_alpha_elab_unique_by_name; eauto.
Qed.

Lemma infer_program_env_end2end_check_env_ready :
  forall env env',
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_captured_call_store_safe_summary env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_captured_call_store_safe_summary.
  eapply infer_fns_env_end2end_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_combined_check_env_ready :
  forall env env',
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  eapply infer_fns_env_end2end_combined_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_unique_by_name :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    fn_env_unique_by_name env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_strict_exact_closure env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  apply andb_true_iff in Hunique_global as [Hunique_top _].
  eapply infer_program_env_alpha_elab_unique_by_name; eauto.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_check_env_ready :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_strict_exact_closure env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary.
  eapply infer_fns_env_end2end_strict_exact_closure_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_combined_check_env_ready :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_strict_exact_closure env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  eapply infer_fns_env_end2end_strict_exact_closure_combined_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_check_when_not_captured :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_captured_call_store_safe_summary env' f_component = false ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcaptured.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_check_when_not_captured.
  - eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hin.
  - exact Hcaptured.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_ready_when_not_captured :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_captured_call_store_safe_summary env' f_component = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcaptured.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready_when_not_captured.
  - eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hin.
  - exact Hcaptured.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_ready :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready.
  - eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hin.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_summary_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    fn_env_unique_by_name env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fdef.
Proof.
  intros env env' base env0 fdef _Hprog Hunique Hbase Henv Hin
    Hcomponent_check.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  change (env_fns
    (global_env_with_local_bounds
      (global_env_with_local_bounds env' bounds_base) bounds))
    with (env_fns env') in Hin.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
  - eapply fn_env_unique_by_name_global_env_with_local_bounds.
    exact Hunique.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
    + exact Hunique.
    + eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_exact_closure_check_in_provider :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    component_body_no_capture_direct_call_component_exact_closure_check_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_no_capture_direct_call_component_exact_closure_check_in_provider_of_strict_exact_closure_check.
  eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_exact_body_target_in_provider :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    component_body_no_capture_direct_call_component_exact_body_target_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_no_capture_direct_call_component_exact_body_target_in_provider_of_strict_exact_closure_check.
  eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_exact_body_target_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  change (env_fns
    (global_env_with_local_bounds
      (global_env_with_local_bounds env' bounds_base) bounds))
    with (env_fns env') in Hin.
  eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_global_env_with_local_bounds.
  eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_global_env_with_local_bounds.
  eapply infer_program_env_end2end_strict_exact_closure_exact_body_target_in_provider;
    eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_target_check_in_provider :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    component_body_no_capture_direct_call_component_target_check_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_no_capture_direct_call_component_target_check_in_provider_of_exact_closure_check_in_provider.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_strict_exact_closure_exact_closure_check_in_provider.
    exact Hprog.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_summary_at_check_in_provider :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_check_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_synthetic_direct_call_ready_summary_at_check_in_provider_of_target_check_in_provider.
  eapply infer_program_env_end2end_strict_exact_closure_target_check_in_provider.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_route_summary_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_strict_exact_closure_component_summary_in_local_bounds_family.
    + exact Hprog.
    + eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
      exact Hprog.
    + exact Hbase.
    + exact Henv.
    + exact Hin.
    + exact Hcomponent_check.
  - intros fcall used used' fname_body args_body synthetic_body Hrename Htarget.
    destruct Hbase as (bounds_base & ->).
    destruct Henv as (bounds & ->).
    change (env_fns
      (global_env_with_local_bounds
        (global_env_with_local_bounds env' bounds_base) bounds))
      with (env_fns env') in Hin.
    destruct (direct_call_target_expr_alpha_rename_fn_def_inv
                used fdef fcall used' fname_body args_body synthetic_body
                Hrename Htarget) as (args0 & Htarget_original).
    pose proof (alpha_rename_fn_def_bounds used fdef fcall used' Hrename)
      as Hbounds.
    rewrite Hbounds.
    change (fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      (global_env_with_local_bounds env' (fn_bounds fdef)) fname_body).
    eapply infer_program_env_end2end_strict_exact_closure_summary_at_check_in_provider;
      eassumption.
Qed.


Lemma infer_program_env_end2end_strict_exact_closure_exact_body_route_scoped_package_local_bounds_family :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
      (fun env0 fdef =>
        global_env_local_bounds_family env' env0 /\
          In fdef (env_fns env') /\
          check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
            env' fdef = true).
Proof.
  intros env env' Hprog.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_summary_at_check_provider_local_bounds_family.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_strict_exact_closure_summary_at_check_in_provider.
    exact Hprog.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_exact_body_route_scoped_package_local_bounds_family_with_route_summary :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
      (fun env0 fdef =>
        global_env_local_bounds_family env' env0 /\
          In fdef (env_fns env0) /\
          check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
            env' fdef = true).
Proof.
  intros env env' Hprog.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_route_summary_at_provider.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body (Hfamily & Hin & Hcomponent_check) _Hin Hname
      Hrename Htarget.
    destruct (infer_program_env_end2end_strict_exact_closure_component_route_summary_in_local_bounds_family
                env env' env' env0 fdef Hprog
                (global_env_local_bounds_family_base env') Hfamily Hin
                Hcomponent_check) as [_ Hroute_summary].
    eapply Hroute_summary; eassumption.
  - intros env0 fdef (Hfamily & Hin & Hcomponent_check).
    eapply infer_program_env_end2end_strict_exact_closure_component_summary_in_local_bounds_family.
    + exact Hprog.
    + eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
      exact Hprog.
    + apply global_env_local_bounds_family_base.
    + exact Hfamily.
    + exact Hin.
    + exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_seen_component_check_in_local_bounds_family :
  forall env env' base env0 fdef fuel seen,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
      fuel seen env' fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true.
Proof.
  intros env env' base env0 fdef fuel seen _Hprog _Hbase _Henv Hseen
    Hnot_seen.
  eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check;
    eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_callee_seen_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn_b fname (env_fns env') = Some fcallee ->
    exists fuel',
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
        fuel' [fn_name f_component] env' fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    _Hprog _Hbase _Henv Hexact Htarget Hlookup.
  eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_callee_seen;
    eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fdef,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hcomponent_check_provider.
  destruct Hbase as (bounds_base & ->).
  eapply (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys (global_env_with_local_bounds env' bounds_base)
    (fun env0 fdef =>
      global_env_local_bounds_family env' env0 /\
        In fdef (env_fns env0) /\
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' fdef = true)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
    + eapply infer_program_env_end2end_strict_exact_closure_exact_body_target_in_local_bounds_family.
      * exact Hprog.
      * exists bounds_base. reflexivity.
      * exact Hfamily.
      * exact Hin.
      * eapply Hcomponent_check_provider; eassumption.
    + exact Hrename.
    + exact Htarget.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    split.
    + eapply global_env_local_bounds_family_of_local_bounds_base.
      exact Hfamily.
    + split.
      * exact Hin.
      * eapply Hcomponent_check_provider; eassumption.
  - eapply infer_program_env_end2end_strict_exact_closure_exact_body_route_scoped_package_local_bounds_family_with_route_summary.
    exact Hprog.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_exact_body_route_scoped_package_check_in_provider :
  forall env env',
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider
      env'
      (fun env0 fdef =>
        env0 = env' /\
        In fdef (env_fns env') /\
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' fdef = true).
Proof.
  intros env env' Hprog.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_summary_at_check_provider.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_strict_exact_closure_summary_at_check_in_provider.
    exact Hprog.
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
  eapply env_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - apply check_env_root_shadow_captured_call_store_safe_summary_ready.
    eapply infer_program_env_end2end_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_routes.
  - exact Hsynthetic_call_route.
  - exact Hscope_call.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_evidence.
  - exact Hpackage.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_in_evidence.
  - exact Hpackage.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
  - exact Hsummary_at_provider.
  - exact Hnested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider env' ->
    component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hsummary_at_provider
    Hnested_summary_provider Hnested_body_provider Hnested2_summary_provider
    Hnested2_body_provider Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_summary_at.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
  - exact Hsummary_at_provider.
  - exact Hnested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hnested2_summary_provider.
  - exact Hnested2_body_provider.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_summary_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_nested_evidence_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_summary_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply infer_program_env_end2end_combined_check_env_ready.
    exact Hprog.
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
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


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
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
    Hroot_names Hroot_keys Hstatic env env' f s s' v Hprog Hstrict_check
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
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


Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check :
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
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hstrict_check Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - exact Hstrict_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env env' f s s' v Hprog Hstrict_check Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hunique.
  - exact Hstrict_check.
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
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


Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
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
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hstore_safe_route Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hexact_body_target Hbody_package
    env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package :
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
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  forall component_ready,
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    component_ready env fdef) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    component_ready ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hexact_body_target component_ready Hcomponent_provider
    Hscoped_package env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall component_ready,
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    component_ready env fdef) ->
  (forall env fdef,
    component_ready env fdef ->
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env fdef) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    component_ready ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys component_ready Hcomponent_provider Htarget_provider
    Hscoped_package env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hin0 Hname Hrename Htarget.
    eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
    + eapply Htarget_provider.
      eapply Hcomponent_provider; eassumption.
    + exact Hrename.
    + exact Htarget.
  - exact Hcomponent_provider.
  - exact Hscoped_package.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_check_route_package :
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
    fn_env_unique_by_name env /\
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef = true) ->
  (forall env,
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env = true) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_check_provider Hstrict_provider env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply (infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys
    (fun env fdef =>
      fn_env_unique_by_name env /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env fdef = true)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hin0 Hname Hrename Htarget.
    destruct (Hcomponent_check_provider env0 fname fdef fcall used used'
      fname_body args_body synthetic_body Hin0 Hname Hrename Htarget)
      as [Hunique Hcomponent_check].
    destruct (check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready
                env0 fdef (Hstrict_provider env0) Hin0 Hcomponent_check)
      as [Hcomponent Hexact].
    split; [exact Hunique |].
    split; [exact Hcomponent | exact Hexact].
  - intros env0 fdef (_Hunique & _Hcomponent & Hexact).
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env0 fdef Hexact) as [_ Hexact_target].
    exact Hexact_target.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_non_captured_route_package :
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
    fn_env_unique_by_name env /\
    check_fn_root_shadow_captured_call_store_safe_summary env fdef = false) ->
  (forall env,
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env = true) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hnon_captured_provider Hstrict_provider env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_check_route_package.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hin0 Hname Hrename Htarget.
    destruct (Hnon_captured_provider env0 fname fdef fcall used used'
      fname_body args_body synthetic_body Hin0 Hname Hrename Htarget)
      as [Hunique Hcaptured].
    split.
    + exact Hunique.
    + eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_check_when_not_captured.
      * exact (Hstrict_provider env0).
      * exact Hin0.
      * exact Hcaptured.
  - exact Hstrict_provider.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_ready_route_package :
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
    fn_env_unique_by_name env /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env fdef = true) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_provider env env' f s s' v Hprog Hinitial Hin
    Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hcomponent_provider.
  - intros env0 fdef (_Hunique & _Hcomponent & Hexact).
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env0 fdef Hexact) as [_ Hexact_target].
    exact Hexact_target.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_body_target_provider :
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
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env fdef) ->
  (forall env, component_body_no_capture_direct_call_component_exact_body_target_provider env) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_provider Htarget_provider env env' f s s' v Hprog
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hcomponent_provider.
  - intros env0 fdef Hready.
    destruct Hready as [Hcomponent _Hsummary].
    eapply Htarget_provider. exact Hcomponent.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_closure_provider :
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
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env fdef) ->
  (forall env, component_body_no_capture_direct_call_component_exact_closure_check_provider env) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_provider Hexact_closure_provider env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_body_target_provider.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hcomponent_provider.
  - intros env0.
    eapply component_body_no_capture_direct_call_component_exact_body_target_provider_of_exact_closure_check_provider.
    exact (Hexact_closure_provider env0).
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package :
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
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env fdef) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hexact_body_target Hcomponent_provider env env' f s s' v Hprog
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hexact_body_target.
  - exact Hcomponent_provider.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route :
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
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hsummary_body_at_all
    Hexact_body_target env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_synthetic_evidence_at_route;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_branch_local_strict_exact_closure_check :
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
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hsummary_body_at_all
    Hexact_body_target env env' f s s' v Hprog Hstrict_check Hinitial Hin
    Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_synthetic_evidence_at_route;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hstrict_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  forall component_ready,
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    component_ready env fdef) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    component_ready ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hexact_body_target component_ready
    Hcomponent_provider Hscoped_package env env' f s s' v Hprog
    Hstrict_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_branch_local_strict_exact_closure_check.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height;
      eassumption.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hin0 Hname Hrename Htarget.
    pose proof
      (Hexact_body_target env0 fname fdef fcall used used' fname_body
        args_body synthetic_body Hin0 Hname Hrename Htarget) as Htarget_exact.
    pose proof
      (direct_call_target_expr_same_is_call (fn_body fcall) fname_body
        args_body Htarget_exact) as Hbody_exact.
    pose proof
      (Hcomponent_provider env0 fname fdef fcall used used' fname_body
        args_body synthetic_body Hin0 Hname Hrename Htarget) as Hcomponent.
    destruct (Hscoped_package env0 fname fdef fcall used used' fname_body
      args_body Hcomponent Hin0 Hname Hrename) as [Hsummary _].
    { rewrite Hbody_exact. reflexivity. }
    exact Hsummary.
  - intros env0 fname fdef fcall used used' fname_body args_body Hin0
      Hname Hrename Htarget.
    eapply Hexact_body_target; eassumption.
  - exact Hprog.
  - exact Hstrict_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  forall component_ready,
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    component_ready env fdef) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    component_ready ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hexact_body_target component_ready
    Hcomponent_provider Hscoped_package env env' f s s' v Hprog
    Hstrict_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hprog.
  - exact Hstrict_check.
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
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
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

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
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
  intros Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hprovider Hinitial Hin
    Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_summary_at.
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
  - eapply component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider_of_provider.
    exact Hprovider.
  - eapply component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider_of_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hprovider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hprovider Hinitial Hin
    Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog. }
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_summary_at.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply infer_program_env_end2end_strict_exact_closure_combined_check_env_ready.
    exact Hprog.
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
  - eapply component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider_of_provider.
    exact Hprovider.
  - eapply component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider_of_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hprovider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready Hexact_body_target Hbody_package
    env env' f s s' v Hprog Hprovider Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_evidence_at;
      try eassumption.
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_no_scope;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package;
      eassumption.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hprovider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready Hexact_body_target Hbody_package
    env env' f s s' v Hprog Hcomponent_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hexact_body_target.
  - exact Hbody_package.
  - exact Hprog.
  - eapply component_body_synthetic_direct_call_ready_summary_provider_of_store_safe.
    eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_body_store_safe_provider.
    exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready Hexact_body_target Hbody_package
    env env' f s s' v Hprog Hprovider Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_evidence_at;
      try eassumption.
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_no_scope;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package;
      eassumption.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hprovider.
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
