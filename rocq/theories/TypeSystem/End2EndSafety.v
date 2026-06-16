From Facet.TypeSystem Require Import Types Syntax Program RootProvenance TypeChecker EnvRootSoundness AssocEnvCallStructuralBoundary EnvRuntimeValidatorFacts EnvRuntimeCapturedCallSummaryFacts EnvRuntimeCapturedSafety.
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
  destruct (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
              env f);
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

Theorem infer_program_env_end2end_ordinary_sound :
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

Theorem check_program_env_end2end_ordinary_sound :
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
  eapply infer_program_env_end2end_ordinary_sound; eauto.
Qed.

Theorem infer_fn_env_end2end_assoc_sound :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_assoc env f = infer_ok (T, Γ_out, R_out, roots) ->
    checked_fn_env_roots_checked_assoc_boundary env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Γ_out R_out roots Hend.
  eapply infer_fn_env_end2end_assoc_entry_boundary_sound. exact Hend.
Qed.

Lemma infer_fns_env_end2end_assoc_in_sound :
  forall env fns f,
    infer_fns_env_end2end_assoc env fns = infer_ok tt ->
    In f fns ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env fns f Hinfer Hin.
  eapply infer_fns_env_end2end_assoc_in_boundary_sound; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_sound :
  forall env env' f,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  eapply infer_program_env_end2end_assoc_entry_boundary_sound; eauto.
Qed.

Theorem check_program_env_end2end_assoc_sound :
  forall env env' f,
    check_program_env_end2end_assoc env = true ->
    infer_program_env_end2end_assoc env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_sound; eauto.
Qed.

Lemma check_program_env_end2end_assoc_infer_ok :
  forall env,
    check_program_env_end2end_assoc env = true ->
    exists env', infer_program_env_end2end_assoc env = infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc in Hcheck.
  destruct (infer_program_env_end2end_assoc env) as [env' | err] eqn:Hprog;
    try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_sound_exists :
  forall env,
    check_program_env_end2end_assoc env = true ->
    exists env',
      infer_program_env_end2end_assoc env = infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct (check_program_env_end2end_assoc_infer_ok env Hcheck)
    as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_sound; eauto.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_base :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    infer_program_env_end2end_assoc env = infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_mixed in Hprog.
  destruct (infer_program_env_end2end_assoc env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked);
    try discriminate.
  injection Hprog as <-.
  reflexivity.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  eapply infer_program_env_end2end_assoc_sound; eauto.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
  exact Hprog.
Qed.

Lemma check_program_env_end2end_assoc_direct_receiver_mixed_infer_ok :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_mixed env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_mixed env =
        infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_direct_receiver_mixed in Hcheck.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed env)
    as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_mixed_sound :
  forall env env' f,
    check_program_env_end2end_assoc_direct_receiver_mixed env = true ->
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_sound; eauto.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_mixed_sound_exists :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_mixed env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_mixed env =
        infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_direct_receiver_mixed_infer_ok
       env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_sound;
    eauto.
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



Theorem infer_fn_env_end2end_assoc_strict_exact_closure_sound :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_assoc_strict_exact_closure env f =
      infer_ok (T, Γ_out, R_out, roots) ->
    checked_fn_env_roots_checked_assoc_boundary env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end_assoc_strict_exact_closure in Hend.
  remember (initial_root_env_for_params (fn_params f ++ fn_captures f))
    as R0 eqn:HR0.
  destruct (infer_full_env_roots_checked_assoc env f R0)
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
              env f); try discriminate.
  injection Hend as <- <- <- <-.
  subst R0.
  eapply infer_full_env_roots_checked_assoc_entry_boundary_sound.
  exact Hroots.
Qed.

Lemma infer_fns_env_end2end_assoc_strict_exact_closure_in_sound :
  forall env fns f,
    infer_fns_env_end2end_assoc_strict_exact_closure env fns = infer_ok tt ->
    In f fns ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env fns.
  induction fns as [| f0 rest IH]; intros f Hinfer Hin.
  - contradiction.
  - simpl in Hinfer, Hin.
    destruct (infer_fn_env_end2end_assoc_strict_exact_closure env f0)
      as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hhead; try discriminate.
    destruct Hin as [Heq | Hin].
    + subst f0.
      exists T0, Γ0, R0_out, roots0. split.
      * exact Hhead.
      * eapply infer_fn_env_end2end_assoc_strict_exact_closure_sound.
        exact Hhead.
    + eapply IH; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end_assoc_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc_strict_exact_closure
              env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_assoc_strict_exact_closure_in_sound; eauto.
Qed.

Lemma check_program_env_end2end_assoc_strict_exact_closure_infer_ok :
  forall env,
    check_program_env_end2end_assoc_strict_exact_closure env = true ->
    exists env',
      infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_strict_exact_closure in Hcheck.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_strict_exact_closure_sound :
  forall env env' f,
    check_program_env_end2end_assoc_strict_exact_closure env = true ->
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_sound; eauto.
Qed.

Theorem check_program_env_end2end_assoc_strict_exact_closure_sound_exists :
  forall env,
    check_program_env_end2end_assoc_strict_exact_closure env = true ->
    exists env',
      infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc_strict_exact_closure env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct (check_program_env_end2end_assoc_strict_exact_closure_infer_ok
              env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_sound; eauto.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hassoc; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked);
    try discriminate.
  injection Hprog as <-.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_sound; eauto.
Qed.

Lemma check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_infer_ok :
  forall env,
    check_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
      true ->
    exists env',
      infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
        infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_strict_exact_closure_direct_receiver
    in Hcheck.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
              env) as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_sound :
  forall env env' f,
    check_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
      true ->
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_sound;
    eauto.
Qed.

Theorem check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_sound_exists :
  forall env,
    check_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
      true ->
    exists env',
      infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver env =
        infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc_strict_exact_closure env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_infer_ok
       env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_sound;
    eauto.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hassoc; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked);
    try discriminate.
  injection Hprog as <-.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_sound; eauto.
Qed.

Lemma check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_infer_ok :
  forall env,
    check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = true ->
    exists env',
      infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
        env = infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
    in Hcheck.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
              env) as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_sound :
  forall env env' f,
    check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = true ->
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_strict_exact_closure env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_sound;
    eauto.
Qed.

Theorem check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_sound_exists :
  forall env,
    check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = true ->
    exists env',
      infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
        env = infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc_strict_exact_closure env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_infer_ok
       env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_sound;
    eauto.
Qed.

Theorem infer_program_env_end2end_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_sound.
Qed.

Theorem check_program_env_end2end_sound :
  forall env env' f,
    check_program_env_end2end_assoc_direct_receiver_mixed env = true ->
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  eapply check_program_env_end2end_assoc_direct_receiver_mixed_sound.
Qed.


Lemma infer_fn_env_end2end_assoc_strict_exact_closure_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_assoc_strict_exact_closure env f =
      infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end_assoc_strict_exact_closure in Hend.
  destruct (infer_full_env_roots_checked_assoc env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f)))
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
              env f) eqn:Hgate; try discriminate.
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_assoc_strict_exact_closure_check_env_ready :
  forall env fns,
    infer_fns_env_end2end_assoc_strict_exact_closure env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end_assoc_strict_exact_closure env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_assoc_strict_exact_closure_gate.
      exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_fn_env_end2end_assoc_strict_exact_closure_combined_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_assoc_strict_exact_closure env f =
      infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  pose proof
    (infer_fn_env_end2end_assoc_strict_exact_closure_gate
      env f T Γ_out R_out roots Hend) as Hstrict.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  unfold check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
    in Hstrict.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
              env f) eqn:Hcomponent.
  - rewrite orb_true_r. reflexivity.
  - rewrite orb_false_r. exact Hstrict.
Qed.

Lemma infer_fns_env_end2end_assoc_strict_exact_closure_combined_check_env_ready :
  forall env fns,
    infer_fns_env_end2end_assoc_strict_exact_closure env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end_assoc_strict_exact_closure env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_assoc_strict_exact_closure_combined_gate.
      exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    fn_env_unique_by_name env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc_strict_exact_closure
              env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  apply andb_true_iff in Hunique_global as [Hunique_top _].
  eapply infer_program_env_alpha_elab_unique_by_name; eauto.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc_strict_exact_closure
              env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary.
  eapply infer_fns_env_end2end_assoc_strict_exact_closure_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_combined_check_env_ready :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_strict_exact_closure in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc_strict_exact_closure
              env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  eapply infer_fns_env_end2end_assoc_strict_exact_closure_combined_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_fn_env_end2end_assoc_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_assoc env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end_assoc in Hend.
  destruct (infer_full_env_roots_checked_assoc env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f)))
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
              env f) eqn:Hgate; try discriminate.
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_assoc_check_env_ready :
  forall env fns,
    infer_fns_env_end2end_assoc env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end_assoc env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_assoc_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_fn_env_end2end_assoc_combined_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end_assoc env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  pose proof (infer_fn_env_end2end_assoc_gate env f T Γ_out R_out roots Hend)
    as Hexact.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hexact.
  apply orb_true_iff in Hexact as [Hcaptured | Hexact].
  - rewrite Hcaptured. reflexivity.
  - assert (Hcomponent :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f = true).
    { unfold check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        in Hexact.
      eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check;
        try exact Hexact.
      reflexivity. }
    rewrite Hcomponent. rewrite orb_true_r. reflexivity.
Qed.

Lemma infer_fns_env_end2end_assoc_combined_check_env_ready :
  forall env fns,
    infer_fns_env_end2end_assoc env fns = infer_ok tt ->
    forallb
      (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env) fns = true.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros Hinfer; simpl in *.
  - reflexivity.
  - destruct (infer_fn_env_end2end_assoc env f)
      as [[[[T Γ] R] roots] | err] eqn:Hhead; try discriminate.
    apply andb_true_iff. split.
    + eapply infer_fn_env_end2end_assoc_combined_gate. exact Hhead.
    + eapply IH. exact Hinfer.
Qed.

Lemma infer_program_env_end2end_assoc_unique_by_name :
  forall env env',
    infer_program_env_end2end_assoc env = infer_ok env' ->
    fn_env_unique_by_name env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  apply andb_true_iff in Hunique_global as [Hunique_top _].
  eapply infer_program_env_alpha_elab_unique_by_name; eauto.
Qed.

Lemma infer_program_env_end2end_assoc_check_env_ready :
  forall env env',
    infer_program_env_end2end_assoc env = infer_ok env' ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary.
  eapply infer_fns_env_end2end_assoc_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_assoc_combined_check_env_ready :
  forall env env',
    infer_program_env_end2end_assoc env = infer_ok env' ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique_global;
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end_assoc env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  injection Hprog as <-.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  eapply infer_fns_env_end2end_assoc_combined_check_env_ready.
  exact Hfns.
Qed.

Lemma infer_program_env_end2end_assoc_component_ready_when_not_captured :
  forall env env' f_component,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_captured_call_store_safe_summary env' f_component = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcaptured.
  pose proof (infer_program_env_end2end_assoc_check_env_ready
                env env' Hprog) as Hcheck.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck.
  apply forallb_forall with (x := f_component) in Hcheck; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck.
  rewrite Hcaptured in Hcheck.
  split.
  - destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f_component Hcheck) as [Hcomponent _].
    exact Hcomponent.
  - exact Hcheck.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_ready_when_not_captured :
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_captured_call_store_safe_summary env' f_component = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcaptured.
  eapply infer_program_env_end2end_assoc_component_ready_when_not_captured.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hin.
  - exact Hcaptured.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_exact_closure_when_not_captured :
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_captured_call_store_safe_summary env' f_component = false ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcaptured.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_component_ready_when_not_captured
              env env' f_component Hprog Hin Hcaptured) as [_ Hexact].
  exact Hexact.
Qed.

Lemma infer_fn_env_end2end_gate :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env f = true.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end in Hend.
  destruct (infer_full_env_roots_checked env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f)))
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
              env f) eqn:Hgate; try discriminate.
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_check_env_ready :
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
  pose proof (infer_fn_env_end2end_gate env f T Γ_out R_out roots Hend)
    as Hexact.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hexact.
  apply orb_true_iff in Hexact as [Hcaptured | Hexact].
  - rewrite Hcaptured. reflexivity.
  - assert (Hcomponent :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f = true).
    { unfold check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        in Hexact.
      eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check;
        try exact Hexact.
      reflexivity. }
    rewrite Hcomponent. rewrite orb_true_r. reflexivity.
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
  pose proof (infer_fn_env_end2end_gate env f T Γ_out R_out roots Hend)
    as Hexact.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hexact.
  apply orb_true_iff in Hexact as [Hcaptured | Hexact].
  - rewrite Hcaptured. reflexivity.
  - pose proof
      (check_fn_root_shadow_no_capture_direct_call_component_closure_of_exact_closure
        env f Hexact) as Hclosure.
    rewrite Hclosure. rewrite orb_true_r. reflexivity.
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
  exact (infer_fn_env_end2end_gate env f T Γ_out R_out roots Hend).
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
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
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
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary.
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

Lemma infer_program_env_end2end_strict_exact_closure_component_exact_closure :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  destruct (infer_program_env_end2end_strict_exact_closure_component_ready
              env env' f_component Hprog Hin Hcomponent_check)
    as [_ Hexact].
  exact Hexact.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_unique_by_name_in_local_bounds_family :
  forall env env' base env0,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    fn_env_unique_by_name env0.
Proof.
  intros env env' base env0 Hprog Hbase Henv.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  eapply fn_env_unique_by_name_global_env_with_local_bounds.
  eapply fn_env_unique_by_name_global_env_with_local_bounds.
  eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
  exact Hprog.
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

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_ready_when_not_captured :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_captured_call_store_safe_summary env' f_component = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcaptured.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready_when_not_captured.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hin.
  - exact Hcaptured.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_ready :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hin.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_component_ready
              env env' f_component Hprog Hin Hcomponent_check)
    as [_ Hexact].
  exact Hexact.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name_in_local_bounds_family :
  forall env env' base env0,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    fn_env_unique_by_name env0.
Proof.
  intros env env' base env0 Hprog Hbase Henv.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  eapply fn_env_unique_by_name_global_env_with_local_bounds.
  eapply fn_env_unique_by_name_global_env_with_local_bounds.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_unique_by_name_in_local_bounds_family :
  forall env env' base env0,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    fn_env_unique_by_name env0.
Proof.
  intros env env' base env0 Hprog Hbase Henv.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  eapply fn_env_unique_by_name_global_env_with_local_bounds.
  eapply fn_env_unique_by_name_global_env_with_local_bounds.
  eapply infer_program_env_end2end_assoc_unique_by_name.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_exact_closure_check_in_provider :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    component_body_no_capture_direct_call_component_exact_closure_check_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_no_capture_direct_call_component_exact_closure_check_in_provider_of_strict_exact_closure_check.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_exact_body_target_in_provider :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    component_body_no_capture_direct_call_component_exact_body_target_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_no_capture_direct_call_component_exact_body_target_in_provider_of_strict_exact_closure_check.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
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

Lemma infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fdef /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fdef = true.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name_in_local_bounds_family;
      eassumption.
  - split.
    + eapply infer_program_env_end2end_strict_exact_closure_component_summary_in_local_bounds_family.
      * exact Hprog.
      * eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
        exact Hprog.
      * exact Hbase.
      * exact Henv.
      * exact Hin.
      * exact Hcomponent_check.
    + destruct Hbase as (bounds_base & ->).
      destruct Henv as (bounds & ->).
      change (env_fns
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' bounds_base) bounds))
        with (env_fns env') in Hin.
      rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      eapply infer_program_env_end2end_strict_exact_closure_component_exact_closure.
      * exact Hprog.
      * exact Hin.
      * exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_summary_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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

Lemma infer_program_env_end2end_assoc_strict_exact_closure_exact_body_target_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_strict_exact_closure_exact_body_target_in_provider;
    eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_exact_body_route_package_at_of_component_check_in_local_bounds_family :
  forall env env' base env0 fname fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    fn_name fdef = fname ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env0 fname.
Proof.
  intros env env' base env0 fname fdef Hprog Hbase Henv Hin Hname
    Hcomponent_check fdef0 fcall used used' fname_body args_body Hin0 Hname0
    Hrename Htarget.
  assert (Hunique : fn_env_unique_by_name env0).
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name_in_local_bounds_family;
      eassumption. }
  assert (Heq : fdef0 = fdef).
  { eapply Hunique; try eassumption.
    rewrite Hname0. exact (eq_sym Hname). }
  subst fdef0.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
    try eassumption.
  split; [exact Hunique |].
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family
      env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check)
    as [_ Hpayload].
  exact Hpayload.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fdef /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fdef = true.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name_in_local_bounds_family;
      eassumption.
  - split.
    + eapply infer_program_env_end2end_assoc_strict_exact_closure_component_summary_in_local_bounds_family.
      * exact Hprog.
      * eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
        exact Hprog.
      * exact Hbase.
      * exact Henv.
      * exact Hin.
      * exact Hcomponent_check.
    + destruct Hbase as (bounds_base & ->).
      destruct Henv as (bounds & ->).
      change (env_fns
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' bounds_base) bounds))
        with (env_fns env') in Hin.
      rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      eapply infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure.
      * exact Hprog.
      * exact Hin.
      * exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_when_not_captured :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_captured_call_store_safe_summary
      env' fdef = false ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fdef /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fdef = true.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcaptured
    _Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_assoc_unique_by_name_in_local_bounds_family;
      eassumption.
  - destruct Hbase as (bounds_base & ->).
    destruct Henv as (bounds & ->).
    change (env_fns
      (global_env_with_local_bounds
        (global_env_with_local_bounds env' bounds_base) bounds))
      with (env_fns env') in Hin.
    destruct (infer_program_env_end2end_assoc_component_ready_when_not_captured
                env env' fdef Hprog Hin Hcaptured)
      as [Hcomponent Hexact].
    split.
    + eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
      * eapply fn_env_unique_by_name_global_env_with_local_bounds.
        eapply infer_program_env_end2end_assoc_unique_by_name.
        exact Hprog.
      * eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
        -- eapply infer_program_env_end2end_assoc_unique_by_name.
           exact Hprog.
        -- exact Hcomponent.
    + rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      exact Hexact.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_ready_payload_in_local_bounds_family_when_not_captured :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc_direct_receiver_mixed env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_captured_call_store_safe_summary
      env' fdef = false ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fdef /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fdef = true.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcaptured
    Hcomponent_check.
  eapply infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_when_not_captured.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin.
  - exact Hcaptured.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_of_exact_closure :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' fdef = true ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fdef /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fdef = true.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hexact.
  split.
  - eapply infer_program_env_end2end_assoc_unique_by_name_in_local_bounds_family;
      eassumption.
  - destruct Hbase as (bounds_base & ->).
    destruct Henv as (bounds & ->).
    change (env_fns
      (global_env_with_local_bounds
        (global_env_with_local_bounds env' bounds_base) bounds))
      with (env_fns env') in Hin.
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' fdef Hexact) as [Hcomponent _Hexact_target].
    split.
    + eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
      * eapply fn_env_unique_by_name_global_env_with_local_bounds.
        eapply infer_program_env_end2end_assoc_unique_by_name.
        exact Hprog.
      * eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
        -- eapply infer_program_env_end2end_assoc_unique_by_name.
           exact Hprog.
        -- exact Hcomponent.
    + rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      rewrite check_fn_root_shadow_no_capture_direct_call_component_exact_closure_global_env_with_local_bounds.
      exact Hexact.
Qed.

Lemma infer_program_env_end2end_assoc_exact_body_route_package_at_of_exact_closure_in_local_bounds_family :
  forall env env' base env0 fname fdef,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    fn_name fdef = fname ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' fdef = true ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env0 fname.
Proof.
  intros env env' base env0 fname fdef Hprog Hbase Henv Hin Hname
    Hexact fdef0 fcall used used' fname_body args_body Hin0 Hname0
    Hrename Htarget.
  assert (Hunique : fn_env_unique_by_name env0).
  { eapply infer_program_env_end2end_assoc_unique_by_name_in_local_bounds_family;
      eassumption. }
  assert (Heq : fdef0 = fdef).
  { eapply Hunique; try eassumption.
    rewrite Hname0. exact (eq_sym Hname). }
  subst fdef0.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
    try eassumption.
  destruct
    (infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_of_exact_closure
      env env' base env0 fdef Hprog Hbase Henv Hin Hexact)
    as [Hunique0 Hpayload].
  split; [exact Hunique0 | exact Hpayload].
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_exact_body_route_package_at_of_component_check_in_local_bounds_family :
  forall env env' base env0 fname fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    fn_name fdef = fname ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env0 fname.
Proof.
  intros env env' base env0 fname fdef Hprog Hbase Henv Hin Hname
    Hcomponent_check fdef0 fcall used used' fname_body args_body Hin0 Hname0
    Hrename Htarget.
  assert (Hunique : fn_env_unique_by_name env0).
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name_in_local_bounds_family;
      eassumption. }
  assert (Heq : fdef0 = fdef).
  { eapply Hunique; try eassumption.
    rewrite Hname0. exact (eq_sym Hname). }
  subst fdef0.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
    try eassumption.
  split; [exact Hunique |].
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family
      env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check)
    as [_ Hpayload].
  exact Hpayload.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_target_check_in_provider :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    component_body_no_capture_direct_call_component_target_check_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_no_capture_direct_call_component_target_check_in_provider_of_exact_closure_check_in_provider.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_exact_closure_check_in_provider.
    exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_summary_at_check_in_provider :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_at_check_in_provider
      env'.
Proof.
  intros env env' Hprog.
  eapply component_body_synthetic_direct_call_ready_summary_at_check_in_provider_of_target_check_in_provider.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_target_check_in_provider.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_route_summary_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_summary_in_local_bounds_family.
    + exact Hprog.
    + eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
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
    eapply infer_program_env_end2end_assoc_strict_exact_closure_summary_at_check_in_provider;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_route_summary_in_local_bounds_family;
      eassumption.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_exact_body_target_in_local_bounds_family;
      eassumption.
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

Lemma infer_program_env_end2end_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef Hprog Hbase Henv Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_strict_exact_closure_component_route_summary_in_local_bounds_family;
      eassumption.
  - eapply infer_program_env_end2end_strict_exact_closure_exact_body_target_in_local_bounds_family;
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

Lemma infer_program_env_end2end_assoc_strict_exact_closure_exact_body_route_scoped_package_local_bounds_family :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
      (fun env0 fdef =>
        global_env_local_bounds_family env' env0 /\
          In fdef (env_fns env') /\
          check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
            env' fdef = true).
Proof.
  intros env env' Hprog.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_summary_at_check_provider_local_bounds_family.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_summary_at_check_in_provider.
    exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_exact_body_route_scoped_package_local_bounds_family_when_not_captured :
  forall env env',
    infer_program_env_end2end_assoc env = infer_ok env' ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
      (fun env0 fdef =>
        global_env_local_bounds_family env' env0 /\
          In fdef (env_fns env0) /\
          check_fn_root_shadow_captured_call_store_safe_summary
            env' fdef = false /\
          check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
            env' fdef = true).
Proof.
  intros env env' Hprog env0 fname fdef fcall used used' fname_body
    args_body (Hfamily & Hin_component & Hcaptured & Hcomponent_check)
    Hin Hname Hrename Htarget.
  destruct
    (infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_when_not_captured
      env env' env' env0 fdef Hprog
      (global_env_local_bounds_family_base env') Hfamily Hin_component
      Hcaptured Hcomponent_check)
    as [Hunique Hpayload].
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
    try eassumption.
  split; [exact Hunique | exact Hpayload].
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_exact_body_route_scoped_package_local_bounds_family_with_route_summary :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
    destruct (infer_program_env_end2end_assoc_strict_exact_closure_component_route_summary_in_local_bounds_family
                env env' env' env0 fdef Hprog
                (global_env_local_bounds_family_base env') Hfamily Hin
                Hcomponent_check) as [_ Hroute_summary].
    eapply Hroute_summary; eassumption.
  - intros env0 fdef (Hfamily & Hin & Hcomponent_check).
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_summary_in_local_bounds_family.
    + exact Hprog.
    + eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
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

Lemma infer_program_env_end2end_strict_exact_closure_seen_exact_body_target_in_local_bounds_family :
  forall env env' base env0 fdef fuel seen,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
      fuel seen env' fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef fuel seen _Hprog _Hbase _Henv Hseen
    Hnot_seen.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_head_checks
              fuel seen env' fdef Hseen Hnot_seen) as [_Hcomponent Hexact].
  eapply check_fn_root_shadow_no_capture_direct_call_component_exact_body_target_sound.
  exact Hexact.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_seen_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 fdef fuel seen,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
      fuel seen env' fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef fuel seen Hprog Hbase Henv Hin Hseen
    Hnot_seen.
  eapply infer_program_env_end2end_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin.
  - eapply infer_program_env_end2end_strict_exact_closure_seen_component_check_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_single_seen_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 f_component fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) [fn_name f_component] = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 f_component fdef Hprog Hbase Henv
    Hin_component Hin Hcomponent_check Hseen.
  simpl in Hseen.
  destruct (ident_eqb (fn_name fdef) (fn_name f_component)) eqn:Hname;
    try discriminate.
  apply ident_eqb_eq in Hname.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  change (env_fns
    (global_env_with_local_bounds
      (global_env_with_local_bounds env' bounds_base) bounds))
    with (env_fns env') in Hin.
  assert (Heq : fdef = f_component).
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    - exact Hprog.
    - exact Hin.
    - exact Hin_component.
    - exact Hname. }
  subst fdef.
  eapply infer_program_env_end2end_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family.
  - exact Hprog.
  - exists bounds_base. reflexivity.
  - exists bounds. reflexivity.
  - exact Hin_component.
  - exact Hcomponent_check.
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

Lemma infer_program_env_end2end_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    exists fuel',
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
        fuel' [fn_name f_component] env' fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hexact Htarget Hlookup.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  change (env_fns
    (global_env_with_local_bounds
      (global_env_with_local_bounds env' bounds_base) bounds))
    with (env_fns env') in Hlookup.
  eapply infer_program_env_end2end_strict_exact_closure_callee_seen_in_local_bounds_family.
  - exact Hprog.
  - exists bounds_base. reflexivity.
  - exists bounds. reflexivity.
  - exact Hexact.
  - exact Htarget.
  - eapply lookup_fn_b_of_lookup_fn.
    exact Hlookup.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_seen_component_check_in_local_bounds_family :
  forall env env' base env0 fdef fuel seen,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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

Lemma infer_program_env_end2end_assoc_strict_exact_closure_seen_exact_body_target_in_local_bounds_family :
  forall env env' base env0 fdef fuel seen,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
      fuel seen env' fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef fuel seen _Hprog _Hbase _Henv Hseen
    Hnot_seen.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_head_checks
              fuel seen env' fdef Hseen Hnot_seen) as [_Hcomponent Hexact].
  eapply check_fn_root_shadow_no_capture_direct_call_component_exact_body_target_sound.
  exact Hexact.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_seen_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 fdef fuel seen,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
      fuel seen env' fdef = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) seen = false ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 fdef fuel seen Hprog Hbase Henv Hin Hseen
    Hnot_seen.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_seen_component_check_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_single_seen_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 f_component fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    CheckerOrdinary.ident_in_b (fn_name fdef) [fn_name f_component] = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fdef /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fdef.
Proof.
  intros env env' base env0 f_component fdef Hprog Hbase Henv
    Hin_component Hin Hcomponent_check Hseen.
  simpl in Hseen.
  destruct (ident_eqb (fn_name fdef) (fn_name f_component)) eqn:Hname;
    try discriminate.
  apply ident_eqb_eq in Hname.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  change (env_fns
    (global_env_with_local_bounds
      (global_env_with_local_bounds env' bounds_base) bounds))
    with (env_fns env') in Hin.
  assert (Heq : fdef = f_component).
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    - exact Hprog.
    - exact Hin.
    - exact Hin_component.
    - exact Hname. }
  subst fdef.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family.
  - exact Hprog.
  - exists bounds_base. reflexivity.
  - exists bounds. reflexivity.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_callee_seen_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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

Lemma infer_program_env_end2end_assoc_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    exists fuel',
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
        fuel' [fn_name f_component] env' fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hexact Htarget Hlookup.
  destruct Hbase as (bounds_base & ->).
  destruct Henv as (bounds & ->).
  change (env_fns
    (global_env_with_local_bounds
      (global_env_with_local_bounds env' bounds_base) bounds))
    with (env_fns env') in Hlookup.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_callee_seen_in_local_bounds_family.
  - exact Hprog.
  - exists bounds_base. reflexivity.
  - exists bounds. reflexivity.
  - exact Hexact.
  - exact Htarget.
  - eapply lookup_fn_b_of_lookup_fn.
    exact Hlookup.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hin_component Hcomponent_check Hexact Htarget Hlookup.
  destruct (infer_program_env_end2end_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family
              env env' base env0 f_component fname args synthetic_body fcallee
              Hprog Hbase Henv Hexact Htarget Hlookup) as (fuel' & Hseen).
  destruct (CheckerOrdinary.ident_in_b (fn_name fcallee) [fn_name f_component])
    eqn:Hseen_name.
  - simpl in Hseen_name.
    destruct (ident_eqb (fn_name fcallee) (fn_name f_component))
      eqn:Hname; try discriminate.
    apply ident_eqb_eq in Hname.
    destruct Hbase as (bounds_base & ->).
    destruct Henv as (bounds & ->).
    change (lookup_fn fname
      (env_fns
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' bounds_base) bounds)) =
      Some fcallee) with
      (lookup_fn fname (env_fns env') = Some fcallee) in Hlookup.
    destruct (lookup_fn_in_name fname (env_fns env') fcallee Hlookup)
      as [Hin_callee _Hname_callee].
    assert (Heq : fcallee = f_component).
    { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
      - exact Hprog.
      - exact Hin_callee.
      - exact Hin_component.
      - exact Hname. }
    subst fcallee.
    exact Hcomponent_check.
  - eapply infer_program_env_end2end_strict_exact_closure_seen_component_check_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_direct_callee_component_ready_payload_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fcallee /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hin_component Hcomponent_check Hexact Htarget Hlookup.
  destruct (lookup_fn_in_name fname (env_fns env0) fcallee Hlookup)
    as [Hin_callee _Hname_callee].
  eapply infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_callee.
  - eapply infer_program_env_end2end_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fcallee /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fcallee.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hin_component Hcomponent_check Hexact Htarget Hlookup.
  destruct (lookup_fn_in_name fname (env_fns env0) fcallee Hlookup)
    as [Hin_callee _Hname_callee].
  destruct (infer_program_env_end2end_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family
              env env' base env0 f_component fname args synthetic_body fcallee
              Hprog Hbase Henv Hexact Htarget Hlookup) as (fuel' & Hseen).
  destruct (CheckerOrdinary.ident_in_b (fn_name fcallee) [fn_name f_component])
    eqn:Hseen_name.
  - eapply infer_program_env_end2end_strict_exact_closure_single_seen_route_summary_and_exact_target_in_local_bounds_family;
      eassumption.
  - eapply infer_program_env_end2end_strict_exact_closure_seen_route_summary_and_exact_target_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_direct_callee_summary_evidence_at_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env0 fname.
Proof.
  intros env env' base env0 f_component fname args synthetic_body Hprog
    Hbase Henv Hin_component Hcomponent_check Hexact Htarget fcallee
    Hlookup.
  destruct (infer_program_env_end2end_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family
              env env' base env0 f_component fname args synthetic_body
              fcallee Hprog Hbase Henv Hin_component Hcomponent_check Hexact
              Htarget Hlookup)
    as [[Hcomponent _Hroute_summary] _Hexact].
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  exact Hcomponent.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hin_component Hcomponent_check Hexact Htarget Hlookup.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family
              env env' base env0 f_component fname args synthetic_body fcallee
              Hprog Hbase Henv Hexact Htarget Hlookup) as (fuel' & Hseen).
  destruct (CheckerOrdinary.ident_in_b (fn_name fcallee) [fn_name f_component])
    eqn:Hseen_name.
  - simpl in Hseen_name.
    destruct (ident_eqb (fn_name fcallee) (fn_name f_component))
      eqn:Hname; try discriminate.
    apply ident_eqb_eq in Hname.
    destruct Hbase as (bounds_base & ->).
    destruct Henv as (bounds & ->).
    change (lookup_fn fname
      (env_fns
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' bounds_base) bounds)) =
      Some fcallee) with
      (lookup_fn fname (env_fns env') = Some fcallee) in Hlookup.
    destruct (lookup_fn_in_name fname (env_fns env') fcallee Hlookup)
      as [Hin_callee _Hname_callee].
    assert (Heq : fcallee = f_component).
    { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
      - exact Hprog.
      - exact Hin_callee.
      - exact Hin_component.
      - exact Hname. }
    subst fcallee.
    exact Hcomponent_check.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_seen_component_check_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_ready_payload_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fcallee /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fcallee = true.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hin_component Hcomponent_check Hexact Htarget Hlookup.
  destruct (lookup_fn_in_name fname (env_fns env0) fcallee Hlookup)
    as [Hin_callee _Hname_callee].
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_callee.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fcallee /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fcallee.
Proof.
  intros env env' base env0 f_component fname args synthetic_body fcallee
    Hprog Hbase Henv Hin_component Hcomponent_check Hexact Htarget Hlookup.
  destruct (lookup_fn_in_name fname (env_fns env0) fcallee Hlookup)
    as [Hin_callee _Hname_callee].
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family
              env env' base env0 f_component fname args synthetic_body fcallee
              Hprog Hbase Henv Hexact Htarget Hlookup) as (fuel' & Hseen).
  destruct (CheckerOrdinary.ident_in_b (fn_name fcallee) [fn_name f_component])
    eqn:Hseen_name.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_single_seen_route_summary_and_exact_target_in_local_bounds_family;
      eassumption.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_seen_route_summary_and_exact_target_in_local_bounds_family;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_summary_evidence_at_in_local_bounds_family :
  forall env env' base env0 f_component fname args synthetic_body,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env0 fname.
Proof.
  intros env env' base env0 f_component fname args synthetic_body Hprog
    Hbase Henv Hin_component Hcomponent_check Hexact Htarget fcallee
    Hlookup.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family
              env env' base env0 f_component fname args synthetic_body
              fcallee Hprog Hbase Henv Hin_component Hcomponent_check Hexact
              Htarget Hlookup)
    as [[Hcomponent _Hroute_summary] _Hexact].
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  exact Hcomponent.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_component_ready_payload_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fcallee /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fcallee = true.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body fcallee Hprog Hbase Henv Hin_component Hcomponent_check
    Hexact Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_strict_exact_closure_direct_callee_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fcallee /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fcallee.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body fcallee Hprog Hbase Henv Hin_component Hcomponent_check
    Hexact Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_component_check_of_lookup_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body fcallee,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fcallee = true.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body fcallee Hprog Hbase Henv Hin_component Hcomponent_check
    Hexact Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_summary_evidence_at_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env0 fname.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body Hprog Hbase Henv Hin_component Hcomponent_check Hexact
    Hrename Htarget fcallee Hlookup.
  destruct (infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_route_summary_and_exact_target_in_local_bounds_family
              env env' base env0 f_component fcall used used' fname args
              synthetic_body fcallee Hprog Hbase Henv Hin_component
              Hcomponent_check Hexact Hrename Htarget Hlookup)
    as [[Hcomponent _Hroute_summary] _Hexact].
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  exact Hcomponent.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_alpha_direct_callee_component_ready_payload_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    fn_env_unique_by_name env0 /\
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env0 fcallee /\
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env0 fcallee = true.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body fcallee Hprog Hbase Henv Hin_component Hcomponent_check
    Hexact Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_alpha_direct_callee_route_summary_and_exact_target_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
      env0 fcallee /\
    callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
      env0 fcallee.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body fcallee Hprog Hbase Henv Hin_component Hcomponent_check
    Hexact Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_alpha_direct_callee_component_check_of_lookup_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body fcallee,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname (env_fns env0) = Some fcallee ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fcallee = true.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body fcallee Hprog Hbase Henv Hin_component Hcomponent_check
    Hexact Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Henv.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_alpha_direct_callee_summary_evidence_at_in_local_bounds_family :
  forall env env' base env0 f_component fcall used used' fname args
      synthetic_body,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    global_env_local_bounds_family base env0 ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env0 fname.
Proof.
  intros env env' base env0 f_component fcall used used' fname args
    synthetic_body Hprog Hbase Henv Hin_component Hcomponent_check Hexact
    Hrename Htarget fcallee Hlookup.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_alpha_direct_callee_route_summary_and_exact_target_in_local_bounds_family
              env env' base env0 f_component fcall used used' fname args
              synthetic_body fcallee Hprog Hbase Henv Hin_component
              Hcomponent_check Hexact Hrename Htarget Hlookup)
    as [[Hcomponent _Hroute_summary] _Hexact].
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
  exact Hcomponent.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_callbacks_in_local_bounds_family :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body).
Proof.
  intros env env' f_component Hprog Hin_component Hcomponent_check Hexact.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  assert (Hbase : global_env_local_bounds_family env' body_env).
  { subst body_env. exists (fn_bounds f_component). reflexivity. }
  assert (Hbody_family : global_env_local_bounds_family body_env body_env).
  { eapply global_env_local_bounds_family_base. }
  split.
  - intros fname args synthetic_body Htarget.
    subst body_env.
    eapply infer_program_env_end2end_strict_exact_closure_direct_callee_summary_evidence_at_in_local_bounds_family.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + eapply global_env_local_bounds_family_base.
    + exact Hin_component.
    + exact Hcomponent_check.
    + exact Hexact.
    + exact Htarget.
  - split.
    + intros fname args synthetic_body fdef Htarget Hlookup.
      destruct (infer_program_env_end2end_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family
                  env env' body_env body_env f_component fname args
                  synthetic_body fdef Hprog Hbase Hbody_family Hin_component
                  Hcomponent_check Hexact Htarget Hlookup)
        as [[Hcomponent _Hroute_summary] _Hexact].
      exact Hcomponent.
    + intros fname args synthetic_body fdef Htarget Hlookup _Hcomponent
        fcall used used' fname_body args_body synthetic_body_nested Hrename
        Htarget_body.
      destruct (infer_program_env_end2end_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family
                  env env' body_env body_env f_component fname args
                  synthetic_body fdef Hprog Hbase Hbody_family Hin_component
                  Hcomponent_check Hexact Htarget Hlookup)
        as [[_Hcomponent_payload Hroute_summary] _Hexact].
      eapply Hroute_summary; eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_ready_payload_in_local_bounds_family :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      fn_env_unique_by_name
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef = true.
Proof.
  intros env env' f_component Hprog Hin_component Hcomponent_check Hexact
    fname args synthetic_body fdef Htarget Hlookup.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  assert (Hbase : global_env_local_bounds_family env' body_env).
  { subst body_env. exists (fn_bounds f_component). reflexivity. }
  assert (Hbody_family : global_env_local_bounds_family body_env body_env).
  { eapply global_env_local_bounds_family_base. }
  subst body_env.
  eapply infer_program_env_end2end_strict_exact_closure_direct_callee_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Hbody_family.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_ready_payload_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      fn_env_unique_by_name
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef = true.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  eapply infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hin.
  - exact Hcomponent_check.
  - eapply infer_program_env_end2end_strict_exact_closure_component_exact_closure;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_ready_provider_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    forall fcall used used' fname_body args_body synthetic_body_nested,
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body_nested) ->
      fn_env_unique_by_name
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          (fn_bounds fcall)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          (fn_bounds fcall)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          (fn_bounds fcall)) fdef = true.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog Hin
    Hcomponent_check Htarget Hlookup fcall used used' fname_body args_body
    synthetic_body_nested Hrename Htarget_body.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  pose (nested_env := global_env_with_local_bounds body_env (fn_bounds fcall)).
  assert (Hbase : global_env_local_bounds_family env' body_env).
  { subst body_env. exists (fn_bounds f_component). reflexivity. }
  assert (Hbody_family : global_env_local_bounds_family body_env body_env).
  { eapply global_env_local_bounds_family_base. }
  assert (Hnested : global_env_local_bounds_family body_env nested_env).
  { subst nested_env. exists (fn_bounds fcall). reflexivity. }
  destruct (lookup_fn_in_name fname (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup)
    as [Hin_fdef _Hname_fdef].
  assert (Hcallee_check :
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true).
  { eapply infer_program_env_end2end_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family.
    - exact Hprog.
    - exact Hbase.
    - exact Hbody_family.
    - exact Hin.
    - exact Hcomponent_check.
    - eapply infer_program_env_end2end_strict_exact_closure_component_exact_closure;
        eassumption.
    - exact Htarget.
    - exact Hlookup. }
  subst nested_env body_env.
  change (In fdef
    (env_fns
      (global_env_with_local_bounds
        (global_env_with_local_bounds env' (fn_bounds f_component))
        (fn_bounds fcall)))) in Hin_fdef.
  eapply infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Hnested.
  - exact Hin_fdef.
  - exact Hcallee_check.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_callbacks_in_local_bounds_family :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body).
Proof.
  intros env env' f_component Hprog Hin_component Hcomponent_check Hexact.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  assert (Hbase : global_env_local_bounds_family env' body_env).
  { subst body_env. exists (fn_bounds f_component). reflexivity. }
  assert (Hbody_family : global_env_local_bounds_family body_env body_env).
  { eapply global_env_local_bounds_family_base. }
  split.
  - intros fname args synthetic_body Htarget.
    subst body_env.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_summary_evidence_at_in_local_bounds_family.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + eapply global_env_local_bounds_family_base.
    + exact Hin_component.
    + exact Hcomponent_check.
    + exact Hexact.
    + exact Htarget.
  - split.
    + intros fname args synthetic_body fdef Htarget Hlookup.
      destruct (infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family
                  env env' body_env body_env f_component fname args
                  synthetic_body fdef Hprog Hbase Hbody_family Hin_component
                  Hcomponent_check Hexact Htarget Hlookup)
        as [[Hcomponent _Hroute_summary] _Hexact].
      exact Hcomponent.
    + intros fname args synthetic_body fdef Htarget Hlookup _Hcomponent
        fcall used used' fname_body args_body synthetic_body_nested Hrename
        Htarget_body.
      destruct (infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family
                  env env' body_env body_env f_component fname args
                  synthetic_body fdef Hprog Hbase Hbody_family Hin_component
                  Hcomponent_check Hexact Htarget Hlookup)
        as [[_Hcomponent_payload Hroute_summary] _Hexact].
      eapply Hroute_summary; eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_ready_payload_in_local_bounds_family :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    check_fn_root_shadow_no_capture_direct_call_component_exact_closure
      env' f_component = true ->
    forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      fn_env_unique_by_name
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef = true.
Proof.
  intros env env' f_component Hprog Hin_component Hcomponent_check Hexact
    fname args synthetic_body fdef Htarget Hlookup.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  assert (Hbase : global_env_local_bounds_family env' body_env).
  { subst body_env. exists (fn_bounds f_component). reflexivity. }
  assert (Hbody_family : global_env_local_bounds_family body_env body_env).
  { eapply global_env_local_bounds_family_base. }
  subst body_env.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Hbody_family.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Hexact.
  - exact Htarget.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_ready_payload_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      fn_env_unique_by_name
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef = true.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hin.
  - exact Hcomponent_check.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_ready_provider_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    forall fcall used used' fname_body args_body synthetic_body_nested,
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body_nested) ->
      fn_env_unique_by_name
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          (fn_bounds fcall)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          (fn_bounds fcall)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          (fn_bounds fcall)) fdef = true.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog Hin
    Hcomponent_check Htarget Hlookup fcall used used' fname_body args_body
    synthetic_body_nested Hrename Htarget_body.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  pose (nested_env := global_env_with_local_bounds body_env (fn_bounds fcall)).
  assert (Hbase : global_env_local_bounds_family env' body_env).
  { subst body_env. exists (fn_bounds f_component). reflexivity. }
  assert (Hbody_family : global_env_local_bounds_family body_env body_env).
  { eapply global_env_local_bounds_family_base. }
  assert (Hnested : global_env_local_bounds_family body_env nested_env).
  { subst nested_env. exists (fn_bounds fcall). reflexivity. }
  destruct (lookup_fn_in_name fname (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup)
    as [Hin_fdef _Hname_fdef].
  assert (Hcallee_check :
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true).
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family.
    - exact Hprog.
    - exact Hbase.
    - exact Hbody_family.
    - exact Hin.
    - exact Hcomponent_check.
    - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure;
        eassumption.
    - exact Htarget.
    - exact Hlookup. }
  subst nested_env body_env.
  change (In fdef
    (env_fns
      (global_env_with_local_bounds
        (global_env_with_local_bounds env' (fn_bounds f_component))
        (fn_bounds fcall)))) in Hin_fdef.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exact Hbase.
  - exact Hnested.
  - exact Hin_fdef.
  - exact Hcallee_check.
Qed.

Definition strict_exact_closure_component_body_route_package_at_provider
    (env' : global_env) (f_component : fn_def) : Prop :=
  forall fname args synthetic_body fdef,
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.

Definition strict_exact_closure_component_body_store_safe_callback_at_provider
    (env' : global_env) (f_component : fn_def) : Prop :=
  forall fname args synthetic_body fdef,
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fdef.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_exact_body_route_package_at_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog Hin_component
    Hcomponent_check Htarget Hlookup fdef0 fcall used used' fname_body
    args_body Hin0 Hname0 Hrename Htarget_body.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  destruct (lookup_fn_in_name fname (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup)
    as [Hin_fdef Hname_fdef].
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_ready_payload_of_component_check
      env env' f_component Hprog Hin_component Hcomponent_check fname args
      synthetic_body fdef Htarget Hlookup)
    as [Hunique [Hcomponent Hexact]].
  assert (Heq : fdef0 = fdef).
  { eapply Hunique; try eassumption.
    rewrite Hname0. exact (eq_sym Hname_fdef). }
  subst fdef0 body_env.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
    try eassumption.
  split; [exact Hunique |].
  split; [exact Hcomponent | exact Hexact].
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_alpha_exact_body_route_package_at_of_component_check :
  forall env env' f_component fcall used used' fname args synthetic_body fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fcall used used' fname args synthetic_body fdef
    Hprog Hin_component Hcomponent_check Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_strict_exact_closure_component_body_exact_body_route_package_at_of_component_check.
  - exact Hprog.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Htarget_original.
  - exact Hlookup.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_exact_body_route_package_at_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog Hin_component
    Hcomponent_check Htarget Hlookup fdef0 fcall used used' fname_body
    args_body Hin0 Hname0 Hrename Htarget_body.
  pose (body_env := global_env_with_local_bounds env' (fn_bounds f_component)).
  destruct (lookup_fn_in_name fname (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup)
    as [Hin_fdef Hname_fdef].
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_ready_payload_of_component_check
      env env' f_component Hprog Hin_component Hcomponent_check fname args
      synthetic_body fdef Htarget Hlookup)
    as [Hunique [Hcomponent Hexact]].
  assert (Heq : fdef0 = fdef).
  { eapply Hunique; try eassumption.
    rewrite Hname0. exact (eq_sym Hname_fdef). }
  subst fdef0 body_env.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
    try eassumption.
  split; [exact Hunique |].
  split; [exact Hcomponent | exact Hexact].
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_alpha_exact_body_route_package_at_of_component_check :
  forall env env' f_component fcall used used' fname args synthetic_body fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fcall used used' fname args synthetic_body fdef
    Hprog Hin_component Hcomponent_check Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_exact_body_route_package_at_of_component_check.
  - exact Hprog.
  - exact Hin_component.
  - exact Hcomponent_check.
  - exact Htarget_original.
  - exact Hlookup.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_reachable_component_check_in_local_bounds_family :
  forall env env' f_component fname args synthetic_body fdef env0 fname0 fcur,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname
      env0 fname0 ->
    In fcur (env_fns env0) ->
    fn_name fcur = fname0 ->
    global_env_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) env0 /\
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fcur = true.
Proof.
  intros env env' f_component fname args synthetic_body fdef env0 fname0
    fcur Hprog Hin_component Hcomponent_check Htarget Hlookup Hreachable.
  remember (global_env_with_local_bounds env' (fn_bounds f_component))
    as base_env0 eqn:Hbase_env.
  remember fname as base_fname eqn:Hbase_fname.
  change (store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable
    base_env0 base_fname env0 fname0) in Hreachable.
  assert (Hbody_base : global_env_local_bounds_family env' base_env0).
  { subst base_env0. exists (fn_bounds f_component). reflexivity. }
  revert fcur Hbase_env Hbase_fname.
  induction Hreachable as
    [base_env base_fname0
    |base_env base_fname0 env_cur fname_cur fdef_cur fcall used used'
      fname_body args_body Hreachable IH Hin_cur Hname_cur Hrename Htarget_cur];
    intros fcur Hbase_env Hbase_fname_eq Hin_fcur Hname_fcur.
  - subst base_fname0.
    subst base_env.
    split; [apply global_env_local_bounds_family_base |].
    assert (Hunique : fn_env_unique_by_name (global_env_with_local_bounds env' (fn_bounds f_component))).
    { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - apply global_env_local_bounds_family_base. }
    assert (Heq : fdef = fcur).
    { eapply lookup_fn_unique_by_name.
      - exact Hlookup.
      - exact Hin_fcur.
      - exact Hname_fcur.
      - exact Hunique. }
    subst fcur.
    assert (Hcheck_fdef :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true).
    { eapply infer_program_env_end2end_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - apply global_env_local_bounds_family_base.
      - exact Hin_component.
      - exact Hcomponent_check.
      - eapply infer_program_env_end2end_strict_exact_closure_component_exact_closure;
          eassumption.
      - exact Htarget.
      - exact Hlookup. }
    exact Hcheck_fdef.
  - destruct (IH Htarget Hlookup Hbody_base fdef_cur Hbase_env
        Hbase_fname_eq Hin_cur Hname_cur)
      as [Hfamily_cur Hcheck_cur].
    subst base_env.
    assert (Hfamily_body :
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))
        (global_env_with_local_bounds env_cur (fn_bounds fcall))).
    { eapply global_env_local_bounds_family_with_local_bounds.
      exact Hfamily_cur. }
    split; [exact Hfamily_body |].
    assert (Hunique_body :
      fn_env_unique_by_name
        (global_env_with_local_bounds env_cur (fn_bounds fcall))).
    { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - exact Hfamily_body. }
    assert (Hlookup_body :
      lookup_fn fname_body
        (env_fns (global_env_with_local_bounds env_cur (fn_bounds fcall))) =
      Some fcur).
    { eapply lookup_fn_of_in_unique_by_name.
      - exact Hunique_body.
      - exact Hin_fcur.
      - exact Hname_fcur. }
    assert (Hin_cur_env' : In fdef_cur (env_fns env')).
    { destruct Hfamily_cur as (bounds_cur & ->).
      change (env_fns
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          bounds_cur)) with (env_fns env') in Hin_cur.
      exact Hin_cur. }
    assert (Hexact_cur :
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef_cur = true).
    { eapply infer_program_env_end2end_strict_exact_closure_component_exact_closure;
        eassumption. }
    assert (Hcheck_fcur :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fcur = true).
    { eapply infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_component_check_of_lookup_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - exact Hfamily_cur.
      - exact Hin_cur_env'.
      - exact Hcheck_cur.
      - exact Hexact_cur.
      - exact Hrename.
      - exact Htarget_cur.
      - exact Hlookup_body. }
    exact Hcheck_fcur.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_component_check_in_local_bounds_family :
  forall env env' f_component fname args synthetic_body fdef env0 fname0 fcur,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname
      env0 fname0 ->
    In fcur (env_fns env0) ->
    fn_name fcur = fname0 ->
    global_env_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) env0 /\
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fcur = true.
Proof.
  intros env env' f_component fname args synthetic_body fdef env0 fname0
    fcur Hprog Hin_component Hcomponent_check Htarget Hlookup Hreachable.
  remember (global_env_with_local_bounds env' (fn_bounds f_component))
    as base_env0 eqn:Hbase_env.
  remember fname as base_fname eqn:Hbase_fname.
  change (store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable
    base_env0 base_fname env0 fname0) in Hreachable.
  assert (Hbody_base : global_env_local_bounds_family env' base_env0).
  { subst base_env0. exists (fn_bounds f_component). reflexivity. }
  revert fcur Hbase_env Hbase_fname.
  induction Hreachable as
    [base_env base_fname0
    |base_env base_fname0 env_cur fname_cur fdef_cur fcall used used'
      fname_body args_body Hreachable IH Hin_cur Hname_cur Hrename Htarget_cur];
    intros fcur Hbase_env Hbase_fname_eq Hin_fcur Hname_fcur.
  - subst base_fname0.
    subst base_env.
    split; [apply global_env_local_bounds_family_base |].
    assert (Hunique : fn_env_unique_by_name (global_env_with_local_bounds env' (fn_bounds f_component))).
    { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - apply global_env_local_bounds_family_base. }
    assert (Heq : fdef = fcur).
    { eapply lookup_fn_unique_by_name.
      - exact Hlookup.
      - exact Hin_fcur.
      - exact Hname_fcur.
      - exact Hunique. }
    subst fcur.
    assert (Hcheck_fdef :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true).
    { eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - apply global_env_local_bounds_family_base.
      - exact Hin_component.
      - exact Hcomponent_check.
      - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure;
          eassumption.
      - exact Htarget.
      - exact Hlookup. }
    exact Hcheck_fdef.
  - destruct (IH Htarget Hlookup Hbody_base fdef_cur Hbase_env
        Hbase_fname_eq Hin_cur Hname_cur)
      as [Hfamily_cur Hcheck_cur].
    subst base_env.
    assert (Hfamily_body :
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))
        (global_env_with_local_bounds env_cur (fn_bounds fcall))).
    { eapply global_env_local_bounds_family_with_local_bounds.
      exact Hfamily_cur. }
    split; [exact Hfamily_body |].
    assert (Hunique_body :
      fn_env_unique_by_name
        (global_env_with_local_bounds env_cur (fn_bounds fcall))).
    { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - exact Hfamily_body. }
    assert (Hlookup_body :
      lookup_fn fname_body
        (env_fns (global_env_with_local_bounds env_cur (fn_bounds fcall))) =
      Some fcur).
    { eapply lookup_fn_of_in_unique_by_name.
      - exact Hunique_body.
      - exact Hin_fcur.
      - exact Hname_fcur. }
    assert (Hin_cur_env' : In fdef_cur (env_fns env')).
    { destruct Hfamily_cur as (bounds_cur & ->).
      change (env_fns
        (global_env_with_local_bounds
          (global_env_with_local_bounds env' (fn_bounds f_component))
          bounds_cur)) with (env_fns env') in Hin_cur.
      exact Hin_cur. }
    assert (Hexact_cur :
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef_cur = true).
    { eapply infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure;
        eassumption. }
    assert (Hcheck_fcur :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fcur = true).
    { eapply infer_program_env_end2end_assoc_strict_exact_closure_alpha_direct_callee_component_check_of_lookup_in_local_bounds_family.
      - exact Hprog.
      - exact Hbody_base.
      - exact Hfamily_cur.
      - exact Hin_cur_env'.
      - exact Hcheck_cur.
      - exact Hexact_cur.
      - exact Hrename.
      - exact Htarget_cur.
      - exact Hlookup_body. }
    exact Hcheck_fcur.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_reachable_exact_body_route_package_provider_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog
    Hin_component Hcomponent_check Htarget Hlookup env0 fname0 Hreachable
    fcur fcall used used' fname_body args_body Hin Hname Hrename
    Htarget_body.
  assert (Hbody_base :
    global_env_local_bounds_family env'
      (global_env_with_local_bounds env' (fn_bounds f_component))).
  { exists (fn_bounds f_component). reflexivity. }
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_body_reachable_component_check_in_local_bounds_family
      env env' f_component fname args synthetic_body fdef env0 fname0 fcur
      Hprog Hin_component Hcomponent_check Htarget Hlookup Hreachable Hin
      Hname)
    as [Hfamily Hcheck].
  pose proof
    (infer_program_env_end2end_strict_exact_closure_exact_body_route_package_at_of_component_check_in_local_bounds_family
      env env' (global_env_with_local_bounds env' (fn_bounds f_component))
      env0 fname0 fcur Hprog Hbody_base Hfamily Hin Hname Hcheck)
    as Hpackage.
  eapply Hpackage; eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_reachable_exact_body_target_provider_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog
    Hin_component Hcomponent_check Htarget Hlookup env0 fname0 Hreachable
    fcur fcall used used' fname_body args_body synthetic_body0 Hin Hname
    Hrename Htarget_body.
  assert (Hbody_base :
    global_env_local_bounds_family env'
      (global_env_with_local_bounds env' (fn_bounds f_component))).
  { exists (fn_bounds f_component). reflexivity. }
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_body_reachable_component_check_in_local_bounds_family
      env env' f_component fname args synthetic_body fdef env0 fname0 fcur
      Hprog Hin_component Hcomponent_check Htarget Hlookup Hreachable Hin
      Hname)
    as [Hfamily Hcheck].
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family
      env env' (global_env_with_local_bounds env' (fn_bounds f_component))
      env0 fcur Hprog Hbody_base Hfamily Hin Hcheck)
    as [_ [_ Hexact]].
  eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
  - destruct
      (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
        env0 fcur Hexact) as [_ Hexact_target].
    exact Hexact_target.
  - exact Hrename.
  - exact Htarget_body.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_exact_body_route_package_provider_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog
    Hin_component Hcomponent_check Htarget Hlookup env0 fname0 Hreachable
    fcur fcall used used' fname_body args_body Hin Hname Hrename
    Htarget_body.
  assert (Hbody_base :
    global_env_local_bounds_family env'
      (global_env_with_local_bounds env' (fn_bounds f_component))).
  { exists (fn_bounds f_component). reflexivity. }
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_component_check_in_local_bounds_family
      env env' f_component fname args synthetic_body fdef env0 fname0 fcur
      Hprog Hin_component Hcomponent_check Htarget Hlookup Hreachable Hin
      Hname)
    as [Hfamily Hcheck].
  pose proof
    (infer_program_env_end2end_assoc_strict_exact_closure_exact_body_route_package_at_of_component_check_in_local_bounds_family
      env env' (global_env_with_local_bounds env' (fn_bounds f_component))
      env0 fname0 fcur Hprog Hbody_base Hfamily Hin Hname Hcheck)
    as Hpackage.
  eapply Hpackage; eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_exact_body_target_provider_of_component_check :
  forall env env' f_component fname args synthetic_body fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fname args synthetic_body fdef Hprog
    Hin_component Hcomponent_check Htarget Hlookup env0 fname0 Hreachable
    fcur fcall used used' fname_body args_body synthetic_body0 Hin Hname
    Hrename Htarget_body.
  assert (Hbody_base :
    global_env_local_bounds_family env'
      (global_env_with_local_bounds env' (fn_bounds f_component))).
  { exists (fn_bounds f_component). reflexivity. }
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_component_check_in_local_bounds_family
      env env' f_component fname args synthetic_body fdef env0 fname0 fcur
      Hprog Hin_component Hcomponent_check Htarget Hlookup Hreachable Hin
      Hname)
    as [Hfamily Hcheck].
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family
      env env' (global_env_with_local_bounds env' (fn_bounds f_component))
      env0 fcur Hprog Hbody_base Hfamily Hin Hcheck)
    as [_ [_ Hexact]].
  eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
  - destruct
      (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
        env0 fcur Hexact) as [_ Hexact_target].
    exact Hexact_target.
  - exact Hrename.
  - exact Htarget_body.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body).
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  eapply infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_callbacks_in_local_bounds_family.
  - exact Hprog.
  - exact Hin.
  - exact Hcomponent_check.
  - eapply infer_program_env_end2end_strict_exact_closure_component_exact_closure;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready env env' f_component Hprog
    Hin_component Hcomponent_check.
  split.
  - intros fname args synthetic_body fdef Htarget Hlookup.
    eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_at_of_reachable_exact_body_call_route_package_and_target_provider_prefix.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hstatic.
    + exact Hframe_ready.
    + exact Hparam_ready.
    + eapply infer_program_env_end2end_strict_exact_closure_component_body_reachable_exact_body_target_provider_of_component_check;
        eassumption.
    + eapply infer_program_env_end2end_strict_exact_closure_component_body_reachable_exact_body_route_package_provider_of_component_check;
        eassumption.
    + destruct (lookup_fn_in_name fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup) as [Hin _].
      exact Hin.
    + destruct (lookup_fn_in_name fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup) as [_ Hname].
      exact Hname.
  - eapply infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
  - exact Hframe_ready.
  - exact Hparam_ready.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body).
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_callbacks_in_local_bounds_family.
  - exact Hprog.
  - exact Hin.
  - exact Hcomponent_check.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_exact_closure;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready env env' f_component Hprog
    Hin_component Hcomponent_check.
  split.
  - intros fname args synthetic_body fdef Htarget Hlookup.
    eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_at_of_reachable_exact_body_call_route_package_and_target_provider_prefix.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hstatic.
    + exact Hframe_ready.
    + exact Hparam_ready.
    + eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_exact_body_target_provider_of_component_check;
        eassumption.
    + eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_reachable_exact_body_route_package_provider_of_component_check;
        eassumption.
    + destruct (lookup_fn_in_name fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup) as [Hin _].
      exact Hin.
    + destruct (lookup_fn_in_name fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component)))
        fdef Hlookup) as [_ Hname].
      exact Hname.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
  - exact Hframe_ready.
  - exact Hparam_ready.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_ready_payload_and_callbacks_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      fn_env_unique_by_name
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef = true) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_ready_payload_of_component_check;
      eassumption.
  - eapply infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_route_package_and_callbacks_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_route_package_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  split.
  - intros fname args synthetic_body fdef Htarget Hlookup.
    eapply infer_program_env_end2end_strict_exact_closure_component_body_exact_body_route_package_at_of_component_check;
      eassumption.
  - eapply infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_route_package_at_provider_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_route_package_at_provider
      env' f_component.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  destruct (infer_program_env_end2end_strict_exact_closure_component_body_route_package_and_callbacks_of_component_check
              env env' f_component Hprog Hin Hcomponent_check)
    as [Hroute_package _].
  exact Hroute_package.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_body_route_package_at_provider_alpha_target :
  forall env env' f_component fcall used used' fname args synthetic_body fdef,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_route_package_at_provider
      env' f_component ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fcall used used' fname args synthetic_body fdef
    _Hprog _Hin _Hcomponent_check Hprovider Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply Hprovider.
  - exact Htarget_original.
  - exact Hlookup.
Qed.



Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_ready_payload_and_callbacks_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      fn_env_unique_by_name
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef = true) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_direct_callee_ready_payload_of_component_check;
      eassumption.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_route_package_and_callbacks_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_route_package_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  split.
  - intros fname args synthetic_body fdef Htarget Hlookup.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_exact_body_route_package_at_of_component_check;
      eassumption.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_route_package_at_provider_of_component_check :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_route_package_at_provider
      env' f_component.
Proof.
  intros env env' f_component Hprog Hin Hcomponent_check.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure_component_body_route_package_and_callbacks_of_component_check
              env env' f_component Hprog Hin Hcomponent_check)
    as [Hroute_package _].
  exact Hroute_package.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_body_route_package_at_provider_alpha_target :
  forall env env' f_component fcall used used' fname args synthetic_body fdef,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_route_package_at_provider
      env' f_component ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      (global_env_with_local_bounds env' (fn_bounds f_component)) fname.
Proof.
  intros env env' f_component fcall used used' fname args synthetic_body fdef
    _Hprog _Hin _Hcomponent_check Hprovider Hrename Htarget Hlookup.
  destruct (direct_call_target_expr_alpha_rename_fn_def_inv
              used f_component fcall used' fname args synthetic_body
              Hrename Htarget) as (args0 & Htarget_original).
  eapply Hprovider.
  - exact Htarget_original.
  - exact Hlookup.
Qed.


Lemma infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_ready_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hcomponent_provider.
  eapply (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package_with_component_exact_target
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys base
    (fun env0 fdef =>
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply Hcomponent_provider; eassumption.
  - intros env0 fdef (_Hunique & _Hcomponent & Hexact).
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env0 fdef Hexact) as [_ Hexact_target].
    exact Hexact_target.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_payload_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
        env0 fdef /\
      callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
        env0 fdef) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hcomponent_provider.
  eapply (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package_with_component_exact_target
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys base
    (fun env0 fdef =>
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
        env0 fdef /\
      callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
        env0 fdef)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply Hcomponent_provider; eassumption.
  - intros env0 fdef [_Hroute_summary Hexact]. exact Hexact.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_route_summary_and_exact_target_ready.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_ready_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hcomponent_provider.
  eapply (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package_with_component_exact_target
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys base
    (fun env0 fdef =>
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply Hcomponent_provider; eassumption.
  - intros env0 fdef (_Hunique & _Hcomponent & Hexact).
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env0 fdef Hexact) as [_ Hexact_target].
    exact Hexact_target.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_payload_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
        env0 fdef /\
      callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
        env0 fdef) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hcomponent_provider.
  eapply (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package_with_component_exact_target
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys base
    (fun env0 fdef =>
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
        env0 fdef /\
      callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
        env0 fdef)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply Hcomponent_provider; eassumption.
  - intros env0 fdef [_Hroute_summary Hexact]. exact Hexact.
  - exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_route_summary_and_exact_target_ready.
Qed.

Lemma infer_program_env_end2end_assoc_component_local_bounds_route_of_exact_closure_provider_package_at :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fdef,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef = true) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hexact_provider.
  eapply
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_package_at_provider.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    destruct
      (infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_of_exact_closure
        env env' base env0 fdef Hprog Hbase Hfamily Hin
        (Hexact_provider env0 fdef Hfamily Hin))
      as [_ [_ Hexact]].
    eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
    + destruct
        (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
          env0 fdef Hexact) as [_ Hexact_target].
      exact Hexact_target.
    + exact Hrename.
    + exact Htarget.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply infer_program_env_end2end_assoc_exact_body_route_package_at_of_exact_closure_in_local_bounds_family.
    + exact Hprog.
    + exact Hbase.
    + exact Hfamily.
    + exact Hin.
    + exact Hname.
    + eapply Hexact_provider; eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_component_local_bounds_route_of_exact_closure_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    global_env_local_bounds_family env' base ->
    (forall env0 fdef,
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef = true) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hexact_provider.
  eapply infer_program_env_end2end_assoc_component_local_bounds_route_of_exact_closure_provider_package_at;
    eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_check_provider_package_at :
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
  eapply
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_package_at_provider.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    destruct
      (infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family
        env env' base env0 fdef Hprog Hbase Hfamily Hin
        (Hcomponent_check_provider env0 fdef Hfamily Hin))
      as [_ [_ Hexact]].
    eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
    + destruct
        (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
          env0 fdef Hexact) as [_ Hexact_target].
      exact Hexact_target.
    + exact Hrename.
    + exact Htarget.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply infer_program_env_end2end_strict_exact_closure_exact_body_route_package_at_of_component_check_in_local_bounds_family.
    + exact Hprog.
    + exact Hbase.
    + exact Hfamily.
    + exact Hin.
    + exact Hname.
    + eapply Hcomponent_check_provider; eassumption.
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
  eapply infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_check_provider_package_at;
    eassumption.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_check_provider_package_at :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  eapply
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_package_at_provider.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    destruct
      (infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family
        env env' base env0 fdef Hprog Hbase Hfamily Hin
        (Hcomponent_check_provider env0 fdef Hfamily Hin))
      as [_ [_ Hexact]].
    eapply callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any.
    + destruct
        (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
          env0 fdef Hexact) as [_ Hexact_target].
      exact Hexact_target.
    + exact Hrename.
    + exact Htarget.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_exact_body_route_package_at_of_component_check_in_local_bounds_family.
    + exact Hprog.
    + exact Hbase.
    + exact Hfamily.
    + exact Hin.
    + exact Hname.
    + eapply Hcomponent_check_provider; eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' base,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_check_provider_package_at;
    eassumption.
Qed.

Theorem infer_program_env_end2end_ordinary_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hinitial Hin Hstore
    Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_unique_by_name. exact Hprog. }
  assert (Hcheck_env :
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env' = true).
  { eapply infer_program_env_end2end_check_env_ready. exact Hprog. }
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply forallb_forall with (x := f) in Hcheck_env; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply orb_true_iff in Hcheck_env as [Hcaptured_check | Hexact_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f Hexact_check) as [Hcomponent _Hexact_target].
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply component_body_synthetic_direct_call_ready_summary_at_in_of_exact_closure_check;
        eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check;
        eassumption.
    + intros fname_component args_component synthetic_component fdef
        Htarget_component Hlookup_component Hfdef_component fcall used used'
        fname_body args_body synthetic_body Hrename Htarget_body ftarget
        Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_exact_closure_check;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hinitial Hin Hstore
    Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  assert (Hcheck_env :
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env' = true).
  { eapply infer_program_env_end2end_assoc_check_env_ready. exact Hprog. }
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply forallb_forall with (x := f) in Hcheck_env; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply orb_true_iff in Hcheck_env as [Hcaptured_check | Hexact_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f Hexact_check) as [Hcomponent _Hexact_target].
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply component_body_synthetic_direct_call_ready_summary_at_in_of_exact_closure_check;
        eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check;
        eassumption.
    + intros fname_component args_component synthetic_component fdef
        Htarget_component Hlookup_component Hfdef_component fcall used used'
        fname_body args_body synthetic_body Hrename Htarget_body ftarget
        Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_exact_closure_check;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hinitial Hin Hstore
    Heval.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_check :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_store_safe_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_body_store_safe_summary_evidence :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_store_safe_summary_evidence.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_exact_package_and_component_body_summary_at_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
    exact Hprog.
  - exact Hsummary_at_provider.
  - exact Hbody_evidence_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_exact_package_and_component_body_summary_at_in_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
    exact Hprog.
  - exact Hsummary_at_provider.
  - exact Hnested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_summary_at_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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


Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_in_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
    exact Hprog.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_summary_provider_and_closure_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_nested_in_evidence.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_provider_and_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_in_evidence.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_target_provider :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_in_evidence.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply infer_program_env_end2end_assoc_combined_check_env_ready.
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


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe_prefix.
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
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.



Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe_prefix.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.



Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    split.
    + eapply Hcomponent_route; eassumption.
    + eapply infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check;
        eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_callback_height_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_callback_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      ((forall fname args synthetic_body,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
        forall fcall used used' fname_body args_body synthetic_body_nested,
          alpha_rename_fn_def used fdef = (fcall, used') ->
          direct_call_target_expr (fn_body fcall) =
            Some (fname_body, args_body, synthetic_body_nested) ->
          fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
            (global_env_with_local_bounds
              (global_env_with_local_bounds env' (fn_bounds f_component))
              (fn_bounds fcall)) fname_body))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_call_callback_height_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply Hcomponent_route; eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    split.
    + eapply Hcomponent_route; eassumption.
    + eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check;
        eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_callback_height_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_callback_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) /\
      ((forall fname args synthetic_body,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
        forall fcall used used' fname_body args_body synthetic_body_nested,
          alpha_rename_fn_def used fdef = (fcall, used') ->
          direct_call_target_expr (fn_body fcall) =
            Some (fname_body, args_body, synthetic_body_nested) ->
          fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
            (global_env_with_local_bounds
              (global_env_with_local_bounds env' (fn_bounds f_component))
              (fn_bounds fcall)) fname_body))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_call_callback_height_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply Hcomponent_route; eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component /\
      ((forall fname args synthetic_body,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
        forall fcall used used' fname_body args_body synthetic_body_nested,
          alpha_rename_fn_def used fdef = (fcall, used') ->
          direct_call_target_expr (fn_body fcall) =
            Some (fname_body, args_body, synthetic_body_nested) ->
          fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
            (global_env_with_local_bounds
              (global_env_with_local_bounds env' (fn_bounds f_component))
              (fn_bounds fcall)) fname_body))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply Hcomponent_route; eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.



Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component /\
      ((forall fname args synthetic_body,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
       (forall fname args synthetic_body fdef,
        direct_call_target_expr (fn_body f_component) =
          Some (fname, args, synthetic_body) ->
        lookup_fn fname
          (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
          Some fdef ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
        forall fcall used used' fname_body args_body synthetic_body_nested,
          alpha_rename_fn_def used fdef = (fcall, used') ->
          direct_call_target_expr (fn_body fcall) =
            Some (fname_body, args_body, synthetic_body_nested) ->
          fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
            (global_env_with_local_bounds
              (global_env_with_local_bounds env' (fn_bounds f_component))
              (fn_bounds fcall)) fname_body))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply Hcomponent_route; eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_check_provider_of_check_env_no_capture :
  forall env' env0 fdef,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    global_env_local_bounds_family env' env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true.
Proof.
  intros env' env0 fdef Hcheck Hfamily Hin.
  destruct Hfamily as (bounds & ->).
  change (env_fns (global_env_with_local_bounds env' bounds))
    with (env_fns env') in Hin.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
    in Hcheck.
  eapply forallb_forall; eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_ready_provider_of_component_check_provider :
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true.
Proof.
  intros env env' f_component Hprog Hcomponent_check_provider env0 fname
    fdef fcall used used' fname_body args_body synthetic_body Hfamily Hin
    _Hname _Hrename _Htarget.
  eapply infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exists (fn_bounds f_component). reflexivity.
  - exact Hfamily.
  - exact Hin.
  - eapply Hcomponent_check_provider.
    + eapply global_env_local_bounds_family_of_local_bounds_base.
      exact Hfamily.
    + exact Hin.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_check_provider_of_check_env_no_capture :
  forall env' env0 fdef,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    global_env_local_bounds_family env' env0 ->
    In fdef (env_fns env0) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' fdef = true.
Proof.
  intros env' env0 fdef Hcheck Hfamily Hin.
  eapply infer_program_env_end2end_strict_exact_closure_component_check_provider_of_check_env_no_capture;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_ready_provider_of_component_check_provider :
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true.
Proof.
  intros env env' f_component Hprog Hcomponent_check_provider env0 fname
    fdef fcall used used' fname_body args_body synthetic_body Hfamily Hin
    _Hname _Hrename _Htarget.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_ready_payload_in_local_bounds_family.
  - exact Hprog.
  - exists (fn_bounds f_component). reflexivity.
  - exact Hfamily.
  - exact Hin.
  - eapply Hcomponent_check_provider.
    + eapply global_env_local_bounds_family_of_local_bounds_base.
      exact Hfamily.
    + exact Hin.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_ready_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog Hcomponent_provider
    Hin_component Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_ready_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + exact Hcomponent_provider.
  - eapply infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
        env0 fdef /\
      callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
        env0 fdef) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog Hcomponent_provider
    Hin_component Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_payload_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + exact Hcomponent_provider.
  - eapply infer_program_env_end2end_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog
    Hcomponent_check_provider Hin_component Hcomponent_check.
  eapply infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin0 _Hname _Hrename _Htarget.
    eapply infer_program_env_end2end_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + exact Hfamily.
    + exact Hin0.
    + eapply Hcomponent_check_provider.
      * eapply global_env_local_bounds_family_of_local_bounds_base.
        exact Hfamily.
      * exact Hin0.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_ready_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_env_unique_by_name env0 /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env0 fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env0 fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog Hcomponent_provider
    Hin_component Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_ready_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + exact Hcomponent_provider.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
        env0 fdef /\
      callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
        env0 fdef) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog Hcomponent_provider
    Hin_component Hcomponent_check.
  split.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_local_bounds_route_of_component_payload_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + exact Hcomponent_provider.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_component_body_callbacks_of_component_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog
    Hcomponent_check_provider Hin_component Hcomponent_check.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin0 _Hname _Hrename _Htarget.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family.
    + exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + exact Hfamily.
    + exact Hin0.
    + eapply Hcomponent_check_provider.
      * eapply global_env_local_bounds_family_of_local_bounds_base.
        exact Hfamily.
      * exact Hin0.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_and_callbacks_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog
    Hcomponent_check_provider Hin_component Hcomponent_check.
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_check_provider
      Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
      Hroot_keys env env' f_component Hprog Hcomponent_check_provider
      Hin_component Hcomponent_check) as [Hsummary Hcallbacks].
  split.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family_of_summary_at_prefix_call_statement_evidence_at_height.
    exact Hsummary.
  - exact Hcallbacks.
Qed.

Lemma infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog
    Hcomponent_check_provider Hin_component Hcomponent_check.
  destruct
    (infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_and_callbacks_of_component_check_provider
      Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
      Hroot_keys env env' f_component Hprog Hcomponent_check_provider
      Hin_component Hcomponent_check) as [Hfamily Hcallbacks].
  split.
  - intros fname args synthetic_body fdef _Htarget _Hlookup.
    eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_at_of_in_local_bounds_family.
    + exact Hfamily.
    + apply global_env_local_bounds_family_base.
  - exact Hcallbacks.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_and_callbacks_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)) /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog
    Hcomponent_check_provider Hin_component Hcomponent_check.
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_check_provider
      Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
      Hroot_keys env env' f_component Hprog Hcomponent_check_provider
      Hin_component Hcomponent_check) as [Hsummary Hcallbacks].
  split.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family_of_summary_at_prefix_call_statement_evidence_at_height.
    exact Hsummary.
  - exact Hcallbacks.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_provider :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component /\
    ((forall fname args synthetic_body,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env' (fn_bounds f_component)) fname) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef) /\
     (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f_component) =
        Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env' (fn_bounds f_component)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env' (fn_bounds f_component))
            (fn_bounds fcall)) fname_body)).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f_component Hprog
    Hcomponent_check_provider Hin_component Hcomponent_check.
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_and_callbacks_of_component_check_provider
      Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
      Hroot_keys env env' f_component Hprog Hcomponent_check_provider
      Hin_component Hcomponent_check) as [Hfamily Hcallbacks].
  split.
  - intros fname args synthetic_body fdef _Htarget _Hlookup.
    eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_at_of_in_local_bounds_family.
    + exact Hfamily.
    + apply global_env_local_bounds_family_base.
  - exact Hcallbacks.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hframe_ready Hparam_ready env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_prefix.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hstatic.
    + exact Hframe_ready.
    + exact Hparam_ready.
    + exact Hprog.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
  - exact Hframe_ready.
  - exact Hparam_ready.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_provider_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_check_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exact Hcomponent_check_provider.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hframe_ready Hparam_ready env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_prefix.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hstatic.
    + exact Hframe_ready.
    + exact Hparam_ready.
    + exact Hprog.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
  - exact Hframe_ready.
  - exact Hparam_ready.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_provider_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_check_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_body_call_store_safe_callback_height_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_store_safe_callback_at_provider_and_callbacks_of_component_check_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exact Hcomponent_check_provider.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_ready_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
        global_env_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        fn_env_unique_by_name env0 /\
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          env0 fdef /\
        check_fn_root_shadow_no_capture_direct_call_component_exact_closure
          env0 fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_provider
    Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_ready_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + eapply Hcomponent_provider; eassumption.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_payload_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
        global_env_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
          env0 fdef /\
        callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
          env0 fdef) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_provider
    Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + eapply Hcomponent_provider; eassumption.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_check_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_ready_provider_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component _Hin_component _Hcomponent_check env0 fname fdef fcall
      used used' fname_body args_body synthetic_body Hfamily Hin0 Hname
      Hrename Htarget.
    eapply infer_program_env_end2end_strict_exact_closure_component_ready_provider_of_component_check_provider.
    + exact Hprog.
    + exact Hcomponent_check_provider.
    + exact Hfamily.
    + exact Hin0.
    + exact Hname.
    + exact Hrename.
    + exact Htarget.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_ready_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
        global_env_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        fn_env_unique_by_name env0 /\
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          env0 fdef /\
        check_fn_root_shadow_no_capture_direct_call_component_exact_closure
          env0 fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_provider
    Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_ready_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + eapply Hcomponent_provider; eassumption.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_payload_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      forall env0 fname fdef fcall used used' fname_body args_body synthetic_body,
        global_env_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component)) env0 ->
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_route_summary
          env0 fdef /\
        callee_body_root_shadow_no_capture_direct_call_component_exact_body_target
          env0 fdef) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_provider
    Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + eapply Hcomponent_provider; eassumption.
    + exact Hin_component.
    + exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_check_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_ready_provider_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component _Hin_component _Hcomponent_check env0 fname fdef fcall
      used used' fname_body args_body synthetic_body Hfamily Hin0 Hname
      Hrename Htarget.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_component_ready_provider_of_component_check_provider.
    + exact Hprog.
    + exact Hcomponent_check_provider.
    + exact Hfamily.
    + exact Hin0.
    + exact Hname.
    + exact Hrename.
    + exact Htarget.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_of_pointwise_exact_body_call_route_package_non_store_safe_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  (forall env fname,
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env fname) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hframe_ready Hparam_ready
    Hexact_body_target Hbody_package_at env env' f s s' v Hprog Hinitial
    Hin Hstore Heval.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe_prefix.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_height_statement.
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_of_exact_body_call_route_package_at_all_no_scope_prefix;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_of_pointwise_exact_body_call_route_package_non_store_safe :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
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
  (forall env fname,
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env fname) ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_of_pointwise_exact_body_call_route_package_non_store_safe_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hcomponent_route.
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


Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_of_pointwise_exact_body_call_route_package_non_store_safe_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  (forall env fname,
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env fname) ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic Hframe_ready Hparam_ready
    Hexact_body_target Hbody_package_at env env' f s s' v Hprog Hinitial
    Hin Hstore Heval.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe_prefix.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_height_statement.
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_of_exact_body_call_route_package_at_all_no_scope_prefix;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_of_pointwise_exact_body_call_route_package_non_store_safe :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
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
  (forall env fname,
    store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
      env fname) ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_of_pointwise_exact_body_call_route_package_non_store_safe_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hprog.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  assert (Hcheck_env :
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env' = true).
  { eapply infer_program_env_end2end_assoc_check_env_ready. exact Hprog. }
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply forallb_forall with (x := f) in Hcheck_env; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply orb_true_iff in Hcheck_env as [Hcaptured_check | Hexact_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f Hexact_check) as [Hcomponent _Hexact_target].
    assert (Hcomponent_check :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f = true).
    { unfold check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        in Hexact_check.
      eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check.
      - exact Hexact_check.
      - reflexivity. }
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_in_local_bounds_family.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + eapply Hcomponent_route; eassumption.
    + intros fname args synthetic_body Htarget.
      pose proof Hcomponent as Hcomponent_summary.
      destruct Hcomponent_summary as
        (fname0 & args0 & raw_body0 & synthetic_body0 & fcallee & T_body0 &
          Gamma_out0 & R_body0 & roots_body0 & _Hcaptures0 & Hbody0 &
          Htarget0 & _Hsynthetic0 & _Hsafe_args0 & Hin_callee & Hname_callee &
          _Hcallee_captures0 & _Hnodup0 & _Htyped0 & _Hcompat0 & _Hroots0 &
          _Henv0).
      rewrite Hbody0 in Htarget.
      rewrite Htarget0 in Htarget. injection Htarget as <- <- <-.
      intros fdef Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * rewrite Hbody0. exact Htarget0.
      * exact Hlookup_target.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * exact Htarget.
      * exact Hlookup_target.
    + intros fname_component args_component synthetic_component fdef
        Htarget_component Hlookup_component Hfdef_component fcall used used'
        fname_body args_body synthetic_body Hrename Htarget_body ftarget
        Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_exact_closure_check;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_exact_local_bounds_family :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  assert (Hcheck_env :
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env' = true).
  { eapply infer_program_env_end2end_assoc_check_env_ready. exact Hprog. }
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply forallb_forall with (x := f) in Hcheck_env; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
    in Hcheck_env.
  apply orb_true_iff in Hcheck_env as [Hcaptured_check | Hexact_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f Hexact_check) as [Hcomponent _Hexact_target].
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_in_local_bounds_family.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + eapply Hcomponent_route; eassumption.
    + intros fname args synthetic_body Htarget.
      pose proof Hcomponent as Hcomponent_summary.
      destruct Hcomponent_summary as
        (fname0 & args0 & raw_body0 & synthetic_body0 & fcallee & T_body0 &
          Gamma_out0 & R_body0 & roots_body0 & _Hcaptures0 & Hbody0 &
          Htarget0 & _Hsynthetic0 & _Hsafe_args0 & Hin_callee & Hname_callee &
          _Hcallee_captures0 & _Hnodup0 & _Htyped0 & _Hcompat0 & _Hroots0 &
          _Henv0).
      rewrite Hbody0 in Htarget.
      rewrite Htarget0 in Htarget. injection Htarget as <- <- <-.
      intros fdef Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * rewrite Hbody0. exact Htarget0.
      * exact Hlookup_target.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * exact Htarget.
      * exact Hlookup_target.
    + intros fname_component args_component synthetic_component fdef
        Htarget_component Hlookup_component Hfdef_component fcall used used'
        fname_body args_body synthetic_body Hrename Htarget_body ftarget
        Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_exact_closure_check;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
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


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe_prefix.
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
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
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



Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe_prefix.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_and_exact_closure_provider :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hstore_safe_route Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hexact_body_target Hbody_package
    env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hexact_body_target component_ready Hcomponent_provider
    Hscoped_package env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys component_ready Hcomponent_provider Htarget_provider
    Hscoped_package env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_check_route_package :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_check_provider Hstrict_provider env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply (infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_non_captured_route_package :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hnon_captured_provider Hstrict_provider env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_check_route_package.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_ready_route_package :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_provider env env' f s s' v Hprog Hinitial Hin
    Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_body_target_provider :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_provider Htarget_provider env env' f s s' v Hprog
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_closure_provider :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hcomponent_provider Hexact_closure_provider env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_body_target_provider.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys Hexact_body_target Hcomponent_provider env env' f s s' v Hprog
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package.
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


Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hsummary_body_at_all
    Hexact_body_target env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
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


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height_prefix;
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
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe_prefix.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height_prefix;
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
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
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



Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_branch_local_strict_exact_closure_check :
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_branch_local_strict_exact_closure_check.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height_prefix;
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check :
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe_prefix.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height_prefix;
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe :
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe_prefix.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_component_body_closure_check :
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_check.
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


Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_nested_in_evidence.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hprog. }
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_nested_in_evidence.
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

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider.
  - exact Hsynthetic_route.
  - exact Hscope_summary_at.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hprovider.
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

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_no_scope_prefix;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package_prefix;
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
    Hstatic.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix.
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
    Hstatic.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.


Theorem infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_direct_receiver_method_component_check_scoped_expr_lift :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure env = infer_ok env' ->
    env_fns_root_shadow_provenance_summary_evidence env' ->
    env_fns_preservation_ready env' ->
    check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary
      env' = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_expr_lift_provider_for_eval env' f ->
    direct_receiver_method_consumed_scoped_expr_lift_provider_for_eval env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hevidence Hready Hdirect_check Hcomponent_check Hinitial Hin Hstore
    Heval Hlive_expr Hconsumed_expr.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hprog. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_expr_lift;
    eassumption.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog. }
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_summary_at.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_combined_check_env_ready.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_evidence_at;
      try eassumption.
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_no_scope_prefix;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package_prefix;
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix.
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

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check :
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
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.



Lemma check_env_end2end_direct_receiver_ready_facts :
  forall env,
    check_env_end2end_direct_receiver_ready env = true ->
    check_env_root_shadow_provenance_summary env = true /\
    check_env_preservation_ready env = true /\
    check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary
      env = true /\
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true.
Proof.
  intros env Hcheck.
  unfold check_env_end2end_direct_receiver_ready in Hcheck.
  repeat apply andb_true_iff in Hcheck as [Hcheck ?].
  repeat split; assumption.
Qed.


Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false \/
    check_env_end2end_direct_receiver_ready env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_mixed in Hprog.
  destruct (infer_program_env_end2end_assoc env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked)
    eqn:Hmixed_ready; try discriminate.
  injection Hprog as <-.
  eapply check_env_end2end_direct_receiver_mixed_ready_cases.
  exact Hmixed_ready.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_direct_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hdirect_ready Hinitial Hin Hstore Heval.
  destruct (check_env_end2end_direct_receiver_ready_facts env' Hdirect_ready)
    as (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hbase : infer_program_env_end2end_assoc env = infer_ok env').
  { eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog. }
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_assoc_unique_by_name. exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - apply direct_receiver_method_live_scoped_body_lift_ready_provider_proven.
  - apply direct_receiver_method_consumed_scoped_body_lift_ready_provider_proven.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_case_split_routes :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hstore_safe_route Hscope_synthetic Htyping_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f
    s s' v Hprog Hinitial Hin Hstore Heval.
  destruct
    (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
      env env' Hprog) as [_Hno_receiver | Hdirect_ready].
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready.
    + exact Hstore_safe_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exact Hinitial.
    + exact Hin.
    + exact Hstore.
    + exact Heval.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_direct_ready.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hframe_ready.
    + exact Hparam_ready.
    + exact Hprog.
    + exact Hdirect_ready.
    + exact Hinitial.
    + exact Hin.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem infer_program_env_end2end_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_body_lift_ready_provider_for_eval
      env' f ->
    direct_receiver_method_consumed_scoped_body_lift_ready_provider_for_eval
      env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_body Hconsumed_body.
  unfold infer_program_env_end2end_strict_exact_closure_direct_receiver in Hprog.
  destruct (infer_program_env_end2end_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hunique : fn_env_unique_by_name env_checked).
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_body.
  - exact Hconsumed_body.
Qed.


Theorem infer_program_env_end2end_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - apply direct_receiver_method_live_scoped_body_lift_ready_provider_proven.
  - apply direct_receiver_method_consumed_scoped_body_lift_ready_provider_proven.
Qed.


Theorem infer_program_env_end2end_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_body_lift :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_body_lift_provider_for_eval env' f ->
    direct_receiver_method_consumed_scoped_body_lift_provider_for_eval env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_body Hconsumed_body.
  unfold infer_program_env_end2end_strict_exact_closure_direct_receiver in Hprog.
  destruct (infer_program_env_end2end_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hunique : fn_env_unique_by_name env_checked).
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_body_lift.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_body.
  - exact Hconsumed_body.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_selected_scoped_raw_body_replay :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_raw_body_replay_provider_for_eval
      env' f s s' v ->
    direct_receiver_method_consumed_scoped_raw_body_replay_provider_for_eval
      env' f s s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_raw Hconsumed_raw.
  unfold infer_program_env_end2end_strict_exact_closure_direct_receiver in Hprog.
  destruct (infer_program_env_end2end_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hunique : fn_env_unique_by_name env_checked).
  { eapply infer_program_env_end2end_strict_exact_closure_unique_by_name.
    exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_selected_scoped_raw_body_replay.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_raw.
  - exact Hconsumed_raw.
Qed.

Theorem infer_program_env_end2end_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_expr_lift :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_expr_lift_provider_for_eval env' f ->
    direct_receiver_method_consumed_scoped_expr_lift_provider_for_eval env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_expr Hconsumed_expr.
  unfold infer_program_env_end2end_strict_exact_closure_direct_receiver in Hprog.
  destruct (infer_program_env_end2end_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_direct_receiver_method_component_check_scoped_expr_lift.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hbase.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_expr.
  - exact Hconsumed_expr.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_direct_receiver_method_component_check_scoped_expr_lift :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    env_fns_root_shadow_provenance_summary_evidence env' ->
    env_fns_preservation_ready env' ->
    check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary
      env' = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_expr_lift_provider_for_eval env' f ->
    direct_receiver_method_consumed_scoped_expr_lift_provider_for_eval env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hevidence Hready Hdirect_check Hcomponent_check Hinitial Hin Hstore
    Heval Hlive_expr Hconsumed_expr.
  assert (Hunique : fn_env_unique_by_name env').
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hprog. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_expr_lift;
    eassumption.
Qed.




Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_body_lift_ready_provider_for_eval
      env' f ->
    direct_receiver_method_consumed_scoped_body_lift_ready_provider_for_eval
      env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_body Hconsumed_body.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hunique : fn_env_unique_by_name env_checked).
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_body.
  - exact Hconsumed_body.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_body_lift_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - apply direct_receiver_method_live_scoped_body_lift_ready_provider_proven.
  - apply direct_receiver_method_consumed_scoped_body_lift_ready_provider_proven.
Qed.


Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    infer_program_env_end2end_assoc_strict_exact_closure env =
      infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked);
    try discriminate.
  injection Hprog as <-.
  reflexivity.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_unique_by_name :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    fn_env_unique_by_name env'.
Proof.
  intros env env' Hprog.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_check_env_ready :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env' = true.
Proof.
  intros env env' Hprog.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_ready_cases :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false \/
    check_env_end2end_direct_receiver_ready env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked)
    eqn:Hmixed_ready; try discriminate.
  injection Hprog as <-.
  eapply check_env_end2end_direct_receiver_mixed_ready_cases.
  exact Hmixed_ready.
Qed.

Lemma infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_direct_ready_endpoint :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
      env = infer_ok env'.
Proof.
  intros env env' Hprog Hdirect_ready.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver.
  rewrite (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base
    env env' Hprog).
  rewrite Hdirect_ready.
  reflexivity.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_direct_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hdirect_ready Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_direct_ready_endpoint;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_no_receiver_method :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog _Hno_receiver_method
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_case_split_routes :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hstore_safe_route Hscope_synthetic Htyping_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f
    s s' v Hprog Hinitial Hin Hstore Heval.
  destruct
    (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_ready_cases
      env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_no_receiver_method.
    + exact Hstore_safe_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hprog.
    + exact Hno_receiver.
    + exact Hinitial.
    + exact Hin.
    + exact Hstore.
    + exact Heval.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_direct_ready.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hframe_ready.
    + exact Hparam_ready.
    + exact Hprog.
    + exact Hdirect_ready.
    + exact Hinitial.
    + exact Hin.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_of_base_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros _Hsynthetic_route Hscope_synthetic _Htyping_ready Hroots_ready
    Hroot_names Hroot_keys _Hframe_ready _Hparam_ready env env' f s s' v
    Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  pose proof
    (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base
      env env' Hprog) as Hbase.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hbase.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_static_component_callbacks_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros _Hsynthetic_route Hscope_synthetic _Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  pose proof
    (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base
      env env' Hprog) as Hbase.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_store_safe_at_target_callbacks_prefix.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_prefix_mutual.
  - exact eval_preserves_typing_roots_ready_prefix_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hbase.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_component_check_provider_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_check_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_provider_store_safe_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hcomponent_check_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_static_component_callbacks :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_static_component_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_direct_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_when_direct_ready.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_case_split_routes :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_case_split_routes.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_case_split_exact_body_call_route_package :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
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
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hstore_safe_route Hscope_synthetic Htyping_prefix
    Hprefix_ready Hroots_ready Hroot_names Hroot_keys Hframe_ready
    Hparam_ready Hexact_body_target Hbody_package env env' f s s' v
    Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_case_split_routes.
  - exact Hsynthetic_route.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package;
      eassumption.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check_provider :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  forall env env_out f s s_out v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env_out ->
    (forall env0 fdef,
      global_env_local_bounds_family env_out env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env_out fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env_out) ->
    initial_store_for_fn env_out f s ->
    eval env_out s (fn_body f) s_out v ->
    value_has_type env_out s_out v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call env env_out f s s_out v Hprog
    Hcomponent_check_provider Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check.
  - exact Hsynthetic_call_route.
  - exact Hscope_call.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary.
    apply forallb_forall. intros fdef Hin_fdef.
    eapply Hcomponent_check_provider.
    + apply global_env_local_bounds_family_base.
    + exact Hin_fdef.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  forall env env_out f s s_out v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env_out ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env_out = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env_out) ->
    initial_store_for_fn env_out f s ->
    eval env_out s (fn_body f) s_out v ->
    value_has_type env_out s_out v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call env env_out f s s_out v Hprog
    Hcomponent_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check_provider.
  - exact Hsynthetic_call_route.
  - exact Hscope_call.
  - exact Hprog.
  - intros env0 fdef Hfamily Hin0.
    destruct Hfamily as [bounds ->].
    simpl in Hin0.
    unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary in Hcomponent_check.
    eapply forallb_forall in Hcomponent_check; eauto.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_check_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  (forall env fname,
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at env fname) ->
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
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros _ Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys _ _ Hstatic Hsummary_of_evidence
    Hexact_body_target component_ready Hcomponent_provider Hscoped_package
    env env' f s s' v Hprog Hcomponent_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement_of_exact_body_call_route_scoped_package_height_prefix;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement_of_statement.
    exact Hscope_synthetic.
  - exact Hprog.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.



Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_exact_body_call_route_local_bounds_package_and_component_check_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  (forall env fname,
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at env fname) ->
  (forall env fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, fn_body fcall)) ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall env0 fname fdef fcall used used' fname_body args_body
        synthetic_body,
      In fdef (env_fns env0) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      global_env_local_bounds_family env' env0 /\
        check_fn_root_shadow_captured_call_store_safe_summary
          env' fdef = false /\
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' fdef = true) ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic Hscope_synthetic Htyping_prefix Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic
    Hsummary_of_evidence Hexact_body_target env env' f s s' v Hprog
    Hroute_ready Hcomponent_check Hinitial Hin Hstore Heval.
  eapply (infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_check_prefix
    Hsynthetic Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic
    Hsummary_of_evidence Hexact_body_target
    (fun env0 fdef =>
      global_env_local_bounds_family env' env0 /\
        In fdef (env_fns env0) /\
        check_fn_root_shadow_captured_call_store_safe_summary
          env' fdef = false /\
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' fdef = true)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hin0 Hname Hrename Htarget.
    destruct (Hroute_ready env0 fname fdef fcall used used' fname_body
      args_body synthetic_body Hin0 Hname Hrename Htarget)
      as (Hfamily & Hcaptured & Hcomponent).
    repeat split; try exact Hfamily; try exact Hin0; try exact Hcaptured;
      exact Hcomponent.
  - eapply infer_program_env_end2end_assoc_exact_body_route_scoped_package_local_bounds_family_when_not_captured.
    eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hprog.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_of_base_route :
  (forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f)) ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hassoc_base_runtime env env' f s s' v Hprog Hcomponent_route
    Hinitial Hin Hstore Heval.
  eapply Hassoc_base_runtime.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_of_exact_base_route :
  (forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f)) ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hassoc_base_runtime env env' f s s' v Hprog Hcomponent_route
    Hinitial Hin Hstore Heval.
  eapply Hassoc_base_runtime.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_exact_local_bounds_route_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_of_exact_base_route.
  - eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_exact_local_bounds_family.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
  - exact Hprog.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_exact_local_bounds_provider_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall base env0 fdef,
      global_env_local_bounds_family env' base ->
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hexact_provider
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_exact_local_bounds_route_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hexact_component.
    eapply infer_program_env_end2end_assoc_component_local_bounds_route_of_exact_closure_provider.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog.
    + exists (fn_bounds f_component). reflexivity.
    + intros env0 fdef Hfamily Hin0.
      eapply Hexact_provider.
      * exists (fn_bounds f_component). reflexivity.
      * exact Hfamily.
      * exact Hin0.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_exact_local_bounds_provider_callbacks_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall base env0 fdef,
      global_env_local_bounds_family env' base ->
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros _Hsynthetic_route Hscope_synthetic _Htyping_ready Hroots_ready
    Hroot_names Hroot_keys _Hframe_ready _Hparam_ready _Hstatic
    env env' f s s' v Hprog Hexact_provider Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_exact_local_bounds_provider_callbacks.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_prefix_mutual.
  - exact eval_preserves_typing_roots_ready_prefix_mutual.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hexact_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_exact_local_bounds_provider_callbacks_store_static :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_store_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall base env0 fdef,
      global_env_local_bounds_family env' base ->
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_exact_local_bounds_provider_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store Hstatic).
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_exact_local_bounds_provider_callbacks :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall base env0 fdef,
      global_env_local_bounds_family env' base ->
      global_env_local_bounds_family base env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_exact_local_bounds_provider_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_local_bounds_route_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_ready Hroots_ready Hroot_names Hroot_keys
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_of_base_route.
  - eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
  - exact Hprog.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_local_bounds_route_callbacks_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros _Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys _Hframe_ready _Hparam_ready _Hstatic
    env env' f s s' v Hprog Hcomponent_route Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_local_bounds_route_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hcomponent_route.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_local_bounds_route_callbacks_store_static :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_store_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_local_bounds_route_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store Hstatic).
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_local_bounds_route_callbacks :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_local_bounds_route_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_component_check_provider_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    (forall env0 fdef,
      global_env_local_bounds_family env' env0 ->
      In fdef (env_fns env0) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_component_check_provider_store_safe_at_target_callbacks.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_component_check_store_safe_at_target_callbacks :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' f s s' v Hprog Hcomponent_check
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_component_check_provider_store_safe_at_target_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros env0 fdef Hfamily Hin0.
    destruct Hfamily as [bounds ->].
    simpl in Hin0.
    unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary in Hcomponent_check.
    eapply forallb_forall in Hcomponent_check; eauto.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_component_callbacks_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_static_component_callbacks_prefix.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_component_callbacks_store_static :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_store_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_component_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store Hstatic).
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_component_callbacks :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_component_callbacks_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_static_component_callbacks_store_static.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact preservation_ready_expr_static_runtime_named_prefix_store_complete.
Qed.


Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_body_lift :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_body_lift_provider_for_eval env' f ->
    direct_receiver_method_consumed_scoped_body_lift_provider_for_eval env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_body Hconsumed_body.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hunique : fn_env_unique_by_name env_checked).
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_scoped_body_lift.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_body.
  - exact Hconsumed_body.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_selected_scoped_raw_body_replay :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_raw_body_replay_provider_for_eval
      env' f s s' v ->
    direct_receiver_method_consumed_scoped_raw_body_replay_provider_for_eval
      env' f s s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_raw Hconsumed_raw.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  assert (Hunique : fn_env_unique_by_name env_checked).
  { eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hbase. }
  eapply check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_selected_scoped_raw_body_replay.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hunique.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_raw.
  - exact Hconsumed_raw.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_big_step_safe_checked_initial_ready_with_scoped_expr_lift :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
      env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    direct_receiver_method_live_scoped_expr_lift_provider_for_eval env' f ->
    direct_receiver_method_consumed_scoped_expr_lift_provider_for_eval env' f ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hinitial Hin Hstore Heval Hlive_expr Hconsumed_expr.
  unfold infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
    in Hprog.
  destruct (infer_program_env_end2end_assoc_strict_exact_closure env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_ready env_checked)
    eqn:Hdirect_ready; try discriminate.
  injection Hprog as <-.
  destruct (check_env_end2end_direct_receiver_ready_facts
    env_checked Hdirect_ready) as
    (Hprov_check & Hpres_check & Hdirect_check & Hcomponent_check).
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_direct_receiver_method_component_check_scoped_expr_lift.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hbase.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
  - exact Hdirect_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
  - exact Hlive_expr.
  - exact Hconsumed_expr.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_no_scope_prefix;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package_prefix;
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
    Hstatic.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
Qed.


Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix :
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_evidence_at;
      try eassumption.
    eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_no_scope_prefix;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package_prefix;
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider :
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
    infer_program_env_end2end_assoc env = infer_ok env' ->
    component_body_synthetic_direct_call_ready_summary_provider env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Htyping_prefix Hprefix_ready Hroots_ready Hroot_names Hroot_keys
    Hstatic.
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider_prefix.
  - exact Htyping_prefix.
  - exact Hprefix_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_static Hstatic).
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_body_summary_evidence :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_summary_evidence.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_check :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
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
  eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_check.
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
