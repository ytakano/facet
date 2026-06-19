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


Theorem infer_fn_env_end2end_assoc_direct_receiver_base_sound :
  forall env f T Gamma_out R_out roots,
    infer_fn_env_end2end_assoc_direct_receiver_base env f =
      infer_ok (T, Gamma_out, R_out, roots) ->
    checked_fn_env_roots_checked_assoc_boundary env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Gamma_out R_out roots Hend.
  unfold infer_fn_env_end2end_assoc_direct_receiver_base in Hend.
  destruct (infer_full_env_roots_checked_assoc env f
              (initial_root_env_for_params
                (fn_params f ++ fn_captures f)))
    as [[[[T' Gamma'] R'] roots'] | err] eqn:Hinfer; try discriminate.
  destruct (check_fn_root_shadow_assoc_direct_receiver_base_summary env f);
    try discriminate.
  injection Hend as <- <- <- <-.
  eapply infer_full_env_roots_checked_assoc_entry_boundary_sound.
  exact Hinfer.
Qed.

Lemma infer_fns_env_end2end_assoc_direct_receiver_base_in_sound :
  forall env fns f,
    infer_fns_env_end2end_assoc_direct_receiver_base env fns = infer_ok tt ->
    In f fns ->
    exists T Gamma_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env f =
        infer_ok (T, Gamma_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  induction fns as [| f_head rest IH]; intros f Hinfer Hin.
  - contradiction.
  - simpl in Hinfer. simpl in Hin.
    destruct (infer_fn_env_end2end_assoc_direct_receiver_base env f_head)
      as [[[[T_head Gamma_head] R_head] roots_head] | err] eqn:Hhead;
      try discriminate.
    destruct Hin as [-> | Hin].
    + exists T_head, Gamma_head, R_head, roots_head.
      split; [exact Hhead |].
      eapply infer_fn_env_end2end_assoc_direct_receiver_base_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_base_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Gamma_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Gamma_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end_assoc_direct_receiver_base in Hprog.
  destruct (global_names_unique_b (alpha_normalize_global_env env));
    try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err]
    eqn:Helab; try discriminate.
  destruct (infer_fns_env_end2end_assoc_direct_receiver_base
              env_elab (env_fns env_elab)) as [[] | err]
    eqn:Hfns; try discriminate.
  injection Hprog as <-.
  eapply infer_fns_env_end2end_assoc_direct_receiver_base_in_sound;
    eassumption.
Qed.

Lemma check_program_env_end2end_assoc_direct_receiver_base_infer_ok :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_direct_receiver_base in Hcheck.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base env)
    as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_sound :
  forall env env' f,
    check_program_env_end2end_assoc_direct_receiver_base env = true ->
    infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Gamma_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Gamma_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_sound; eauto.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_sound_exists :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Gamma_out R_out roots,
          infer_fn_env_end2end_assoc_direct_receiver_base env' f =
            infer_ok (T, Gamma_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_direct_receiver_base_infer_ok
      env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_sound; eauto.
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
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked &&
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env_checked) eqn:Hgate; try discriminate.
  apply andb_true_iff in Hgate as [_Hmixed_ready _Hlocal_check].
  injection Hprog as <-.
  reflexivity.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_local_certificate_check :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env' = true.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_mixed in Hprog.
  destruct (infer_program_env_end2end_assoc env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked &&
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env_checked) eqn:Hgate; try discriminate.
  apply andb_true_iff in Hgate as [_Hmixed_ready Hlocal_check].
  injection Hprog as <-.
  exact Hlocal_check.
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

Lemma infer_program_env_end2end_assoc_receiver_method_exact_mixed_base :
  forall env env',
    infer_program_env_end2end_assoc_receiver_method_exact_mixed env =
      infer_ok env' ->
    infer_program_env_end2end_assoc env = infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_receiver_method_exact_mixed in Hprog.
  destruct (infer_program_env_end2end_assoc env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_root_shadow_receiver_method_strict_exact_closure_summary
    env_checked) eqn:Hexact; simpl in Hprog; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked &&
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env_checked) eqn:Hgate; try discriminate.
  apply andb_true_iff in Hgate as [_Hmixed_ready _Hlocal_check].
  injection Hprog as ->.
  reflexivity.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_of_receiver_method_exact_mixed :
  forall env env',
    infer_program_env_end2end_assoc_receiver_method_exact_mixed env =
      infer_ok env' ->
    infer_program_env_end2end_assoc_direct_receiver_mixed env = infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_receiver_method_exact_mixed in Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_mixed.
  destruct (infer_program_env_end2end_assoc env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_root_shadow_receiver_method_strict_exact_closure_summary
    env_checked) eqn:Hexact; simpl in Hprog; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked &&
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env_checked) eqn:Hgate; try discriminate.
  injection Hprog as ->.
  reflexivity.
Qed.


Theorem infer_program_env_end2end_assoc_receiver_method_exact_mixed_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_receiver_method_exact_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_sound;
    eauto.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_of_receiver_method_exact_mixed.
  exact Hprog.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_base_mixed_base :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_base_mixed env =
      infer_ok env' ->
    infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_base_mixed in Hprog.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked);
    try discriminate.
  injection Hprog as <-.
  reflexivity.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_base_mixed_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_direct_receiver_base_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_sound; eauto.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_mixed_base.
  exact Hprog.
Qed.

Lemma check_program_env_end2end_assoc_direct_receiver_base_mixed_infer_ok :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base_mixed env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base_mixed env =
        infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_direct_receiver_base_mixed in Hcheck.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base_mixed env)
    as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_mixed_sound :
  forall env env' f,
    check_program_env_end2end_assoc_direct_receiver_base_mixed env = true ->
    infer_program_env_end2end_assoc_direct_receiver_base_mixed env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_mixed_sound;
    eauto.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_mixed_sound_exists :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base_mixed env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base_mixed env =
        infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc_direct_receiver_base env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_direct_receiver_base_mixed_infer_ok
       env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_mixed_sound;
    eauto.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_base_combined_base :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_base_combined env =
      infer_ok env' ->
    infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_base_combined
    in Hprog.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct
    (check_env_root_shadow_captured_call_store_safe_with_direct_receiver_method_or_no_capture_direct_component_summary
      env_checked); try discriminate.
  injection Hprog as <-.
  reflexivity.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_base_combined_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_direct_receiver_base_combined env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_sound; eauto.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_combined_base.
  exact Hprog.
Qed.

Lemma check_program_env_end2end_assoc_direct_receiver_base_combined_infer_ok :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base_combined env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base_combined env =
        infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_direct_receiver_base_combined
    in Hcheck.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base_combined
    env) as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_combined_sound :
  forall env env' f,
    check_program_env_end2end_assoc_direct_receiver_base_combined env = true ->
    infer_program_env_end2end_assoc_direct_receiver_base_combined env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_combined_sound;
    eauto.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_combined_sound_exists :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base_combined env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base_combined env =
        infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc_direct_receiver_base env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_direct_receiver_base_combined_infer_ok
       env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_combined_sound;
    eauto.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_base_direct_component_base :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_base_direct_component env =
      infer_ok env' ->
    infer_program_env_end2end_assoc_direct_receiver_base env = infer_ok env'.
Proof.
  intros env env' Hprog.
  unfold infer_program_env_end2end_assoc_direct_receiver_base_direct_component
    in Hprog.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base env)
    as [env_checked | err] eqn:Hbase; try discriminate.
  destruct
    (check_env_root_shadow_direct_receiver_method_or_no_capture_direct_component_store_safe_summary
      env_checked); try discriminate.
  injection Hprog as <-.
  reflexivity.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_base_direct_component_sound :
  forall env env' f,
    infer_program_env_end2end_assoc_direct_receiver_base_direct_component env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_sound; eauto.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_direct_component_base.
  exact Hprog.
Qed.

Lemma check_program_env_end2end_assoc_direct_receiver_base_direct_component_infer_ok :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base_direct_component env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base_direct_component env =
        infer_ok env'.
Proof.
  intros env Hcheck.
  unfold check_program_env_end2end_assoc_direct_receiver_base_direct_component
    in Hcheck.
  destruct (infer_program_env_end2end_assoc_direct_receiver_base_direct_component
    env) as [env' | err] eqn:Hprog; try discriminate.
  exists env'. reflexivity.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_direct_component_sound :
  forall env env' f,
    check_program_env_end2end_assoc_direct_receiver_base_direct_component env = true ->
    infer_program_env_end2end_assoc_direct_receiver_base_direct_component env =
      infer_ok env' ->
    In f (env_fns env') ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end_assoc_direct_receiver_base env' f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_direct_component_sound;
    eauto.
Qed.

Theorem check_program_env_end2end_assoc_direct_receiver_base_direct_component_sound_exists :
  forall env,
    check_program_env_end2end_assoc_direct_receiver_base_direct_component env = true ->
    exists env',
      infer_program_env_end2end_assoc_direct_receiver_base_direct_component env =
        infer_ok env' /\
      forall f,
        In f (env_fns env') ->
        exists T Γ_out R_out roots,
          infer_fn_env_end2end_assoc_direct_receiver_base env' f =
            infer_ok (T, Γ_out, R_out, roots) /\
          checked_fn_env_roots_checked_assoc_boundary env' f
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            R_out roots.
Proof.
  intros env Hcheck.
  destruct
    (check_program_env_end2end_assoc_direct_receiver_base_direct_component_infer_ok
       env Hcheck) as [env' Hprog].
  exists env'. split; [exact Hprog |].
  intros f Hin.
  eapply infer_program_env_end2end_assoc_direct_receiver_base_direct_component_sound;
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


Lemma check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary_of_strict_exact_closure :
  forall env fdef,
    check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env fdef = true ->
    check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
      env fdef = true.
Proof.
  intros env fdef Hstrict.
  unfold check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
    in Hstrict.
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary.
  destruct (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
              env fdef) eqn:Hcomponent.
  - rewrite Hstrict. destruct (check_fn_root_shadow_captured_call_store_safe_summary env fdef); reflexivity.
  - rewrite Hstrict. reflexivity.
Qed.

Lemma infer_fn_env_end2end_assoc_of_strict_exact_closure :
  forall env f T Gamma_out R_out roots,
    infer_fn_env_end2end_assoc_strict_exact_closure env f =
      infer_ok (T, Gamma_out, R_out, roots) ->
    infer_fn_env_end2end_assoc env f =
      infer_ok (T, Gamma_out, R_out, roots).
Proof.
  intros env f T Gamma_out R_out roots Hstrict.
  unfold infer_fn_env_end2end_assoc_strict_exact_closure in Hstrict.
  unfold infer_fn_env_end2end_assoc.
  destruct (infer_full_env_roots_checked_assoc env f
              (initial_root_env_for_params (fn_params f ++ fn_captures f)))
    as [[[[T' Gamma'] R'] roots'] | err] eqn:Hinfer; try discriminate.
  destruct (check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
              env f) eqn:Hgate; try discriminate.
  injection Hstrict as -> -> -> ->.
  rewrite (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary_of_strict_exact_closure
    env f Hgate).
  reflexivity.
Qed.

Lemma infer_fns_env_end2end_assoc_of_strict_exact_closure :
  forall env fns,
    infer_fns_env_end2end_assoc_strict_exact_closure env fns = infer_ok tt ->
    infer_fns_env_end2end_assoc env fns = infer_ok tt.
Proof.
  induction fns as [| f rest IH]; intros Hstrict.
  - reflexivity.
  - simpl in Hstrict. simpl.
    destruct (infer_fn_env_end2end_assoc_strict_exact_closure env f)
      as [[[[T Gamma_out] R_out] roots] | err] eqn:Hfn; try discriminate.
    rewrite (infer_fn_env_end2end_assoc_of_strict_exact_closure
      env f T Gamma_out R_out roots Hfn).
    eapply IH. exact Hstrict.
Qed.

Lemma infer_program_env_end2end_assoc_of_strict_exact_closure :
  forall env env',
    infer_program_env_end2end_assoc_strict_exact_closure env = infer_ok env' ->
    infer_program_env_end2end_assoc env = infer_ok env'.
Proof.
  intros env env' Hstrict.
  unfold infer_program_env_end2end_assoc_strict_exact_closure in Hstrict.
  unfold infer_program_env_end2end_assoc.
  destruct (global_names_unique_b (alpha_normalize_global_env env))
    eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err]
    eqn:Helab; try discriminate.
  destruct (infer_fns_env_end2end_assoc_strict_exact_closure
              env_elab (env_fns env_elab)) as [[] | err]
    eqn:Hfns; try discriminate.
  injection Hstrict as ->.
  rewrite (infer_fns_env_end2end_assoc_of_strict_exact_closure
    env' (env_fns env') Hfns).
  reflexivity.
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

Definition strict_exact_closure_component_body_narrow_callee_at_provider
    (env' : global_env) (f_component : fn_def) : Prop :=
  forall fname args synthetic_body fdef,
    direct_call_target_expr (fn_body f_component) =
      Some (fname, args, synthetic_body) ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env' (fn_bounds f_component))) =
      Some fdef ->
    callee_body_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env' (fn_bounds f_component)) fdef.

Definition callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary
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
    callee_body_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env (fn_bounds fdef)) fcallee /\
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

Lemma infer_program_env_end2end_assoc_component_local_bounds_route_of_non_captured_component_provider :
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
      check_fn_root_shadow_captured_call_store_safe_summary
        env' fdef = false /\
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' fdef = true) ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys env env' base Hprog Hbase Hcomponent_provider.
  eapply (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package
    Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready Hroot_names
    Hroot_keys base
    (fun env0 fdef =>
      global_env_local_bounds_family base env0 /\
        In fdef (env_fns env0) /\
        check_fn_root_shadow_captured_call_store_safe_summary
          env' fdef = false /\
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' fdef = true)).
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body Hfamily Hin Hname Hrename Htarget.
    destruct (Hcomponent_provider env0 fdef Hfamily Hin)
      as [Hcaptured Hcomponent_check].
    destruct
      (infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_when_not_captured
        env env' base env0 fdef Hprog Hbase Hfamily Hin Hcaptured
        Hcomponent_check)
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
    destruct (Hcomponent_provider env0 fdef Hfamily Hin)
      as [Hcaptured Hcomponent_check].
    repeat split; try exact Hfamily; try exact Hin; try exact Hcaptured;
      exact Hcomponent_check.
  - intros env0 fname fdef fcall used used' fname_body args_body
      (Hfamily & Hin_component & Hcaptured & Hcomponent_check) Hin Hname
      Hrename Htarget.
    eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready;
      try eassumption.
    destruct
      (infer_program_env_end2end_assoc_component_ready_payload_in_local_bounds_family_when_not_captured
        env env' base env0 fdef Hprog Hbase Hfamily Hin_component
        Hcaptured Hcomponent_check)
      as [Hunique Hpayload].
    split; [exact Hunique | exact Hpayload].
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

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_body_store_safe_provider_of_component_check :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env = infer_ok env' ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' = true ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider
      env'.
Proof.
  intros env env' _Hprog Hcomponent_check.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_body_store_safe_provider.
  exact Hcomponent_check.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_uncaptured_component_local_bounds_family :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_captured_call_store_safe_summary
        env' f_component = false ->
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
  destruct (check_fn_root_shadow_captured_call_store_safe_summary env' f)
    eqn:Hcaptured_check.
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - simpl in Hcheck_env.
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f Hcheck_env) as [Hcomponent _Hexact_target].
    assert (Hcomponent_check :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f = true).
    { unfold check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        in Hcheck_env.
      eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check.
      - exact Hcheck_env.
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
      * exact Hcheck_env.
      * rewrite Hbody0. exact Htarget0.
      * exact Hlookup_target.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hcheck_env.
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
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hexact_body_target Hbody_package env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_height;
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
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hexact_body_target Hbody_package env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_height;
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



Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_check_provider :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true.
Proof.
  intros env Hcheck f_component Hin_component.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
    in Hcheck.
  eapply (proj1 (forallb_forall
    (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env)
    (env_fns env)) Hcheck); exact Hin_component.
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
  destruct (check_env_end2end_direct_receiver_mixed_ready env_checked &&
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env_checked) eqn:Hgate; try discriminate.
  apply andb_true_iff in Hgate as [Hmixed_ready _Hlocal_check].
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

Lemma typed_env_roots_direct_call_inv :
  forall env Omega n R Sigma fname args T Sigma' R' roots,
    typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R'
      roots ->
    exists fdef sigma arg_roots,
      In fdef (env_fns env) /\
      fn_name fdef = fname /\
      fn_captures fdef = [] /\
      fn_type_params fdef = 0 /\
      typed_args_roots env Omega n R Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' R' arg_roots /\
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) /\
      T = apply_lt_ty sigma (fn_ret fdef) /\
      roots = root_sets_union arg_roots.
Proof.
  intros env Omega n R Sigma fname args T Sigma' R' roots Htyped.
  dependent destruction Htyped.
  exists fdef, σ, arg_roots.
  repeat split; try eassumption; reflexivity.
Qed.

Definition fn_root_shadow_ready_body_or_narrow_summary_evidence_at
    (env : global_env) (fname : ident) : Prop :=
  forall fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary env fdef \/
    callee_body_root_shadow_summary env fdef \/
    callee_body_root_shadow_store_safe_narrow_summary env fdef.

Lemma fn_root_shadow_ready_body_or_narrow_summary_evidence_at_of_synthetic_at :
  forall env fname,
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at env fname ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at env fname.
Proof.
  intros env fname Hsynthetic fdef Hlookup.
  left. eapply Hsynthetic. exact Hlookup.
Qed.

Lemma fn_root_shadow_ready_body_or_narrow_summary_evidence_at_of_shadow_at :
  forall env fname,
    fn_root_shadow_summary_evidence_at env fname ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at env fname.
Proof.
  intros env fname Hsummary fdef Hlookup.
  right. left. eapply Hsummary. exact Hlookup.
Qed.

Lemma fn_root_shadow_ready_body_or_narrow_summary_evidence_at_of_narrow_at :
  forall env fname,
    (forall fdef,
      lookup_fn fname (env_fns env) = Some fdef ->
      callee_body_root_shadow_store_safe_narrow_summary env fdef) ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at env fname.
Proof.
  intros env fname Hnarrow fdef Hlookup.
  right. right. eapply Hnarrow. exact Hlookup.
Qed.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
    (env : global_env) : Prop :=
  forall s fname args s' v n_call,
    eval env s (ECall fname args) s' v ->
    direct_call_eval_height env s (ECall fname args) s' v n_call ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R'
        roots ->
      fn_env_unique_by_name env ->
      fn_root_shadow_ready_body_or_narrow_summary_evidence_at env fname ->
      value_has_type env s' v T.

Definition eval_preserves_typing_roots_store_safe_narrow_summary_at_prefix_call_statement_evidence_at_height_statement
    : Prop :=
  forall env s fname args s' v n_call,
    eval env s (ECall fname args) s' v ->
    direct_call_eval_height env s (ECall fname args) s' v n_call ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R'
        roots ->
      fn_env_unique_by_name env ->
      forall fdef sigma arg_roots,
        In fdef (env_fns env) ->
        fn_name fdef = fname ->
        fn_captures fdef = [] ->
        fn_type_params fdef = 0 ->
        typed_args_roots env Omega n R Sigma args
          (apply_lt_params sigma (fn_params fdef)) Sigma' R' arg_roots ->
        roots = root_sets_union arg_roots ->
        Forall (fun '(a, b) => outlives Omega a b)
          (apply_lt_outlives sigma (fn_outlives fdef)) ->
        callee_body_root_shadow_store_safe_narrow_summary env fdef ->
        store_typed_prefix env s' Sigma' /\
        value_has_type env s' v (apply_lt_ty sigma (fn_ret fdef)) /\
        store_ref_targets_preserved env s s' /\
        store_roots_within R' s' /\
        value_roots_within roots v /\
        store_no_shadow s' /\
        root_env_no_shadow R'.

Theorem eval_preserves_typing_roots_store_safe_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_package :
  eval_preserves_typing_roots_store_safe_narrow_summary_at_prefix_call_statement_evidence_at_height_statement.
Proof.
  intros env s fname args s' v n_call Heval_call _Hheight_call Omega n R
    Sigma T Sigma' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Htyped Hunique fdef sigma arg_roots Hin_fdef
    Hname_fdef Hcaps_fdef Htype_params Htyped_args Hroots_eq Houtlives
    Hnarrow.
  pose proof (eval_direct_call_store_safe_narrow_summary_package_prefix_named
    env Omega n R Sigma fname args sigma Sigma' R' arg_roots s s' v fdef
    Hsafe_args Hnarrow Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef Hcaps_fdef
    Htype_params Htyped_args Houtlives) as Hpkg.
  repeat split.
  - exact (generic_direct_call_package_store _ _ _ _ _ _ _ _ Hpkg).
  - exact (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg).
  - exact (generic_direct_call_package_preserved _ _ _ _ _ _ _ _ Hpkg).
  - exact (generic_direct_call_package_roots _ _ _ _ _ _ _ _ Hpkg).
  - rewrite Hroots_eq.
    exact (generic_direct_call_package_value_roots _ _ _ _ _ _ _ _ Hpkg).
  - exact (generic_direct_call_package_shadow _ _ _ _ _ _ _ _ Hpkg).
  - exact (generic_direct_call_package_root_shadow _ _ _ _ _ _ _ _ Hpkg).
Qed.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_cleanup_summary_at_prefix_call_statement_evidence_at_height_statement
    : Prop :=
  forall env s fname args s' v n_call,
    eval env s (ECall fname args) s' v ->
    direct_call_eval_height env s (ECall fname args) s' v n_call ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R'
        roots ->
      fn_env_unique_by_name env ->
      fn_root_shadow_ready_body_or_narrow_summary_evidence_at env fname ->
      store_typed_prefix env s' Sigma' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family
    (env_family : global_env -> Prop) : Prop :=
  forall env,
    env_family env ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
    (base : global_env) : Prop :=
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family
    (global_env_local_bounds_family base).

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement
    : Prop :=
  forall env,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement
    : Prop :=
  forall env fname fdef fcall used used' s_args s_body vs ret R_args
      arg_roots fname_body args_body T_body Gamma_out R_body roots_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, ECall fname_body args_body) ->
    store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body ->
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out) R_body
      roots_body ->
    fn_env_unique_by_name (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_function_closure_targets_summary
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args) ->
    eval (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret ->
    forall n_body_call,
    direct_call_eval_height
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret n_body_call ->
    value_has_type (global_env_with_local_bounds env (fn_bounds fcall))
      s_body ret T_body.


Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement
    : Prop :=
  forall env fname fdef fcall used used' s_args s_body vs ret R_args
      arg_roots fname_body args_body T_body Gamma_out R_body roots_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, ECall fname_body args_body) ->
    store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body ->
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out) R_body
      roots_body ->
    fn_env_unique_by_name (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_function_closure_targets_summary
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args) ->
    eval (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret ->
    forall n_body_call,
    direct_call_eval_height
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret n_body_call ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      s_body (sctx_of_ctx Gamma_out) /\
    value_has_type (global_env_with_local_bounds env (fn_bounds fcall))
      s_body ret T_body /\
    store_ref_targets_preserved
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args) s_body /\
    store_roots_within R_body s_body /\
    value_roots_within roots_body ret /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_of_cleanup_callback :
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement.
Proof.
  intros Hcleanup.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement
    in *.
  intros env fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  destruct (Hcleanup env fname fdef fcall used used' s_args s_body vs ret
    R_args arg_roots fname_body args_body T_body Gamma_out R_body roots_body
    Hin Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight)
    as [_ [Hv _]].
  exact Hv.
Qed.


Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family
    (env_family : global_env -> Prop) : Prop :=
  forall env,
    env_family env ->
  forall fname fdef fcall used used' s_args s_body vs ret R_args
      arg_roots fname_body args_body T_body Gamma_out R_body roots_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, ECall fname_body args_body) ->
    store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body ->
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out) R_body
      roots_body ->
    fn_env_unique_by_name (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_function_closure_targets_summary
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args) ->
    eval (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret ->
    forall n_body_call,
    direct_call_eval_height
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret n_body_call ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      s_body (sctx_of_ctx Gamma_out) /\
    value_has_type (global_env_with_local_bounds env (fn_bounds fcall))
      s_body ret T_body /\
    store_ref_targets_preserved
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args) s_body /\
    store_roots_within R_body s_body /\
    value_roots_within roots_body ret /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family
    (base : global_env) : Prop :=
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family
    (global_env_local_bounds_family base).

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family_of_statement :
  forall env_family,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family
      env_family.
Proof.
  intros env_family Hcleanup env _Henv.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family
    in *.
  intros fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  eapply Hcleanup; eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family_of_statement :
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros base Hcleanup.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family_of_statement.
  exact Hcleanup.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_of_route :
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement.
Proof.
  intros Hroute.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement
    in *.
  intros env fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  eapply Hroute; eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_of_cleanup_route :
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_cleanup_summary_at_prefix_call_statement_evidence_at_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement.
Proof.
  intros Hroute.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_cleanup_summary_at_prefix_call_statement_evidence_at_height_statement,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement
    in *.
  intros env fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  eapply Hroute; eassumption.
Qed.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
    (env_family : global_env -> Prop) : Prop :=
  forall env,
    env_family env ->
  forall fname fdef fcall used used' s_args s_body vs ret R_args
      arg_roots fname_body args_body T_body Gamma_out R_body roots_body,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, ECall fname_body args_body) ->
    store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body ->
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out) R_body
      roots_body ->
    fn_env_unique_by_name (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_function_closure_targets_summary
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args) ->
    eval (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret ->
    forall n_body_call,
    direct_call_eval_height
      (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (ECall fname_body args_body) s_body ret n_body_call ->
    value_has_type (global_env_with_local_bounds env (fn_bounds fcall))
      s_body ret T_body.

Definition eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
    (base : global_env) : Prop :=
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
    (global_env_local_bounds_family base).


Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family_of_cleanup_callback_family :
  forall env_family,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family
      env_family ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
      env_family.
Proof.
  intros env_family Hcleanup.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_env_family,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
    in *.
  intros env Henv fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  destruct (Hcleanup env Henv fname fdef fcall used used' s_args s_body vs
    ret R_args arg_roots fname_body args_body T_body Gamma_out R_body
    roots_body Hin Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call
    Hheight) as [_ [Hv _]].
  exact Hv.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_cleanup_callback_family :
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family
      base ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros base Hcleanup.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family_of_cleanup_callback_family.
  exact Hcleanup.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family_of_statement :
  forall env_family,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
      env_family.
Proof.
  intros env_family Hcallback env _Henv.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
    in *.
  intros fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  eapply Hcallback; eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_statement :
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros base Hcallback.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family_of_statement.
  exact Hcallback.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_route :
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros base Hroute.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_statement.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_of_route.
  exact Hroute.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family_of_route_family :
  forall env_family,
    (forall env bounds,
      env_family env ->
      env_family (global_env_with_local_bounds env bounds)) ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family
      env_family ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family
      env_family.
Proof.
  intros env_family Henv_family_step Hroute.
  unfold
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family.
  intros env Henv fname fdef fcall used used' s_args s_body vs ret R_args
    arg_roots fname_body args_body T_body Gamma_out R_body roots_body Hin
    Hname Hrename Htarget Hsafe_args Htyped Hunique Hmixed_at Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval n_body_call Hheight.
  eapply Hroute.
  - eapply Henv_family_step. exact Henv.
  - exact Heval.
  - exact Hheight.
  - exact Hsafe_args.
  - exact Hstore.
  - exact Hroots.
  - exact Hshadow.
  - exact Hrn.
  - exact Hnamed.
  - exact Hkeys.
  - exact Hsummary.
  - exact Htyped.
  - exact Hunique.
  - exact Hmixed_at.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_route_family :
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros base Hroute.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_env_family_of_route_family.
  - intros env bounds Henv.
    eapply global_env_local_bounds_family_with_local_bounds. exact Henv.
  - exact Hroute.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_statement :
  forall env,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env.
Proof.
  intros env Hroute.
  eapply Hroute.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family_of_statement :
  forall env_family,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family
      env_family.
Proof.
  intros env_family Hroute env _Henv.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_statement.
  exact Hroute.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_statement :
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros base Hroute.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family_of_statement.
  exact Hroute.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_family :
  forall env_family env,
    env_family env ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_family
      env_family ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env.
Proof.
  intros env_family env Henv Hroute.
  eapply Hroute. exact Henv.
Qed.

Theorem eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route env s fname
    args s' v n_call Heval_call Hheight_call Omega n R Sigma T Sigma' R'
    roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Htyped Hunique Hmixed_at.
  destruct (typed_env_roots_direct_call_inv
    env Omega n R Sigma fname args T Sigma' R' roots Htyped)
    as (fdef & sigma & arg_roots & Hin_fdef & Hname_fdef & Hcaps_fdef &
        Htype_params & Htyped_args & Houtlives & HT & Hroots_eq).
  assert (Hlookup : lookup_fn fname (env_fns env) = Some fdef).
  { eapply lookup_fn_in_unique_by_name; eassumption. }
  destruct (Hmixed_at fdef Hlookup) as [Hsynthetic | [Hsummary | Hnarrow]].
  - assert (Hsynthetic_at :
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsynthetic. }
    pose proof
      (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsynthetic_at Hunique)
      as Hevidence_at.
    eapply Hsynthetic_route; eassumption.
  - assert (Hsummary_at : fn_root_shadow_summary_evidence_at env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsummary. }
    pose proof
      (direct_call_callee_body_root_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsummary_at Hunique)
      as Hevidence_at.
    eapply Hshadow_route; eassumption.
  - rewrite HT.
    eapply eval_direct_call_store_safe_narrow_summary_value_prefix_named;
      eassumption.
Qed.



Theorem eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_evidence_at_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route env s fname
    args s' v n_call Heval_call _Hheight_call Omega n R Sigma T Sigma' R'
    roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Htyped Hunique Hmixed_at.
  destruct (typed_env_roots_direct_call_inv
    env Omega n R Sigma fname args T Sigma' R' roots Htyped)
    as (fdef & sigma & arg_roots & Hin_fdef & Hname_fdef & Hcaps_fdef &
        Htype_params & Htyped_args & Houtlives & HT & Hroots_eq).
  assert (Hlookup : lookup_fn fname (env_fns env) = Some fdef).
  { eapply lookup_fn_in_unique_by_name; eassumption. }
  destruct (Hmixed_at fdef Hlookup) as [Hsynthetic | [Hsummary | Hnarrow]].
  - assert (Hsynthetic_at :
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsynthetic. }
    pose proof
      (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsynthetic_at Hunique)
      as Hevidence_at.
    eapply Hsynthetic_route; eassumption.
  - assert (Hsummary_at : fn_root_shadow_summary_evidence_at env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsummary. }
    pose proof
      (direct_call_callee_body_root_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsummary_at Hunique)
      as Hevidence_at.
    eapply Hshadow_route; eassumption.
  - rewrite HT.
    eapply eval_direct_call_store_safe_narrow_summary_value_prefix_named;
      eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_synthetic_and_shadow_route_families :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall base,
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base ->
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hroot_names Hroot_keys base Hsynthetic_route Hshadow_route env
    Hfamily s fname args s' v n_call Heval_call Hheight_call Omega n R Sigma
    T Sigma' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary_store Htyped Hunique Hmixed_at.
  destruct (typed_env_roots_direct_call_inv
    env Omega n R Sigma fname args T Sigma' R' roots Htyped)
    as (fdef & sigma & arg_roots & Hin_fdef & Hname_fdef & Hcaps_fdef &
        Htype_params & Htyped_args & Houtlives & HT & Hroots_eq).
  assert (Hlookup : lookup_fn fname (env_fns env) = Some fdef).
  { eapply lookup_fn_in_unique_by_name; eassumption. }
  destruct (Hmixed_at fdef Hlookup) as [Hsynthetic | [Hsummary | Hnarrow]].
  - assert (Hsynthetic_at :
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsynthetic. }
    pose proof
      (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsynthetic_at Hunique)
      as Hevidence_at.
    eapply Hsynthetic_route; eassumption.
  - assert (Hsummary_at : fn_root_shadow_summary_evidence_at env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsummary. }
    pose proof
      (direct_call_callee_body_root_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsummary_at Hunique)
      as Hevidence_at.
    eapply Hshadow_route; eassumption.
  - rewrite HT.
    eapply eval_direct_call_store_safe_narrow_summary_value_prefix_named;
      eassumption.
Qed.

Theorem eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_cleanup_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_shadow_and_narrow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  eval_preserves_typing_roots_store_safe_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_cleanup_summary_at_prefix_call_statement_evidence_at_height_statement.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route Hnarrow_route
    env s fname args s' v n_call Heval_call Hheight_call Omega n R Sigma T
    Sigma' R' roots Hsafe_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary_store Htyped Hunique Hmixed_at.
  destruct (typed_env_roots_direct_call_inv
    env Omega n R Sigma fname args T Sigma' R' roots Htyped)
    as (fdef & sigma & arg_roots & Hin_fdef & Hname_fdef & Hcaps_fdef &
        Htype_params & Htyped_args & Houtlives & HT & Hroots_eq).
  assert (Hlookup : lookup_fn fname (env_fns env) = Some fdef).
  { eapply lookup_fn_in_unique_by_name; eassumption. }
  destruct (Hmixed_at fdef Hlookup) as [Hsynthetic | [Hsummary | Hnarrow]].
  - assert (Hsynthetic_at :
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsynthetic. }
    pose proof
      (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsynthetic_at Hunique)
      as Hevidence_at.
    eapply Hsynthetic_route; eassumption.
  - assert (Hsummary_at : fn_root_shadow_summary_evidence_at env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fdef) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsummary. }
    pose proof
      (direct_call_callee_body_root_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys env fname Hsummary_at Hunique)
      as Hevidence_at.
    eapply Hshadow_route; eassumption.
  - rewrite HT.
    eapply Hnarrow_route; eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_of_route.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_and_shadow_routes;
    eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_of_synthetic_shadow_and_narrow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_of_cleanup_route.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_cleanup_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_shadow_and_narrow_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hsynthetic_route.
  - exact Hshadow_route.
  - exact eval_preserves_typing_roots_store_safe_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_package.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family_of_synthetic_shadow_and_narrow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route base.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family_of_statement.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_of_synthetic_shadow_and_narrow_routes;
    eassumption.
Qed.

Lemma eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  forall base,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
      base.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route base.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_statement.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_of_synthetic_and_shadow_routes;
    eassumption.
Qed.

Definition mixed_ready_body_or_narrow_value_cleanup_bridge_statement : Prop :=
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement.


Theorem mixed_ready_body_or_narrow_value_cleanup_bridge_statement_of_synthetic_branch_route :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  mixed_ready_body_or_narrow_value_cleanup_bridge_statement.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_and_shadow_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hsynthetic_route.
  - intros env.
    eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_provenance_ready_with_callee_summary.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hframe_ready.
    + exact Hprefix_ready.
    + exact Hparam_ready.
Qed.


Theorem mixed_ready_body_or_narrow_value_cleanup_bridge_statement_of_synthetic_evidence_at_route :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  mixed_ready_body_or_narrow_value_cleanup_bridge_statement.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_evidence_at_and_shadow_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hsynthetic_route.
  - intros env.
    eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_provenance_ready_with_callee_summary.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hframe_ready.
    + exact Hprefix_ready.
    + exact Hparam_ready.
Qed.

Definition component_body_local_bounds_synthetic_summary_check_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    check_env_root_shadow_synthetic_direct_call_ready_summary
      (global_env_with_local_bounds env (fn_bounds f_component)) = true.

Definition component_body_local_bounds_ready_body_summary_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    env_fns_root_shadow_ready_body_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_ready_body_route_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_ready_body_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_shadow_summary_route_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_mixed_route_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)) /\
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_cleanup_callback_provider :
  forall env,
    component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.
Proof.
  intros env Hprovider f_component Hin Hcheck.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_cleanup_callback_family.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_of_statement :
  forall env,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
    component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_in_env
      env.
Proof.
  intros env Hcleanup f_component _Hin_component _Hcomponent_check.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_in_local_bounds_family_of_statement.
  exact Hcleanup.
Qed.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_route_provider :
  forall env,
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.
Proof.
  intros env Hprovider f_component Hin Hcheck.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_value_callback_height_statement_in_local_bounds_family_of_route_family.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_statement :
  forall env,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.
Proof.
  intros env Hroute f_component _Hin_component _Hcomponent_check.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_statement.
  exact Hroute.
Qed.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  forall env,
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route env.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_statement.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_and_shadow_routes;
    eassumption.
Qed.


Lemma component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_mixed_route_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    component_body_local_bounds_mixed_route_provider_in_env env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.
Proof.
  intros Hroot_names Hroot_keys env Hprovider f_component Hin_component
    Hcomponent_check.
  destruct (Hprovider f_component Hin_component Hcomponent_check)
    as [Hsynthetic_route Hshadow_route].
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_synthetic_and_shadow_route_families;
    eassumption.
Qed.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  forall env,
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route env.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_route_provider.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_synthetic_and_shadow_routes;
    eassumption.
Qed.

Lemma component_body_local_bounds_mixed_route_provider_synthetic :
  forall env,
    component_body_local_bounds_mixed_route_provider_in_env env ->
    forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component)).
Proof.
  intros env Hprovider f_component Hin Hcheck.
  exact (proj1 (Hprovider f_component Hin Hcheck)).
Qed.

Lemma component_body_local_bounds_mixed_route_provider_shadow :
  forall env,
    component_body_local_bounds_mixed_route_provider_in_env env ->
    forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component)).
Proof.
  intros env Hprovider f_component Hin Hcheck.
  exact (proj2 (Hprovider f_component Hin Hcheck)).
Qed.

Lemma component_body_local_bounds_mixed_route_provider_of_synthetic_and_provenance_ready :
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env,
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component))) ->
    component_body_local_bounds_mixed_route_provider_in_env env.
Proof.
  intros Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready env
    Hsynthetic_provider f_component Hin_component Hcomponent_check.
  split.
  - eapply Hsynthetic_provider; eassumption.
  - eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_provenance_ready_with_callee_summary.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hframe_ready.
    + exact eval_preserves_typing_roots_ready_prefix_mutual.
    + exact Hparam_ready.
Qed.

Definition component_body_local_bounds_narrow_summary_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    env_fns_root_shadow_store_safe_narrow_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
    (env : global_env) : Prop :=
  forall f_component fname fdef,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    lookup_fn fname
      (env_fns (global_env_with_local_bounds env (fn_bounds f_component))) =
      Some fdef ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary
      (global_env_with_local_bounds env (fn_bounds f_component)) fdef \/
    callee_body_root_shadow_summary
      (global_env_with_local_bounds env (fn_bounds f_component)) fdef \/
    callee_body_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env (fn_bounds f_component)) fdef.

Definition mixed_ready_body_or_narrow_summary_provider_route_bridge : Prop :=
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_summary_route_bridge :
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.
Proof.
  intros Hbridge env Hprovider.
  eapply Hbridge.
  exact Hprovider.
Qed.

Lemma mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route env _Hprovider.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_synthetic_and_shadow_routes;
    eassumption.
Qed.


Lemma mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_evidence_at_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route env _Hprovider.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_statement.
  eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_of_synthetic_evidence_at_and_shadow_routes;
    eassumption.
Qed.


Lemma mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_evidence_at_prefix_route_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge.
Proof.
  intros Hroot_names Hroot_keys Hsynthetic_route Hshadow_route.
  eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_evidence_at_and_shadow_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_summary_at_prefix_call_statement_evidence_at.
    exact Hsynthetic_route.
  - exact Hshadow_route.
Qed.

Lemma mixed_ready_body_or_narrow_summary_provider_route_bridge_of_exact_body_call_route_package :
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
  mixed_ready_body_or_narrow_summary_provider_route_bridge.
Proof.
  intros Hscope_synthetic Htyping_prefix Hprefix_ready Hroots_ready
    Hroot_names Hroot_keys Hexact_body_target Hbody_package.
  eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_and_shadow_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_of_exact_body_call_route_package.
    + exact Hscope_synthetic.
    + exact Htyping_prefix.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hexact_body_target.
    + exact Hbody_package.
  - intros env0.
    eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_provenance_ready_with_callee_summary.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact eval_preserves_frame_scope_roots_ready_mutual.
    + exact Hprefix_ready.
    + exact eval_preserves_param_scope_roots_ready_mutual.
Qed.

Lemma mixed_ready_body_or_narrow_summary_provider_route_bridge_of_prefix_statement_and_synthetic_shadow_summary_at_all :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  (forall env fname,
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env fname) ->
  (forall env,
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env
      env) ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge.
Proof.
  intros Hprefix Hroot_names Hroot_keys Hsummary_at_all Hshadow_route.
  eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_evidence_at_and_shadow_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_prefix_statement_and_shadow_summary_at_all;
      eassumption.
  - exact Hshadow_route.
Qed.

Lemma component_body_local_bounds_ready_body_or_narrow_summary_provider_evidence_at :
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    forall f_component fname,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      fn_root_shadow_ready_body_or_narrow_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f_component)) fname.
Proof.
  intros env Hprovider f_component fname Hin_component Hcomponent_check
    fdef Hlookup.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_ready_body_or_narrow_summary_provider_alpha_body_callback :
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    forall fname fdef fcall used used' fname_body args_body synthetic_body,
      In fdef (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env fdef = true ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_ready_body_or_narrow_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds fcall)) fname_body.
Proof.
  intros env Hprovider fname fdef fcall used used' fname_body args_body
    synthetic_body Hin_component Hcomponent_check _Hname Hrename _Htarget.
  destruct (alpha_rename_fn_def_static_fields used fdef fcall used' Hrename)
    as [_ [_ [_ [_ [_ [_ Hbounds]]]]]].
  rewrite Hbounds.
  eapply component_body_local_bounds_ready_body_or_narrow_summary_provider_evidence_at;
    eassumption.
Qed.

Definition component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
    (env : global_env) : Prop :=
  forall fname fdef fcall used used' fname_body args_body synthetic_body,
    In fdef (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef = true ->
    fn_name fdef = fname ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body.

Lemma component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_of_summary_provider :
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env.
Proof.
  intros env Hprovider fname fdef fcall used used' fname_body args_body
    synthetic_body Hin_component Hcomponent_check Hname Hrename Htarget.
  eapply component_body_local_bounds_ready_body_or_narrow_summary_provider_alpha_body_callback;
    eassumption.
Qed.

Definition mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge : Prop :=
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_alpha_summary_route_bridge :
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env.
Proof.
  intros Hbridge env Hprovider Halpha_provider.
  eapply Hbridge; eassumption.
Qed.

Lemma mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge :
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge.
Proof.
  intros Hbridge env Hprovider _Halpha_provider.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_summary_route_bridge;
    eassumption.
Qed.

Definition mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge : Prop :=
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.

Lemma component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_alpha_summary_value_callback_bridge :
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge ->
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.
Proof.
  intros Hbridge env Hprovider Halpha_provider.
  eapply Hbridge; eassumption.
Qed.

Lemma mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_alpha_route_bridge :
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge.
Proof.
  intros Hbridge env Hprovider Halpha_provider.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_route_provider.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_alpha_summary_route_bridge;
    eassumption.
Qed.

Lemma mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge :
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge.
Proof.
  intros Hbridge.
  eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_alpha_route_bridge.
  eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
  exact Hbridge.
Qed.

Definition mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge : Prop :=
  forall env,
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env /\
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.

Lemma mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge_of_alpha_bridges :
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge ->
  mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge.
Proof.
  intros Hroute_bridge Hvalue_bridge env Hprovider.
  assert (Halpha_provider :
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env).
  { eapply component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_of_summary_provider.
    exact Hprovider. }
  split.
  - eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_alpha_summary_route_bridge;
      eassumption.
  - eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_alpha_summary_value_callback_bridge;
      eassumption.
Qed.

Lemma mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge_of_summary_route_bridge :
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge.
Proof.
  intros Hbridge.
  eapply mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge_of_alpha_bridges.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
    exact Hbridge.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge.
    exact Hbridge.
Qed.

Lemma component_body_local_bounds_narrow_summary_provider_of_env_summary :
  forall env,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_narrow_summary_evidence env ->
    component_body_local_bounds_narrow_summary_provider_in_env env.
Proof.
  intros env Hunique Hsummary f_component _Hin_component _Hcomponent_check.
  eapply env_fns_root_shadow_store_safe_narrow_summary_evidence_global_env_with_local_bounds;
    eassumption.
Qed.

Lemma check_env_root_shadow_no_receiver_component_narrow_summary_provider_check_sound :
  forall env,
    fn_env_unique_by_name env ->
    check_env_root_shadow_no_receiver_component_narrow_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_narrow_summary_provider_in_env env.
Proof.
  intros env Hunique Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_narrow_summary_provider_check
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  eapply component_body_local_bounds_narrow_summary_provider_of_env_summary.
  - exact Hunique.
  - eapply check_env_root_shadow_store_safe_narrow_summary_sound.
    exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_local_bounds_narrow_summary_sound :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_local_bounds_narrow_summary
      env = true ->
    component_body_local_bounds_narrow_summary_provider_in_env env.
Proof.
  intros env Hcheck f_component Hin_component Hcomponent_check.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_local_bounds_narrow_summary
    in Hcheck.
  pose proof (proj1 (forallb_forall
    (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_local_bounds_narrow_summary
      env)
    (env_fns env)) Hcheck f_component Hin_component) as Hlocal_check.
  unfold check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_local_bounds_narrow_summary
    in Hlocal_check.
  rewrite Hcomponent_check in Hlocal_check.
  eapply check_env_root_shadow_store_safe_narrow_summary_sound.
  exact Hlocal_check.
Qed.

Lemma check_env_root_shadow_no_receiver_component_local_bounds_narrow_summary_provider_check_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_local_bounds_narrow_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_narrow_summary_provider_in_env env.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_local_bounds_narrow_summary_provider_check
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_local_bounds_narrow_summary_sound.
  exact Hcheck.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_narrow_summary_provider_of_no_receiver_component_narrow_summary_provider_check :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_narrow_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_narrow_summary_provider_in_env env'.
Proof.
  intros env env' Hprog Hcheck Hno_receiver.
  eapply check_env_root_shadow_no_receiver_component_narrow_summary_provider_check_sound.
  - eapply infer_program_env_end2end_assoc_unique_by_name.
    eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
    exact Hprog.
  - exact Hcheck.
  - exact Hno_receiver.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_narrow_callee_at_provider_of_no_receiver_component_narrow_summary_provider_check :
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_narrow_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_narrow_callee_at_provider
      env' f_component.
Proof.
  intros env env' f_component Hprog Hcheck Hno_receiver Hin_component
    Hcomponent_check fname args synthetic_body fdef _Htarget Hlookup.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_narrow_summary_provider_of_no_receiver_component_narrow_summary_provider_check;
    eassumption.
Qed.

Definition shadow_summary_local_bounds_family_route_bridge : Prop :=
  forall base,
    env_fns_root_shadow_summary_evidence base ->
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.



Lemma direct_call_callee_body_root_ready_body_evidence_at_of_shadow_summary_local_bounds_family :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall base,
    env_fns_root_shadow_summary_evidence base ->
    forall env fname,
      global_env_local_bounds_family base env ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_ready_body_evidence_at env fname.
Proof.
  intros Hroot_names Hroot_keys base Hsummary_base env fname Hfamily Hunique.
  eapply direct_call_callee_body_root_ready_body_evidence_at_of_shadow_summary.
  - exact Hroot_names.
  - exact Hroot_keys.
  - destruct Hfamily as [bounds ->].
    eapply env_fns_root_shadow_summary_evidence_global_env_with_local_bounds_for_route.
    exact Hsummary_base.
  - exact Hunique.
Qed.

Lemma component_body_local_bounds_shadow_summary_route_provider_of_env_summary :
  shadow_summary_local_bounds_family_route_bridge ->
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env.
Proof.
  intros Hbridge env Hsummary f_component _Hin_component _Hcomponent_check.
  eapply Hbridge.
  eapply env_fns_root_shadow_summary_evidence_global_env_with_local_bounds_for_route.
  exact Hsummary.
Qed.

Lemma check_env_root_shadow_summary_evidence_of_provenance_and_preservation_checks :
  forall env,
    check_env_root_shadow_provenance_summary env = true ->
    check_env_preservation_ready env = true ->
    env_fns_root_shadow_summary_evidence env.
Proof.
  intros env Hprov_check Hpres_check.
  eapply env_fns_root_shadow_summary_evidence_of_provenance_and_preservation.
  - eapply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
    eapply check_env_root_shadow_provenance_summary_ready.
    exact Hprov_check.
  - eapply check_env_preservation_ready_sound.
    exact Hpres_check.
Qed.

Definition ready_body_summary_local_bounds_family_route_bridge : Prop :=
  forall base,
    env_fns_root_shadow_ready_body_summary_evidence base ->
    eval_preserves_typing_roots_store_safe_ready_body_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.

Definition ready_body_summary_local_bounds_family_mixed_route_bridge : Prop :=
  forall base,
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base ->
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base ->
    eval_preserves_typing_roots_store_safe_ready_body_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      base.

Lemma ready_body_summary_local_bounds_family_mixed_route_bridge_of_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_mixed_route_bridge.
Proof.
  intros Hroot_names Hroot_keys base Hsynthetic Hordinary.
  eapply eval_preserves_typing_roots_store_safe_ready_body_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_synthetic_or_shadow_summary;
    eassumption.
Qed.

Lemma shadow_summary_local_bounds_family_route_bridge_of_ready_body_route_bridge :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  shadow_summary_local_bounds_family_route_bridge.
Proof.
  intros Hroot_names Hroot_keys Hready_bridge base Hsummary.
  eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_ready_body_in_local_bounds_family.
  - exact Hroot_names.
  - exact Hroot_keys.
  - eapply Hready_bridge.
    eapply env_fns_root_shadow_ready_body_summary_evidence_of_summary.
    exact Hsummary.
Qed.

Lemma component_body_local_bounds_ready_body_route_provider_of_summary_provider :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env,
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    component_body_local_bounds_ready_body_route_provider_in_env env.
Proof.
  intros Hbridge env Hprovider f_component Hin_component Hcomponent_check.
  eapply Hbridge.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_ready_body_route_provider_of_synthetic_and_shadow_route_providers :
  ready_body_summary_local_bounds_family_mixed_route_bridge ->
  forall env,
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env ->
    component_body_local_bounds_ready_body_route_provider_in_env env.
Proof.
  intros Hbridge env Hsynthetic_provider Hshadow_provider f_component
    Hin_component Hcomponent_check.
  eapply Hbridge.
  - eapply Hsynthetic_provider; eassumption.
  - eapply Hshadow_provider; eassumption.
Qed.

Definition component_body_local_bounds_ready_body_callback_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Definition component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
    (env : global_env) : Prop :=
  forall f_component,
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).

Lemma component_body_local_bounds_synthetic_route_provider_of_ready_body_route_provider :
  forall env,
    component_body_local_bounds_ready_body_route_provider_in_env env ->
    forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component)).
Proof.
  intros env Hprovider f_component Hin_component Hcomponent_check.
  eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_ready_body_in_local_bounds_family.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_ready_body_callback_provider_of_route_provider :
  forall env,
    component_body_local_bounds_ready_body_route_provider_in_env env ->
    component_body_local_bounds_ready_body_callback_provider_in_env env.
Proof.
  intros env Hprovider f_component Hin_component Hcomponent_check.
  eapply eval_preserves_typing_roots_store_safe_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family_of_summary_at_prefix_call_statement_evidence_at_height.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_synthetic_ready_body_callback_provider_of_ready_body_callback_provider :
  forall env,
    component_body_local_bounds_ready_body_callback_provider_in_env env ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env.
Proof.
  intros env Hprovider f_component Hin_component Hcomponent_check.
  eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_in_local_bounds_family_of_ready_body_in_local_bounds_family.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_synthetic_ready_body_callback_provider_of_route_provider :
  forall env,
    component_body_local_bounds_ready_body_route_provider_in_env env ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env.
Proof.
  intros env Hprovider.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_ready_body_callback_provider.
  eapply component_body_local_bounds_ready_body_callback_provider_of_route_provider.
  exact Hprovider.
Qed.

Lemma strict_exact_closure_component_body_store_safe_callback_at_provider_of_synthetic_ready_body_callback_provider :
  forall env f_component,
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env f_component.
Proof.
  intros env f_component Hprovider Hin_component Hcomponent_check fname args
    synthetic_body fdef _Htarget _Hlookup.
  eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_body_call_store_safe_callback_height_statement_at_of_in_local_bounds_family.
  - eapply Hprovider; eassumption.
  - apply global_env_local_bounds_family_base.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_at_in :
  forall env,
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    forall f_component fname,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      fn_root_shadow_ready_body_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f_component)) fname.
Proof.
  intros env Hprovider f_component fname Hin Hcheck.
  eapply fn_root_shadow_ready_body_summary_evidence_at_of_env.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_narrow_summary_provider_at_lookup :
  forall env,
    component_body_local_bounds_narrow_summary_provider_in_env env ->
    forall f_component fname fdef,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f_component))) =
        Some fdef ->
      callee_body_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env (fn_bounds f_component)) fdef.
Proof.
  intros env Hprovider f_component fname fdef Hin Hcheck Hlookup.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_narrow_summary_provider_narrow_callee_at_provider :
  forall env f_component,
    component_body_local_bounds_narrow_summary_provider_in_env env ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    strict_exact_closure_component_body_narrow_callee_at_provider
      env f_component.
Proof.
  intros env f_component Hprovider Hin Hcheck fname args synthetic_body fdef
    _Htarget Hlookup.
  eapply component_body_local_bounds_narrow_summary_provider_at_lookup;
    eassumption.
Qed.

Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_of_component_and_local_bounds_narrow_provider :
  forall env f_component,
    fn_env_unique_by_name env ->
    component_body_local_bounds_narrow_summary_provider_in_env env ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary
      env f_component.
Proof.
  intros env f_component Hunique Hprovider Hin_component Hcomponent_check
    Hcomponent.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & Hcaps & Hbody & Htarget &
      Hsynthetic & Hsafe_args & Hin_callee & Hname_callee &
      Hcaps_callee & Hnodup & Htyped & Hcompat & Hroots & Henv_excl).
  pose (body_env := global_env_with_local_bounds env (fn_bounds f_component)).
  assert (Hunique_body : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  assert (Hin_callee_body : In fcallee (env_fns body_env)).
  { subst body_env. simpl. exact Hin_callee. }
  assert (Hlookup : lookup_fn fname (env_fns body_env) = Some fcallee).
  { eapply lookup_fn_in_unique_by_name; eassumption. }
  assert (Hnarrow_callee :
    callee_body_root_shadow_store_safe_narrow_summary body_env fcallee).
  { subst body_env. eapply Hprovider; eassumption. }
  exists fname, args, raw_body, synthetic_body, fcallee, T_body, Gamma_out,
    R_body, roots_body.
  repeat split; try eassumption.
Qed.


Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary Hinitial Hstore Heval.
  destruct Hsummary as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & Hin_callee & Hname_callee &
      _Hcallee_captures & Hcallee_summary_body & Hnodup & Htyped_shadow &
      Hcompat & _Hroots & _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env. apply store_typed_prefix_exact.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Hsummary_store_body_env :
    store_function_closure_targets_summary body_env s).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  pose proof (typed_env_roots_shadow_safe_roots
    body_env (fn_outlives f) (fn_lifetimes f)
    (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
    (ECall fname args) T_body (sctx_of_ctx Gamma_out) R_body roots_body
    Htyped_call_shadow) as Htyped_call.
  dependent destruction Htyped_call.
  assert (fdef = fcallee) as ->.
  { eapply Hunique.
    - exact H.
    - exact Hin_callee.
    - exact (eq_sym Hname_callee). }
  pose proof
    (eval_direct_call_store_safe_narrow_summary_value_prefix_named
      body_env (fn_outlives f) (fn_lifetimes f)
      (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
      (fn_name fcallee) args σ _ _ _ s s' v fcallee
      Hsafe_args_body Hcallee_summary_body Hstore_body_env Hroots
      Hshadow Hrn Hnamed Hkeys Hsummary_store_body_env Heval_call
      Hunique Hin_callee Hname_callee H1 H2 H3 H4) as Hv_body.
  assert (Hv_env :
    value_has_type env s' v (apply_lt_ty σ (fn_ret fcallee))).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv_body. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.



Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_mixed_route_provider :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f)) ->
    In f (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hprovider Hmixed_route Hin_component
    Hcomponent_check Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Hsummary_store_body_env :
    store_function_closure_targets_summary body_env s).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hstore_body_prefix :
    store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
  { eapply store_typed_prefix_exact. exact Hstore_body_env. }
  assert (Hunique_body : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  assert (Hmixed_at :
    fn_root_shadow_ready_body_or_narrow_summary_evidence_at body_env fname).
  { subst body_env.
    eapply component_body_local_bounds_ready_body_or_narrow_summary_provider_evidence_at;
      eassumption. }
  destruct (direct_call_eval_height_exists body_env s (ECall fname args)
    s' v Heval_call) as [n_call Hheight_call].
  pose proof (Hmixed_route body_env
              (global_env_local_bounds_family_base body_env)
              s fname args s' v n_call Heval_call Hheight_call
              (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
              (sctx_of_ctx (fn_body_ctx f)) T_body
              (sctx_of_ctx Gamma_out) R_body roots_body Hsafe_args_body
              Hstore_body_prefix Hroots Hshadow Hrn Hnamed Hkeys
              Hsummary_store_body_env Htyped_call Hunique_body Hmixed_at)
    as Hv_body.
  eapply VHT_Compatible.
  - subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_mixed_ready_body_or_narrow_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f)) ->
    eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f)) ->
    In f (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys env f s s' v Hunique Hprovider
    Hsynthetic_route Hordinary_route Hin_component Hcomponent_check
    Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & Hin_callee & Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hstore_body_prefix :
    store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
  { eapply store_typed_prefix_exact. exact Hstore_body_env. }
  assert (Hunique_body : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  assert (Hin_callee_body : In fcallee (env_fns body_env)).
  { subst body_env. simpl. exact Hin_callee. }
  assert (Hlookup : lookup_fn fname (env_fns body_env) = Some fcallee).
  { subst body_env. eapply lookup_fn_in_unique_by_name; eassumption. }
  destruct (Hprovider f fname fcallee Hin_component Hcomponent_check Hlookup)
    as [Hsynthetic_callee | [Hsummary_callee | Hnarrow_callee]].
  - assert (Hsynthetic_summary_at :
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        body_env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fcallee) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsynthetic_callee. }
    pose proof
      (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys body_env fname Hsynthetic_summary_at
        Hunique_body) as Hsynthetic_evidence_at.
    destruct (direct_call_eval_height_exists body_env s (ECall fname args)
      s' v Heval_call) as [n_call Hheight_call].
    destruct (Hsynthetic_route body_env
                (global_env_local_bounds_family_base body_env)
                s fname args s' v n_call Heval_call Hheight_call
                (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
                (sctx_of_ctx (fn_body_ctx f)) T_body
                (sctx_of_ctx Gamma_out) R_body roots_body
                Hsafe_args_body Hstore_body_prefix Hroots Hshadow Hrn Hnamed
                Hkeys Htyped_call Hunique_body Hsynthetic_summary_at
                Hsynthetic_evidence_at)
      as [_Hstore_body_prefix' [Hv_body [_Hpres_body [_Hroots_body
          [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
    eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
  - assert (Hsummary_at :
      fn_root_shadow_summary_evidence_at body_env fname).
    { intros fdef0 Hlookup0.
      assert (fdef0 = fcallee) as ->.
      { eapply lookup_fn_deterministic; eassumption. }
      exact Hsummary_callee. }
    pose proof
      (direct_call_callee_body_root_evidence_at_of_shadow_summary_at
        Hroot_names Hroot_keys body_env fname Hsummary_at Hunique_body)
      as Hevidence_at.
    destruct (direct_call_eval_height_exists body_env s (ECall fname args)
      s' v Heval_call) as [n_call Hheight_call].
    destruct (Hordinary_route body_env
      (global_env_local_bounds_family_base body_env) s fname args s' v
      n_call Heval_call Hheight_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hsafe_args_body Hstore_body_prefix Hroots Hshadow
      Hrn Hnamed Hkeys Htyped_call Hunique_body Hsummary_at Hevidence_at)
      as [_Hstore_body_prefix' [Hv_body [_Hpres_body [_Hroots_body
          [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
    eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exists fname, args, raw_body, synthetic_body, fcallee, T_body,
        Gamma_out, R_body, roots_body.
      repeat split; try eassumption.
    + exact Hinitial.
    + exact Hstore.
    + rewrite Hbody. exact Heval.
Qed.

Lemma callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_ready_body_or_narrow_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    eval_preserves_typing_roots_store_safe_ready_body_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f)) ->
    In f (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys env f s s' v Hunique Hprovider
    Hready_route Hin_component Hcomponent_check Hcomponent Hinitial Hstore
    Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & Hcaps & Hbody & Htarget &
      Hsynthetic & Hsafe_args & Hin_callee & Hname_callee &
      Hcaps_callee & Hnodup & Htyped & Hcompat & Hroots & Henv_excl).
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hunique_body : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  assert (Hin_callee_body : In fcallee (env_fns body_env)).
  { subst body_env. simpl. exact Hin_callee. }
  assert (Hlookup : lookup_fn fname (env_fns body_env) = Some fcallee).
  { subst body_env. eapply lookup_fn_in_unique_by_name; eassumption. }
  destruct (Hprovider f fname fcallee Hin_component Hcomponent_check Hlookup)
    as [Hsynthetic_callee | [Hsummary_callee | Hnarrow_callee]].
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_ready_body_route_in_local_bounds_family.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hready_route.
    + intros fname0 args0 synthetic_body0 Htarget0 fdef0 Hlookup0.
      pose proof Hname_callee as Hname_callee0.
      assert (Htarget0_raw :
        direct_call_target_expr raw_body =
          Some (fname0, args0, synthetic_body0)).
      { rewrite <- Hbody. exact Htarget0. }
      rewrite Htarget in Htarget0_raw.
      inversion Htarget0_raw; subst.
      assert (fdef0 = fcallee) as ->.
      { eapply lookup_fn_unique_by_name.
        - exact Hlookup0.
        - exact Hin_callee_body.
        - exact Hname_callee0.
        - exact Hunique_body. }
      left. exact Hsynthetic_callee.
    + exists fname, args, raw_body, synthetic_body, fcallee, T_body,
        Gamma_out, R_body, roots_body.
      repeat split; try eassumption.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_ready_body_route_in_local_bounds_family.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hready_route.
    + intros fname0 args0 synthetic_body0 Htarget0 fdef0 Hlookup0.
      pose proof Hname_callee as Hname_callee0.
      assert (Htarget0_raw :
        direct_call_target_expr raw_body =
          Some (fname0, args0, synthetic_body0)).
      { rewrite <- Hbody. exact Htarget0. }
      rewrite Htarget in Htarget0_raw.
      inversion Htarget0_raw; subst.
      assert (fdef0 = fcallee) as ->.
      { eapply lookup_fn_unique_by_name.
        - exact Hlookup0.
        - exact Hin_callee_body.
        - exact Hname_callee0.
        - exact Hunique_body. }
      right. exact Hsummary_callee.
    + exists fname, args, raw_body, synthetic_body, fcallee, T_body,
        Gamma_out, R_body, roots_body.
      repeat split; try eassumption.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exists fname, args, raw_body, synthetic_body, fcallee, T_body,
        Gamma_out, R_body, roots_body.
      repeat split; try eassumption.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_component_ready_body_or_narrow_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_route_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys env f s s' v Hunique Hcombined Hprovider
    Hroute_provider Hcomponent_checks Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent_branch].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - pose proof (Hcomponent_checks f Hin) as Hcomponent_check.
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_ready_body_or_narrow_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hprovider.
    + eapply Hroute_provider; eassumption.
    + exact Hin.
    + exact Hcomponent_check.
    + exact Hcomponent_branch.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_ready_body_or_narrow_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_ready_body_route_provider_in_env env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hprovider Hroute_provider Hinitial Hin Hstore Heval.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined_check.
  apply forallb_forall with (x := f) in Hcombined_check; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined_check.
  apply orb_true_iff in Hcombined_check as [Hcaptured_check | Hcomponent_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_ready_body_or_narrow_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hprovider.
    + eapply Hroute_provider; eassumption.
    + exact Hin.
    + exact Hcomponent_check.
    + apply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      exact Hcomponent_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.



Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_mixed_route_provider :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hcombined_check Hprovider Hroute_provider
    Hinitial Hin Hstore Heval.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined_check.
  apply forallb_forall with (x := f) in Hcombined_check; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined_check.
  apply orb_true_iff in Hcombined_check as [Hcaptured_check | Hcomponent_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_mixed_route_provider.
    + exact Hunique.
    + exact Hprovider.
    + eapply Hroute_provider; eassumption.
    + exact Hin.
    + exact Hcomponent_check.
    + apply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      exact Hcomponent_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_mixed_ready_body_or_narrow_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env ->
    component_body_local_bounds_mixed_route_provider_in_env env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hprovider Hroute_provider Hinitial Hin Hstore Heval.
  unfold check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined_check.
  apply forallb_forall with (x := f) in Hcombined_check; [| exact Hin].
  unfold check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
    in Hcombined_check.
  apply orb_true_iff in Hcombined_check as [Hcaptured_check | Hcomponent_check].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_mixed_ready_body_or_narrow_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hprovider.
    + eapply component_body_local_bounds_mixed_route_provider_synthetic;
        eassumption.
    + eapply component_body_local_bounds_mixed_route_provider_shadow;
        eassumption.
    + exact Hin.
    + exact Hcomponent_check.
    + apply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      exact Hcomponent_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_component_narrow_callee_provider :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_local_bounds_narrow_summary_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hcombined Hprovider Hcomponent_checks
    Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent_branch].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - pose proof (Hcomponent_checks f Hin) as Hcomponent_check.
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + eapply (callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_of_component_and_local_bounds_narrow_provider
        env f).
      * exact Hunique.
      * exact Hprovider.
      * exact Hin.
      * exact Hcomponent_check.
      * exact Hcomponent_branch.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_component_narrow_callee_provider :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_ready
      env ->
    component_body_local_bounds_narrow_summary_provider_in_env env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hstrict Hprovider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hstrict (fn_name f) f Hlookup) as [Hcaptured | Hcomponent_branch].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct Hcomponent_branch as [Hcomponent_check [Hcomponent _Hexact_check]].
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_of_component_and_local_bounds_narrow_provider;
        eassumption.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_narrow_callee_provider :
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
      env = infer_ok env' ->
    component_body_local_bounds_narrow_summary_provider_in_env env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros env env' f s s' v Hprog Hprovider Hinitial Hin Hstore Heval.
  pose proof
    (infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed_base
      env env' Hprog) as Hbase.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_component_narrow_callee_provider.
  - eapply infer_program_env_end2end_assoc_strict_exact_closure_unique_by_name.
    exact Hbase.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    eapply infer_program_env_end2end_assoc_strict_exact_closure_check_env_ready.
    exact Hbase.
  - exact Hprovider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_component_narrow_provider :
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    component_body_local_bounds_narrow_summary_provider_in_env env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros env env' f s s' v Hprog Hprovider Hinitial Hin Hstore Heval.
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
  destruct (check_fn_root_shadow_captured_call_store_safe_summary env' f)
    eqn:Hcaptured_check.
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
      exact Hcaptured_check.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - simpl in Hcheck_env.
    destruct (check_fn_root_shadow_no_capture_direct_call_component_exact_closure_head_sound
                env' f Hcheck_env) as [Hcomponent _Hexact_target].
    assert (Hcomponent_check :
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f = true).
    { unfold check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        in Hcheck_env.
      eapply check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check.
      - exact Hcheck_env.
      - reflexivity. }
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_narrow_callee_summary_of_component_and_local_bounds_narrow_provider.
      * exact Hunique.
      * exact Hprovider.
      * exact Hin.
      * exact Hcomponent_check.
      * exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_narrow_summary_provider_check :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_receiver_component_narrow_summary_provider_check
        env' = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hnarrow_when_no_receiver Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hprovider :
      component_body_local_bounds_narrow_summary_provider_in_env env').
    { eapply infer_program_env_end2end_assoc_direct_receiver_mixed_narrow_summary_provider_of_no_receiver_component_narrow_summary_provider_check.
      - exact Hprog.
      - apply Hnarrow_when_no_receiver.
        exact Hno_receiver.
      - exact Hno_receiver. }
    eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_component_narrow_provider.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog.
    + exact Hprovider.
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

Theorem infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_ready_body_route_component_local_bounds_family :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc env = infer_ok env' ->
    component_body_local_bounds_ready_body_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys env env' f s s' v Hprog
    Hcomponent_route Hcomponent_ready_summary Hinitial Hin Hstore Heval.
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
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_ready_body_route_in_local_bounds_family.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + eapply Hcomponent_route; eassumption.
    + intros fname args synthetic_body _Htarget.
      eapply component_body_local_bounds_ready_body_summary_provider_at_in;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_route_package :
  forall env f_component used fcall used' fname_body args_body synthetic_body,
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    alpha_rename_fn_def used f_component = (fcall, used') ->
    direct_call_target_expr (fn_body fcall) =
      Some (fname_body, args_body, synthetic_body) ->
    fn_root_shadow_ready_body_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fcall)) fname_body /\
    store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body.
Proof.
  intros env f_component used fcall used' fname_body args_body
    synthetic_body Hprovider Hin Hcheck Hrename Htarget.
  destruct (alpha_rename_fn_def_static_fields
    used f_component fcall used' Hrename)
    as (_ & _ & _ & _ & _ & _ & Hbounds).
  split.
  - rewrite Hbounds.
    eapply component_body_local_bounds_ready_body_summary_provider_at_in;
      eassumption.
  - pose proof
      (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound
        env f_component Hcheck) as Hsummary.
    eapply
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds;
      eassumption.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_exact_route_package_at_all :
  forall env bounds,
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    forall fname,
      store_safe_ready_body_exact_body_call_route_package_at
        (global_env_with_local_bounds env bounds) fname.
Proof.
  intros env bounds Hprovider Hcomponent_check fname fdef fcall used used'
    fname_body args_body Hin Hname Hrename Htarget.
  change (env_fns (global_env_with_local_bounds env bounds)) with
    (env_fns env) in Hin.
  destruct (alpha_rename_fn_def_static_fields used fdef fcall used' Hrename)
    as (_ & _ & _ & _ & _ & _ & Hbounds).
  split.
  - rewrite Hbounds.
    change (fn_root_shadow_ready_body_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fdef)) fname_body).
    eapply component_body_local_bounds_ready_body_summary_provider_at_in.
    + exact Hprovider.
    + exact Hin.
    + eapply Hcomponent_check. exact Hin.
  - change (store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body).
    eapply
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds.
    + eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      eapply Hcomponent_check. exact Hin.
    + exact Hrename.
    + exact Htarget.
Qed.

Lemma check_fn_root_shadow_synthetic_direct_call_ready_summary_sound :
  forall env fdef,
    check_fn_root_shadow_synthetic_direct_call_ready_summary env fdef =
      true ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_synthetic_direct_call_ready_summary in Hcheck.
  destruct (direct_call_target_expr (fn_body fdef))
    as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
  apply andb_true_iff in Hcheck as [Hready Hcheck].
  destruct (infer_env_roots_shadow_safe env
    (fn_with_body fdef synthetic_body)
    (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hcompat Hroots] Henv].
  pose proof (infer_env_roots_shadow_safe_sound env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
  unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
  destruct Htyped_fn as
    (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
  split.
  - change (NoDup
      (ctx_names
        (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
    eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env.
  - unfold callee_body_root_shadow_synthetic_direct_call_ready_at.
    exists fname, args, synthetic_body, T_body_actual, Gamma_out_actual,
      R_body, roots_body.
    repeat split; try exact Htarget; try exact Htyped_body;
      try exact Hcompat_body; try exact Hcompat.
    + unfold direct_call_target_expr in Htarget.
      destruct (fn_body fdef); try discriminate.
      * inversion Htarget. reflexivity.
      * destruct e; try discriminate.
        inversion Htarget. reflexivity.
    + unfold direct_call_target_expr in Htarget.
      destruct (fn_body fdef); try discriminate.
      * inversion Htarget. subst. simpl in Hready.
        apply PDCR_Call.
        apply preservation_ready_args_b_sound. exact Hready.
      * destruct e; try discriminate.
        inversion Htarget. subst. simpl in Hready.
        apply PDCR_Call.
        apply preservation_ready_args_b_sound. exact Hready.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_env_root_shadow_synthetic_direct_call_ready_summary_sound :
  forall env,
    check_env_root_shadow_synthetic_direct_call_ready_summary env = true ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _Hname].
  unfold check_env_root_shadow_synthetic_direct_call_ready_summary in Hcheck.
  eapply check_fn_root_shadow_synthetic_direct_call_ready_summary_sound.
  eapply (proj1 (forallb_forall
    (check_fn_root_shadow_synthetic_direct_call_ready_summary env)
    (env_fns env)) Hcheck); exact Hin.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary_sound :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary
      env = true ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env env.
Proof.
  intros env Hcheck f_component fname fdef Hin_component Hcomponent_check
    Hlookup.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary
    in Hcheck.
  pose proof (proj1 (forallb_forall
    (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary
      env)
    (env_fns env)) Hcheck f_component Hin_component) as Hlocal_check.
  unfold check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary
    in Hlocal_check.
  rewrite Hcomponent_check in Hlocal_check.
  pose (local_env := global_env_with_local_bounds env (fn_bounds f_component)).
  assert (Hin_local : In fdef (env_fns local_env)).
  { subst local_env. eapply lookup_fn_in. exact Hlookup. }
  pose proof (proj1 (forallb_forall
    (fun local_fdef =>
       check_fn_root_shadow_synthetic_direct_call_ready_summary
         local_env local_fdef ||
       check_fn_root_shadow_summary local_env local_fdef ||
       check_fn_root_shadow_store_safe_narrow_summary local_env local_fdef)
    (env_fns local_env)) Hlocal_check fdef Hin_local) as Hfn_check.
  repeat rewrite orb_true_iff in Hfn_check.
  destruct Hfn_check as [[Hsynthetic | Hsummary] | Hnarrow].
  - left.
    eapply check_fn_root_shadow_synthetic_direct_call_ready_summary_sound.
    exact Hsynthetic.
  - right. left.
    eapply check_fn_root_shadow_summary_sound.
    exact Hsummary.
  - right. right.
    eapply check_fn_root_shadow_store_safe_narrow_summary_sound.
    exact Hnarrow.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env env.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_alpha_body_callback_provider_check_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env.
Proof.
  intros env Hcheck Hno_receiver.
  eapply component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_of_summary_provider.
  eapply check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_sound;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_alpha_body_callback_provider_of_local_certificate :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env'.
Proof.
  intros env env' Hprog Hno_receiver.
  eapply check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_alpha_body_callback_provider_check_sound.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_local_certificate_check.
    exact Hprog.
  - exact Hno_receiver.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
      env' /\
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env'.
Proof.
  intros env env' Hprog Hno_receiver.
  split.
  - eapply check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_sound.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_local_certificate_check.
      exact Hprog.
    + exact Hno_receiver.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_alpha_body_callback_provider_of_local_certificate;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_route_and_alpha_callback_provider_of_local_certificate :
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env' /\
    component_body_local_bounds_ready_body_or_narrow_alpha_body_callback_provider_in_env
      env'.
Proof.
  intros Hbridge env env' Hprog Hno_receiver.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate
    env env' Hprog Hno_receiver) as [Hprovider Halpha_provider].
  split.
  - eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_summary_route_bridge;
      eassumption.
  - exact Halpha_provider.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_route_and_value_callback_provider_of_local_certificate :
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env' /\
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env'.
Proof.
  intros Hroute_bridge Hvalue_bridge env env' Hprog Hno_receiver.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate
    env env' Hprog Hno_receiver) as [Hprovider Halpha_provider].
  split.
  - eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_alpha_summary_route_bridge;
      eassumption.
  - eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_alpha_summary_value_callback_bridge;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_route_and_value_callback_provider_of_summary_route_bridge_local_certificate :
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
      env' /\
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env'.
Proof.
  intros Hbridge.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_route_and_value_callback_provider_of_local_certificate.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
    exact Hbridge.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge.
    exact Hbridge.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_shadow_checks_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_shadow_checks
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env env /\
    env_fns_root_shadow_summary_evidence env.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_shadow_checks
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hlocal Hprovenance] Hpreservation].
  split.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_or_local_narrow_summary_sound.
    exact Hlocal.
  - eapply check_env_root_shadow_summary_evidence_of_provenance_and_preservation_checks;
      eassumption.
Qed.

Lemma component_body_local_bounds_synthetic_summary_check_provider_exact_route_package_at_all :
  forall env bounds,
    component_body_local_bounds_synthetic_summary_check_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    forall fname,
      store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
        (global_env_with_local_bounds env bounds) fname.
Proof.
  intros env bounds Hprovider Hcomponent_check fname fdef fcall used used'
    fname_body args_body Hin Hname Hrename Htarget.
  change (env_fns (global_env_with_local_bounds env bounds)) with
    (env_fns env) in Hin.
  destruct (alpha_rename_fn_def_static_fields used fdef fcall used' Hrename)
    as (_ & _ & _ & _ & _ & _ & Hbounds).
  split.
  - rewrite Hbounds.
    change (fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      (global_env_with_local_bounds env (fn_bounds fdef)) fname_body).
    eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
    eapply check_env_root_shadow_synthetic_direct_call_ready_summary_sound.
    eapply Hprovider.
    + exact Hin.
    + eapply Hcomponent_check. exact Hin.
  - change (store_safe_function_value_call_args
      (global_env_with_local_bounds env (fn_bounds fcall)) args_body).
    eapply
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds.
    + eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      eapply Hcomponent_check. exact Hin.
    + exact Hrename.
    + exact Htarget.
Qed.

Lemma component_body_local_bounds_synthetic_summary_check_provider_reachable_package_provider :
  forall env bounds base_fname,
    component_body_local_bounds_synthetic_summary_check_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env bounds) base_fname.
Proof.
  intros env bounds base_fname Hprovider Hcomponent_check env0 fname
    Hreachable.
  destruct
    (store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_local_bounds_family
      _ _ _ _ Hreachable) as [bounds0 ->].
  change (store_safe_synthetic_direct_call_ready_exact_body_call_route_package_at
    (global_env_with_local_bounds env bounds0) fname).
  eapply component_body_local_bounds_synthetic_summary_check_provider_exact_route_package_at_all;
    eassumption.
Qed.

Lemma component_body_local_bounds_synthetic_summary_check_provider_reachable_package_and_exact_target_provider :
  forall env bounds base_fname,
    component_body_local_bounds_synthetic_summary_check_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    (forall env0 fname,
      global_env_local_bounds_family
        (global_env_with_local_bounds env bounds) env0 ->
      forall fdef fcall used used' fname_body args_body synthetic_body,
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, fn_body fcall)) ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env bounds) base_fname /\
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env bounds) base_fname.
Proof.
  intros env bounds base_fname Hprovider Hcomponent_check Htarget.
  split.
  - eapply component_body_local_bounds_synthetic_summary_check_provider_reachable_package_provider;
      eassumption.
  - intros env0 fname Hreachable.
    eapply Htarget.
    eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_local_bounds_family.
    exact Hreachable.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_of_synthetic_summary_check_provider :
  forall env,
    component_body_local_bounds_synthetic_summary_check_provider_in_env env ->
    component_body_local_bounds_ready_body_summary_provider_in_env env.
Proof.
  intros env Hprovider f_component Hin_component Hcomponent_check.
  eapply env_fns_root_shadow_ready_body_summary_evidence_of_synthetic.
  eapply check_env_root_shadow_synthetic_direct_call_ready_summary_sound.
  eapply Hprovider; eassumption.
Qed.

Lemma component_body_local_bounds_ready_body_route_provider_of_synthetic_summary_check_provider :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env,
    component_body_local_bounds_synthetic_summary_check_provider_in_env env ->
    component_body_local_bounds_ready_body_route_provider_in_env env.
Proof.
  intros Hbridge env Hprovider.
  eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
  - exact Hbridge.
  - eapply component_body_local_bounds_ready_body_summary_provider_of_synthetic_summary_check_provider.
    exact Hprovider.
Qed.

Lemma check_env_root_shadow_ready_body_summary_sound :
  forall env,
    forallb
      (fun local_fdef =>
         check_fn_root_shadow_synthetic_direct_call_ready_summary
           env local_fdef ||
         check_fn_root_shadow_summary env local_fdef)
      (env_fns env) = true ->
    env_fns_root_shadow_ready_body_summary_evidence env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _Hname].
  pose proof (proj1 (forallb_forall
    (fun local_fdef =>
       check_fn_root_shadow_synthetic_direct_call_ready_summary
         env local_fdef ||
       check_fn_root_shadow_summary env local_fdef)
    (env_fns env)) Hcheck fdef Hin) as Hfn_check.
  apply orb_true_iff in Hfn_check as [Hready | Hsummary].
  - left.
    eapply check_fn_root_shadow_synthetic_direct_call_ready_summary_sound.
    exact Hready.
  - right.
    eapply check_fn_root_shadow_summary_sound.
    exact Hsummary.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary_local_bounds_synthetic_summary_provider_sound :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env = true ->
    component_body_local_bounds_synthetic_summary_check_provider_in_env
      env.
Proof.
  intros env Hcheck f_component Hin_component Hcomponent_check.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
    in Hcheck.
  pose proof (proj1 (forallb_forall
    (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env)
    (env_fns env)) Hcheck f_component Hin_component) as Hbody_check.
  unfold check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
    in Hbody_check.
  rewrite Hcomponent_check in Hbody_check.
  exact Hbody_check.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound :
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    component_body_local_bounds_ready_body_summary_provider_in_env
      env.
Proof.
  intros env Hcheck f_component Hin_component Hcomponent_check.
  unfold check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
    in Hcheck.
  pose proof (proj1 (forallb_forall
    (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env)
    (env_fns env)) Hcheck f_component Hin_component) as Hbody_check.
  unfold check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
    in Hbody_check.
  rewrite Hcomponent_check in Hbody_check.
  eapply check_env_root_shadow_ready_body_summary_sound.
  exact Hbody_check.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_route_provider_sound :
  forall env,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    component_body_local_bounds_ready_body_route_provider_in_env
      env.
Proof.
  intros env Hsummary_to_route Hcheck.
  apply Hsummary_to_route.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_and_route_provider_sound_of_synthetic_and_shadow_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env ->
    component_body_local_bounds_ready_body_summary_provider_in_env env /\
    component_body_local_bounds_ready_body_route_provider_in_env env.
Proof.
  intros Hroot_names Hroot_keys env Hcheck Hsynthetic_provider
    Hshadow_provider.
  split.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hcheck.
  - eapply component_body_local_bounds_ready_body_route_provider_of_synthetic_and_shadow_route_providers.
    + eapply ready_body_summary_local_bounds_family_mixed_route_bridge_of_routes;
        eassumption.
    + exact Hsynthetic_provider.
    + exact Hshadow_provider.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_synthetic_route_provider_sound :
  forall env,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env (fn_bounds f_component)).
Proof.
  intros env Hsummary_to_route Hcheck f_component Hin_component
    Hcomponent_check.
  eapply component_body_local_bounds_synthetic_route_provider_of_ready_body_route_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_route_provider_sound;
      eassumption.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma component_body_local_bounds_ready_body_callback_provider_of_summary_provider :
  forall env,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    component_body_local_bounds_ready_body_callback_provider_in_env env.
Proof.
  intros env Hsummary_to_route Hprovider.
  eapply component_body_local_bounds_ready_body_callback_provider_of_route_provider.
  eapply Hsummary_to_route. exact Hprovider.
Qed.

Lemma component_body_local_bounds_synthetic_ready_body_callback_provider_of_summary_provider :
  forall env,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env.
Proof.
  intros env Hsummary_to_route Hprovider.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_ready_body_callback_provider.
  eapply component_body_local_bounds_ready_body_callback_provider_of_summary_provider;
    eassumption.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_store_safe_callback_at_provider :
  forall env f_component,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env f_component.
Proof.
  intros env f_component Hsummary_to_route Hprovider Hin_component
    Hcomponent_check.
  eapply strict_exact_closure_component_body_store_safe_callback_at_provider_of_synthetic_ready_body_callback_provider.
  - eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_summary_provider;
      eassumption.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_callback_provider_sound :
  forall env,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    component_body_local_bounds_ready_body_callback_provider_in_env
      env.
Proof.
  intros env Hsummary_to_route Hcheck.
  eapply component_body_local_bounds_ready_body_callback_provider_of_summary_provider.
  - exact Hsummary_to_route.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_synthetic_ready_body_callback_provider_sound :
  forall env,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env.
Proof.
  intros env Hsummary_to_route Hcheck.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_summary_provider.
  - exact Hsummary_to_route.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_store_safe_callback_at_provider_sound :
  forall env f_component,
    (component_body_local_bounds_ready_body_summary_provider_in_env env ->
     component_body_local_bounds_ready_body_route_provider_in_env env) ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env f_component.
Proof.
  intros env f_component Hsummary_to_route Hcheck Hin_component
    Hcomponent_check.
  eapply component_body_local_bounds_ready_body_summary_provider_store_safe_callback_at_provider.
  - exact Hsummary_to_route.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hcheck.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_exact_route_package_at_all_sound :
  forall env bounds,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    forall fname,
      store_safe_ready_body_exact_body_call_route_package_at
        (global_env_with_local_bounds env bounds) fname.
Proof.
  intros env bounds Hready_check Hcomponent_check fname.
  eapply component_body_local_bounds_ready_body_summary_provider_exact_route_package_at_all.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hready_check.
  - exact Hcomponent_check.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_reachable_package_provider :
  forall env bounds base_fname,
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env bounds) base_fname.
Proof.
  intros env bounds base_fname Hprovider Hcomponent_check env0 fname
    Hreachable.
  pose proof
    (store_safe_ready_body_exact_body_call_route_reachable_local_bounds_family
      (global_env_with_local_bounds env bounds) base_fname env0 fname
      Hreachable) as Hfamily.
  destruct Hfamily as [bounds0 ->].
  change (store_safe_ready_body_exact_body_call_route_package_at
    (global_env_with_local_bounds env bounds0) fname).
  eapply component_body_local_bounds_ready_body_summary_provider_exact_route_package_at_all;
    eassumption.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_reachable_package_provider_sound :
  forall env bounds base_fname,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env bounds) base_fname.
Proof.
  intros env bounds base_fname Hready_check Hcomponent_check.
  eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hready_check.
  - exact Hcomponent_check.
Qed.

Lemma component_body_local_bounds_ready_body_summary_provider_reachable_package_and_exact_target_provider :
  forall env bounds base_fname,
    component_body_local_bounds_ready_body_summary_provider_in_env env ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    (forall env0 fname,
      global_env_local_bounds_family
        (global_env_with_local_bounds env bounds) env0 ->
      forall fdef fcall used used' fname_body args_body synthetic_body,
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, fn_body fcall)) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env bounds) base_fname /\
    store_safe_ready_body_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env bounds) base_fname.
Proof.
  intros env bounds base_fname Hprovider Hcomponent_check Htarget.
  split.
  - eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_provider;
      eassumption.
  - eapply store_safe_ready_body_exact_body_call_route_reachable_exact_body_target_provider_of_local_bounds_family.
    exact Htarget.
Qed.

Lemma check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_reachable_package_and_exact_target_provider_sound :
  forall env bounds base_fname,
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true ->
    (forall f_component,
      In f_component (env_fns env) ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env f_component = true) ->
    (forall env0 fname,
      global_env_local_bounds_family
        (global_env_with_local_bounds env bounds) env0 ->
      forall fdef fcall used used' fname_body args_body synthetic_body,
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, fn_body fcall)) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env bounds) base_fname /\
    store_safe_ready_body_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env bounds) base_fname.
Proof.
  intros env bounds base_fname Hready_check Hcomponent_check Htarget.
  eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_and_exact_target_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    exact Hready_check.
  - exact Hcomponent_check.
  - exact Htarget.
Qed.

Lemma component_body_local_bounds_synthetic_summary_check_provider_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f_component,
    component_body_local_bounds_synthetic_summary_check_provider_in_env env ->
    In f_component (env_fns env) ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env (fn_bounds f_component)).
Proof.
  intros Hsynthetic_route Hroot_names Hroot_keys env f_component Hprovider
    Hin_component Hcomponent_check.
  intros env0 Hfamily s0 fname args s1 v1 n_call Heval_call
    _Hheight_call Ω n R Σ T Σ' R' roots Hsafe_args Hstore_prefix
    Hroots_within Hshadow Hrn Hnamed Hkeys Htyped Hunique _Hsummary_at
    _Hevidence_at.
  pose proof (check_env_root_shadow_synthetic_direct_call_ready_summary_sound
    (global_env_with_local_bounds env (fn_bounds f_component))
    (Hprovider f_component Hin_component Hcomponent_check))
    as Hsummary_base.
  destruct Hfamily as [bounds ->].
  eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_with_evidence_at_all.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement_of_prefix_statement.
    exact Hsynthetic_route.
  - exact Heval_call.
  - eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args.
  - exact Hstore_prefix.
  - exact Hroots_within.
  - exact Hshadow.
  - exact Hrn.
  - exact Hnamed.
  - exact Hkeys.
  - exact Htyped.
  - exact Hunique.
  - eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
    eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    exact Hsummary_base.
  - intros fname_top.
    eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at.
    + exact Hroot_names.
    + exact Hroot_keys.
    + eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
      eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary_base.
    + exact Hunique.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_when_direct_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
      (global_env_with_local_bounds env' (fn_bounds f_component)).
Proof.
  intros Hsynthetic_route Hroot_names Hroot_keys env env' f_component Hprog
    Hdirect_ready _Hin_component Hcomponent_check env0 Hfamily s0 fname args
    s1 v1 n_call Heval_call _Hheight_call Ω n R Σ T Σ' R' roots
    Hsafe_args Hstore_prefix Hroots_within Hshadow Hrn Hnamed Hkeys Htyped
    Hunique _Hsummary_at _Hevidence_at.
  destruct (check_env_end2end_direct_receiver_ready_facts env' Hdirect_ready)
    as (_Hprov_check & _Hpres_check & _Hdirect_check & Hcomponent_env_check).
  pose proof
    (component_body_no_capture_direct_call_component_store_safe_summary_with_body_summary_provider_of_store_safe_provider
      env'
      (infer_program_env_end2end_assoc_direct_receiver_mixed_component_body_store_safe_provider_of_component_check
        env env' Hprog Hcomponent_env_check)
      f_component
      (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound
        env' f_component Hcomponent_check)) as [_ Hsummary_base].
  destruct Hfamily as [bounds ->].
  eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_with_evidence_at_all.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement_of_prefix_statement.
    exact Hsynthetic_route.
  - exact Heval_call.
  - eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args.
  - exact Hstore_prefix.
  - exact Hroots_within.
  - exact Hshadow.
  - exact Hrn.
  - exact Hnamed.
  - exact Hkeys.
  - exact Htyped.
  - exact Hunique.
  - eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
    eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    exact Hsummary_base.
  - intros fname_top.
    eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at.
    + exact Hroot_names.
    + exact Hroot_keys.
    + eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
      eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary_base.
    + exact Hunique.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_synthetic_summary_provider_prefix :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_synthetic_summary_check_provider_in_env
        env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic env env' f s s' v
    Hprog Hlocal_bounds_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_local_bounds_route_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    destruct
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
        env env' Hprog) as [Hno_receiver | Hdirect_ready].
    + eapply component_body_local_bounds_synthetic_summary_check_provider_route.
      * exact Hsynthetic_route.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact (Hlocal_bounds_provider_when_no_receiver Hno_receiver).
      * exact Hin_component.
      * exact Hcomponent_check.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_when_direct_ready;
        eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_synthetic_summary_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_synthetic_summary_check_provider_in_env
        env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hlocal_bounds_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_synthetic_summary_provider_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
  - exact Hprog.
  - exact Hlocal_bounds_provider_when_no_receiver.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider_prefix :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_ready_body_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic env env' f s s' v
    Hprog Hready_route_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_mixed_local_bounds_route_callbacks.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - intros f_component Hin_component Hcomponent_check.
    destruct
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
        env env' Hprog) as [Hno_receiver | Hdirect_ready].
    + eapply component_body_local_bounds_synthetic_route_provider_of_ready_body_route_provider.
      * exact (Hready_route_provider_when_no_receiver Hno_receiver).
      * exact Hin_component.
      * exact Hcomponent_check.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_when_direct_ready;
        eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_ready_body_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hready_route_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
  - exact Hprog.
  - exact Hready_route_provider_when_no_receiver.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_route_provider_check_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_prefix_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
        env' = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic
    Hsummary_to_route env env' f s s' v Hprog
    Hready_body_check_when_no_receiver Hinitial Hin Hstore Heval.
  destruct
    (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
      env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - pose proof (Hready_body_check_when_no_receiver Hno_receiver)
      as Hready_check.
    eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_ready_body_route_component_local_bounds_family.
    + exact Hroot_names.
    + exact Hroot_keys.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog.
    + eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_route_provider_sound.
      * eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
        exact Hsummary_to_route.
      * exact Hready_check.
    + eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
      exact Hready_check.
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

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_route_provider_check :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
        env' = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route
    env env' f s s' v Hprog Hready_body_check_when_no_receiver Hinitial
    Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_route_provider_check_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
  - exact Hsummary_to_route.
  - exact Hprog.
  - exact Hready_body_check_when_no_receiver.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_and_mixed_route_providers_prefix :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
        env' = true) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic env env' f s s' v
    Hprog Hready_body_check_when_no_receiver Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  destruct
    (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
      env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - pose proof (Hready_body_check_when_no_receiver Hno_receiver)
      as Hready_check.
    eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_ready_body_route_component_local_bounds_family.
    + exact Hroot_names.
    + exact Hroot_keys.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog.
    + eapply component_body_local_bounds_ready_body_route_provider_of_synthetic_and_shadow_route_providers.
      * eapply ready_body_summary_local_bounds_family_mixed_route_bridge_of_routes;
          eassumption.
      * exact (Hsynthetic_provider_when_no_receiver Hno_receiver).
      * exact (Hshadow_provider_when_no_receiver Hno_receiver).
    + eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
      exact Hready_check.
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

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_and_mixed_route_providers :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
        env' = true) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v Hprog
    Hready_body_check_when_no_receiver Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_and_mixed_route_providers_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
  - exact Hprog.
  - exact Hready_body_check_when_no_receiver.
  - exact Hsynthetic_provider_when_no_receiver.
  - exact Hshadow_provider_when_no_receiver.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_summary_provider_check_prefix :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
        env' = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic env env' f s s' v
    Hprog Hcomponent_body_check_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_synthetic_summary_provider_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hstatic.
  - exact Hprog.
  - intros Hno_receiver.
    eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary_local_bounds_synthetic_summary_provider_sound.
    exact (Hcomponent_body_check_when_no_receiver Hno_receiver).
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_component_body_summary_provider_check_prefix :
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
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hstatic env env' f s s' v
    Hprog Hcomponent_body_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_summary_provider_check_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hstatic.
  - exact Hprog.
  - intros _Hno_receiver.
    exact Hcomponent_body_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_component_body_summary_provider_check :
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
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hcomponent_body_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_component_body_summary_provider_check_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
  - exact Hprog.
  - exact Hcomponent_body_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_summary_provider_check :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
        env' = true) ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hcomponent_body_check_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_public_callbacks_big_step_safe_checked_initial_ready_with_no_receiver_component_body_summary_provider_check_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
  - exact Hprog.
  - exact Hcomponent_body_check_when_no_receiver.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Lemma check_env_root_shadow_no_receiver_component_body_summary_provider_check_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_body_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
      env = true.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_body_summary_provider_check
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  exact Hcheck.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_check_provider_when_direct_ready :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true.
Proof.
  intros env env' _Hprog Hdirect_ready f_component Hin_component.
  destruct (check_env_end2end_direct_receiver_ready_facts env' Hdirect_ready)
    as (_Hprov_check & _Hpres_check & _Hdirect_check & Hcomponent_env_check).
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_check_provider;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_checks_when_direct_ready :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    check_env_root_shadow_provenance_summary env' = true /\
    check_env_preservation_ready env' = true.
Proof.
  intros env env' _Hprog Hdirect_ready.
  destruct (check_env_end2end_direct_receiver_ready_facts env' Hdirect_ready)
    as (Hprov_check & Hpres_check & _Hdirect_check & _Hcomponent_env_check).
  split; assumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_check_provider_when_direct_receiver_present :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = true ->
    forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true.
Proof.
  intros env env' Hprog Hpresent f_component Hin_component.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
              env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - rewrite Hpresent in Hno_receiver. discriminate.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_component_check_provider_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_checks_when_direct_receiver_present :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = true ->
    check_env_root_shadow_provenance_summary env' = true /\
    check_env_preservation_ready env' = true.
Proof.
  intros env env' Hprog Hpresent.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
              env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - rewrite Hpresent in Hno_receiver. discriminate.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_checks_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_component_check_provider_cases :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false \/
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true).
Proof.
  intros env env' Hprog.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
              env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - left. exact Hno_receiver.
  - right.
    eapply infer_program_env_end2end_assoc_direct_receiver_mixed_component_check_provider_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_checks_cases :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false \/
    (check_env_root_shadow_provenance_summary env' = true /\
     check_env_preservation_ready env' = true).
Proof.
  intros env env' Hprog.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
              env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - left. exact Hno_receiver.
  - right.
    eapply infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_checks_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_direct_ready_provider_bundle_when_direct_ready :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_end2end_direct_receiver_ready env' = true ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) /\
    check_env_root_shadow_provenance_summary env' = true /\
    check_env_preservation_ready env' = true.
Proof.
  intros env env' Hprog Hdirect_ready.
  split.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_component_check_provider_when_direct_ready;
      eassumption.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_checks_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_direct_ready_provider_bundle_when_direct_receiver_present :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = true ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) /\
    check_env_root_shadow_provenance_summary env' = true /\
    check_env_preservation_ready env' = true.
Proof.
  intros env env' Hprog Hpresent.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
              env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - rewrite Hpresent in Hno_receiver. discriminate.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_direct_ready_provider_bundle_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_direct_ready_provider_bundle_cases :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_direct_receiver_method_present env' = false \/
    ((forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) /\
     check_env_root_shadow_provenance_summary env' = true /\
     check_env_preservation_ready env' = true).
Proof.
  intros env env' Hprog.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
              env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - left. exact Hno_receiver.
  - right.
    eapply infer_program_env_end2end_assoc_direct_receiver_mixed_direct_ready_provider_bundle_when_direct_ready;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_reachable_package_provider_of_no_receiver_component_body_summary_provider_check :
  forall env env' bounds base_fname,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' bounds) base_fname.
Proof.
  intros env env' bounds base_fname _Hprog Hbody_check Hno_receiver
    Hcomponent_check.
  eapply component_body_local_bounds_synthetic_summary_check_provider_reachable_package_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary_local_bounds_synthetic_summary_provider_sound.
    eapply check_env_root_shadow_no_receiver_component_body_summary_provider_check_sound;
      eassumption.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_reachable_package_and_exact_target_provider_of_no_receiver_component_body_summary_provider_check :
  forall env env' bounds base_fname,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    (forall env0 fname,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' bounds) env0 ->
      forall fdef fcall used used' fname_body args_body synthetic_body,
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, fn_body fcall)) ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' bounds) base_fname /\
    store_safe_synthetic_direct_call_ready_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env' bounds) base_fname.
Proof.
  intros env env' bounds base_fname _Hprog Hbody_check Hno_receiver
    Hcomponent_check Htarget.
  eapply component_body_local_bounds_synthetic_summary_check_provider_reachable_package_and_exact_target_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary_local_bounds_synthetic_summary_provider_sound.
    eapply check_env_root_shadow_no_receiver_component_body_summary_provider_check_sound;
      eassumption.
  - exact Hcomponent_check.
  - exact Htarget.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_of_shadow_checks :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env = true ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env = true.
Proof.
  intros env Hcheck.
  unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
    in Hcheck.
  unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check.
  destruct (check_env_root_shadow_direct_receiver_method_present env) eqn:Hpresent;
    simpl in *; [reflexivity |].
  destruct (check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
              env); simpl in Hcheck; try discriminate.
  reflexivity.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_of_checks :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env = true ->
    check_env_root_shadow_provenance_summary env = true ->
    check_env_preservation_ready env = true ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env = true.
Proof.
  intros env Hready_body Hprovenance Hpreservation.
  unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks.
  unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
    in Hready_body.
  destruct (check_env_root_shadow_direct_receiver_method_present env);
    simpl in *; [reflexivity |].
  rewrite Hready_body, Hprovenance, Hpreservation. reflexivity.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true /\
    check_env_root_shadow_provenance_summary env = true /\
    check_env_preservation_ready env = true.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
    in Hcheck.
  rewrite Hno_receiver in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hready_body Hprovenance] Hpreservation].
  repeat split; assumption.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check_sound :
  forall env,
    fn_env_unique_by_name env ->
    check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true \/
    component_body_local_bounds_narrow_summary_provider_in_env env.
Proof.
  intros env Hunique Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check
    in Hcheck.
  apply orb_true_iff in Hcheck as [Hready_check | Hnarrow_check].
  - left.
    eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
      eassumption.
  - right.
    eapply check_env_root_shadow_no_receiver_component_narrow_summary_provider_check_sound;
      eassumption.
Qed.

Lemma check_env_root_shadow_no_receiver_component_ready_body_or_local_bounds_narrow_summary_provider_check_sound :
  forall env,
    check_env_root_shadow_no_receiver_component_ready_body_or_local_bounds_narrow_summary_provider_check
      env = true ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
      env = true \/
    component_body_local_bounds_narrow_summary_provider_in_env env.
Proof.
  intros env Hcheck Hno_receiver.
  unfold check_env_root_shadow_no_receiver_component_ready_body_or_local_bounds_narrow_summary_provider_check
    in Hcheck.
  apply orb_true_iff in Hcheck as [Hready_check | Hnarrow_check].
  - left.
    eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
      eassumption.
  - right.
    eapply check_env_root_shadow_no_receiver_component_local_bounds_narrow_summary_provider_check_sound;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_summary_evidence_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    env_fns_root_shadow_summary_evidence env'.
Proof.
  intros env env' Hprog Hcombined_check.
  destruct
    (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
      env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - destruct (check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_sound
                env' Hcombined_check Hno_receiver)
      as [_Hready_body [Hprovenance Hpreservation]].
    eapply check_env_root_shadow_summary_evidence_of_provenance_and_preservation_checks;
      eassumption.
  - destruct (check_env_end2end_direct_receiver_ready_facts env' Hdirect_ready)
      as (Hprovenance & Hpreservation & _Hdirect & _Hcomponent).
    eapply check_env_root_shadow_summary_evidence_of_provenance_and_preservation_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_summary_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
    Hcombined_check.
  eapply component_body_local_bounds_shadow_summary_route_provider_of_env_summary.
  - eapply shadow_summary_local_bounds_family_route_bridge_of_ready_body_route_bridge;
      eassumption.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_summary_evidence_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_summary_provider_in_env env'.
Proof.
  intros env env' _Hprog Hcombined_check Hno_receiver.
  destruct (check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_sound
              env' Hcombined_check Hno_receiver)
    as [Hready_body _Hshadow_checks].
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
  exact Hready_body.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_summary_provider_in_env env'.
Proof.
  intros env env' _Hprog Hready_body_check Hno_receiver.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
  eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_route_provider_in_env env'.
Proof.
  intros Hsummary_to_route env env' Hprog Hready_body_check Hno_receiver.
  eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
  - exact Hsummary_to_route.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_of_no_receiver_component_ready_body_summary_provider_check :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)).
Proof.
  intros Hsummary_to_route env env' Hprog Hready_body_check Hno_receiver.
  eapply component_body_local_bounds_synthetic_route_provider_of_ready_body_route_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_callback_provider_in_env env'.
Proof.
  intros Hsummary_to_route env env' Hprog Hready_body_check Hno_receiver.
  eapply component_body_local_bounds_ready_body_callback_provider_of_route_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env'.
Proof.
  intros Hsummary_to_route env env' Hprog Hready_body_check Hno_receiver.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_ready_body_callback_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_store_safe_callback_at_provider_of_no_receiver_component_ready_body_summary_provider_check :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component.
Proof.
  intros Hsummary_to_route env env' f_component Hprog Hready_body_check
    Hno_receiver Hin_component Hcomponent_check.
  eapply component_body_local_bounds_ready_body_summary_provider_store_safe_callback_at_provider.
  - eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
    exact Hsummary_to_route.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check;
      eassumption.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_and_route_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys env env' _Hprog Hready_body_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_and_route_provider_sound_of_synthetic_and_shadow_routes;
    try eassumption.
  eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_route_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hready_body_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  destruct
    (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_and_route_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes
      Hroot_names Hroot_keys env env' Hprog Hready_body_check Hno_receiver
      Hsynthetic_provider Hshadow_provider) as [_ Hroute].
  exact Hroute.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_callback_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hready_body_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  eapply component_body_local_bounds_ready_body_callback_provider_of_route_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hready_body_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_ready_body_callback_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_store_safe_callback_at_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component.
Proof.
  intros Hroot_names Hroot_keys env env' f_component Hprog
    Hready_body_check Hno_receiver Hsynthetic_provider Hshadow_provider
    Hin_component Hcomponent_check.
  eapply strict_exact_closure_component_body_store_safe_callback_at_provider_of_synthetic_ready_body_callback_provider.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
      eassumption.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env' /\
    component_body_local_bounds_ready_body_callback_provider_in_env env' /\
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env' /\
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component).
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hready_body_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  split.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check;
      eassumption.
  - split.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
        eassumption.
    + split.
      * eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
          eassumption.
      * split.
        -- eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
             eassumption.
        -- intros f_component Hin_component Hcomponent_check.
           eapply infer_program_env_end2end_assoc_direct_receiver_mixed_store_safe_callback_at_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
             eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_shadow_route_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env' /\
    component_body_local_bounds_ready_body_callback_provider_in_env env' /\
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env' /\
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component).
Proof.
  intros Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
    Hready_body_check Hno_receiver Hshadow_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hready_body_check.
  - exact Hno_receiver.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_of_no_receiver_component_ready_body_summary_provider_check;
      eassumption.
  - exact Hshadow_provider.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_and_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hcombined_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_and_route_provider_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes;
    try eassumption.
  eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_of_shadow_checks.
  exact Hcombined_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_route_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hcombined_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  destruct
    (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_and_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes
      Hroot_names Hroot_keys env env' Hprog Hcombined_check Hno_receiver
      Hsynthetic_provider Hshadow_provider) as [_ Hroute].
  exact Hroute.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_callback_provider_in_env env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hcombined_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  eapply component_body_local_bounds_ready_body_callback_provider_of_route_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env'.
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hcombined_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_ready_body_callback_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_store_safe_callback_at_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component.
Proof.
  intros Hroot_names Hroot_keys env env' f_component Hprog
    Hcombined_check Hno_receiver Hsynthetic_provider Hshadow_provider
    Hin_component Hcomponent_check.
  eapply strict_exact_closure_component_body_store_safe_callback_at_provider_of_synthetic_ready_body_callback_provider.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
      eassumption.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_shadow_summary_route_provider_in_env env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env' /\
    component_body_local_bounds_ready_body_callback_provider_in_env env' /\
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env' /\
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component).
Proof.
  intros Hroot_names Hroot_keys env env' Hprog Hcombined_check
    Hno_receiver Hsynthetic_provider Hshadow_provider.
  split.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
  - split.
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
        eassumption.
    + split.
      * eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
          eassumption.
      * split.
        -- eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
             eassumption.
        -- intros f_component Hin_component Hcomponent_check.
           eapply infer_program_env_end2end_assoc_direct_receiver_mixed_store_safe_callback_at_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes;
             eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_synthetic_route_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env' /\
    component_body_local_bounds_ready_body_callback_provider_in_env env' /\
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env' /\
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component).
Proof.
  intros Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
    Hcombined_check Hno_receiver Hsynthetic_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hcombined_check.
  - exact Hno_receiver.
  - exact Hsynthetic_provider.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_summary_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_route_provider_in_env env'.
Proof.
  intros Hsummary_to_route env env' Hprog Hcombined_check Hno_receiver.
  eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
  - exact Hsummary_to_route.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
        (global_env_with_local_bounds env' (fn_bounds f_component)).
Proof.
  intros Hsummary_to_route env env' Hprog Hcombined_check Hno_receiver.
  eapply component_body_local_bounds_synthetic_route_provider_of_ready_body_route_provider.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
    eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_callback_provider_in_env env'.
Proof.
  intros Hsummary_to_route env env' Hprog Hcombined_check Hno_receiver.
  eapply component_body_local_bounds_ready_body_callback_provider_of_summary_provider.
  - eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
    exact Hsummary_to_route.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_ready_body_callback_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env'.
Proof.
  intros Hsummary_to_route env env' Hprog Hcombined_check Hno_receiver.
  eapply component_body_local_bounds_synthetic_ready_body_callback_provider_of_summary_provider.
  - eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
    exact Hsummary_to_route.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_store_safe_callback_at_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f_component,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    In f_component (env_fns env') ->
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env' f_component = true ->
    strict_exact_closure_component_body_store_safe_callback_at_provider
      env' f_component.
Proof.
  intros Hsummary_to_route env env' f_component Hprog Hcombined_check
    Hno_receiver Hin_component Hcomponent_check.
  eapply component_body_local_bounds_ready_body_summary_provider_store_safe_callback_at_provider.
  - eapply component_body_local_bounds_ready_body_route_provider_of_summary_provider.
    exact Hsummary_to_route.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
  - exact Hin_component.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env' /\
    component_body_local_bounds_ready_body_callback_provider_in_env env' /\
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env' /\
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component).
Proof.
  intros Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
    Hcombined_check Hno_receiver.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hcombined_check.
  - exact Hno_receiver.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_shadow_summary_route_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_shadow_summary_bridge :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    env_fns_root_shadow_summary_evidence env' ->
    component_body_local_bounds_ready_body_summary_provider_in_env env' /\
    component_body_local_bounds_ready_body_route_provider_in_env env' /\
    component_body_local_bounds_ready_body_callback_provider_in_env env' /\
    component_body_local_bounds_synthetic_ready_body_callback_provider_in_env
      env' /\
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true ->
      strict_exact_closure_component_body_store_safe_callback_at_provider
        env' f_component).
Proof.
  intros Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
    Hready_body_check Hno_receiver Hshadow_summary.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hprog.
  - exact Hready_body_check.
  - exact Hno_receiver.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_synthetic_route_provider_of_no_receiver_component_ready_body_summary_provider_check;
      eassumption.
  - eapply component_body_local_bounds_shadow_summary_route_provider_of_env_summary.
    + eapply shadow_summary_local_bounds_family_route_bridge_of_ready_body_route_bridge;
        eassumption.
    + exact Hshadow_summary.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_exact_route_package_at_all_of_no_receiver_component_ready_body_summary_provider_check :
  forall env env' bounds,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    forall fname,
      store_safe_ready_body_exact_body_call_route_package_at
        (global_env_with_local_bounds env' bounds) fname.
Proof.
  intros env env' bounds _Hprog Hready_body_check Hno_receiver
    Hcomponent_check fname.
  eapply component_body_local_bounds_ready_body_summary_provider_exact_route_package_at_all.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
      eassumption.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_reachable_package_provider_of_no_receiver_component_ready_body_summary_provider_check :
  forall env env' bounds base_fname,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' bounds) base_fname.
Proof.
  intros env env' bounds base_fname Hprog Hready_body_check Hno_receiver
    Hcomponent_check.
  eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
      eassumption.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_reachable_package_and_exact_target_provider_of_no_receiver_component_ready_body_summary_provider_check :
  forall env env' bounds base_fname,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    (forall env0 fname,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' bounds) env0 ->
      forall fdef fcall used used' fname_body args_body synthetic_body,
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, fn_body fcall)) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' bounds) base_fname /\
    store_safe_ready_body_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env' bounds) base_fname.
Proof.
  intros env env' bounds base_fname Hprog Hready_body_check Hno_receiver
    Hcomponent_check Htarget.
  eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_and_exact_target_provider.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary_local_bounds_ready_body_summary_provider_sound.
    eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
      eassumption.
  - exact Hcomponent_check.
  - exact Htarget.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_exact_route_package_at_all_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  forall env env' bounds,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    forall fname,
      store_safe_ready_body_exact_body_call_route_package_at
        (global_env_with_local_bounds env' bounds) fname.
Proof.
  intros env env' bounds Hprog Hcombined_check Hno_receiver
    Hcomponent_check fname.
  eapply component_body_local_bounds_ready_body_summary_provider_exact_route_package_at_all.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_reachable_package_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  forall env env' bounds base_fname,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' bounds) base_fname.
Proof.
  intros env env' bounds base_fname Hprog Hcombined_check Hno_receiver
    Hcomponent_check.
  eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_provider.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
  - exact Hcomponent_check.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_reachable_package_and_exact_target_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks :
  forall env env' bounds base_fname,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_env_root_shadow_direct_receiver_method_present env' = false ->
    (forall f_component,
      In f_component (env_fns env') ->
      check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
        env' f_component = true) ->
    (forall env0 fname,
      global_env_local_bounds_family
        (global_env_with_local_bounds env' bounds) env0 ->
      forall fdef fcall used used' fname_body args_body synthetic_body,
        In fdef (env_fns env0) ->
        fn_name fdef = fname ->
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body) ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, fn_body fcall)) ->
    store_safe_ready_body_exact_body_call_route_reachable_package_provider
      (global_env_with_local_bounds env' bounds) base_fname /\
    store_safe_ready_body_exact_body_call_route_reachable_exact_body_target_provider
      (global_env_with_local_bounds env' bounds) base_fname.
Proof.
  intros env env' bounds base_fname Hprog Hcombined_check Hno_receiver
    Hcomponent_check Htarget.
  eapply component_body_local_bounds_ready_body_summary_provider_reachable_package_and_exact_target_provider.
  - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_summary_provider_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks;
      eassumption.
  - exact Hcomponent_check.
  - exact Htarget.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env
    env' f s s' v Hprog Hready_body_provider_check Hinitial Hin Hstore
    Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_route_provider_check.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hsummary_to_route.
  - exact Hprog.
  - intros Hno_receiver.
    eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_sound;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_or_narrow_summary_provider_check_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env
    env' f s s' v Hprog Hcombined_check Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hunique : fn_env_unique_by_name env').
    { eapply infer_program_env_end2end_assoc_unique_by_name.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    destruct (check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check_sound
      env' Hunique Hcombined_check Hno_receiver) as [Hready_body | Hnarrow].
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_diagnostic.
      * exact Hsynthetic_route.
      * exact Hscope_synthetic.
      * exact Htyping_ready.
      * exact Hroots_ready.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact Hframe_ready.
      * exact Hparam_ready.
      * exact Hsummary_to_route.
      * exact Hprog.
      * unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check.
        rewrite Hno_receiver. simpl. exact Hready_body.
      * exact Hinitial.
      * exact Hin.
      * exact Hstore.
      * exact Heval.
    + eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_component_narrow_provider.
      * eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
        exact Hprog.
      * exact Hnarrow.
      * exact Hinitial.
      * exact Hin.
      * exact Hstore.
      * exact Heval.
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

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_and_mixed_route_providers_diagnostic :
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
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hready_body_provider_check Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    pose proof
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_mixed_routes
        Hroot_names Hroot_keys env env' Hprog Hready_body_provider_check
        Hno_receiver
        (Hsynthetic_provider_when_no_receiver Hno_receiver)
        (Hshadow_provider_when_no_receiver Hno_receiver)) as
        (_Hsummary_provider & Hroute_provider & _Hcallback_provider).
    exact Hroute_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_or_narrow_summary_provider_check_and_mixed_route_providers_diagnostic :
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
    check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hcombined_check Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hunique : fn_env_unique_by_name env').
    { eapply infer_program_env_end2end_assoc_unique_by_name.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    destruct (check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check_sound
      env' Hunique Hcombined_check Hno_receiver) as [Hready_body | Hnarrow].
    + eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_and_mixed_route_providers_diagnostic.
      * exact Hsynthetic_route.
      * exact Hscope_synthetic.
      * exact Htyping_ready.
      * exact Hroots_ready.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact Hframe_ready.
      * exact Hparam_ready.
      * exact Hprog.
      * unfold check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check.
        rewrite Hno_receiver. simpl. exact Hready_body.
      * exact Hsynthetic_provider_when_no_receiver.
      * exact Hshadow_provider_when_no_receiver.
      * exact Hinitial.
      * exact Hin.
      * exact Hstore.
      * exact Heval.
    + eapply infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_component_narrow_provider.
      * eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
        exact Hprog.
      * exact Hnarrow.
      * exact Hinitial.
      * exact Hin.
      * exact Hstore.
      * exact Heval.
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


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_and_mixed_route_providers_diagnostic :
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
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hlocal_mixed_check Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hunique : fn_env_unique_by_name env').
    { eapply infer_program_env_end2end_assoc_unique_by_name.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    assert (Hprovider :
      component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
        env').
    { eapply check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_sound;
        eassumption. }
    assert (Hroute_provider :
      component_body_local_bounds_ready_body_route_provider_in_env env').
    { eapply component_body_local_bounds_ready_body_route_provider_of_synthetic_and_shadow_route_providers.
      - eapply ready_body_summary_local_bounds_family_mixed_route_bridge_of_routes;
          eassumption.
      - exact (Hsynthetic_provider_when_no_receiver Hno_receiver).
      - exact (Hshadow_provider_when_no_receiver Hno_receiver). }
    assert (Hcombined_check :
      check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env' = true).
    { eapply infer_program_env_end2end_assoc_combined_check_env_ready.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_ready_body_or_narrow_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hcombined_check.
    + exact Hprovider.
    + exact Hroute_provider.
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


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_shadow_checks_and_synthetic_route_provider_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_shadow_checks
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env env'
    f s s' v Hprog Hlocal_shadow_check
    Hsynthetic_provider_when_no_receiver Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hunique : fn_env_unique_by_name env').
    { eapply infer_program_env_end2end_assoc_unique_by_name.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    destruct (check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_shadow_checks_sound
      env' Hlocal_shadow_check Hno_receiver) as [Hprovider Hshadow_summary].
    assert (Hroute_provider :
      component_body_local_bounds_ready_body_route_provider_in_env env').
    { eapply component_body_local_bounds_ready_body_route_provider_of_synthetic_and_shadow_route_providers.
      - eapply ready_body_summary_local_bounds_family_mixed_route_bridge_of_routes;
          eassumption.
      - exact (Hsynthetic_provider_when_no_receiver Hno_receiver).
      - eapply component_body_local_bounds_shadow_summary_route_provider_of_env_summary.
        + eapply shadow_summary_local_bounds_family_route_bridge_of_ready_body_route_bridge;
            eassumption.
        + exact Hshadow_summary. }
    assert (Hcombined_check :
      check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env' = true).
    { eapply infer_program_env_end2end_assoc_combined_check_env_ready.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_ready_body_or_narrow_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hcombined_check.
    + exact Hprovider.
    + exact Hroute_provider.
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



Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
        env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hmixed_route_provider_when_no_receiver Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hunique : fn_env_unique_by_name env').
    { eapply infer_program_env_end2end_assoc_unique_by_name.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate
      env env' Hprog Hno_receiver) as [Hprovider _Halpha_callback_provider].
    assert (Hcombined_check :
      check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env' = true).
    { eapply infer_program_env_end2end_assoc_combined_check_env_ready.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_mixed_route_provider.
    + exact Hunique.
    + exact Hcombined_check.
    + exact Hprovider.
    + exact (Hmixed_route_provider_when_no_receiver Hno_receiver).
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


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_component_mixed_route_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hmixed_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_mixed_route_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact (Hmixed_provider_when_no_receiver Hno_receiver).
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_alpha_summary_route_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate
      env env' Hprog Hno_receiver) as [Hprovider Halpha_provider].
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_alpha_summary_route_bridge;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_summary_route_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_alpha_summary_route_bridge;
    try eassumption.
  eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
  exact Hbridge.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_callback_providers :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
        env') ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
        env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hmixed_route_provider_when_no_receiver
    _Hmixed_callback_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_provider;
    eassumption.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_alpha_summary_route_value_callback_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hroute_bridge
    Hvalue_bridge env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_callback_providers.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_route_and_value_callback_provider_of_local_certificate
      Hroute_bridge Hvalue_bridge env env' Hprog Hno_receiver)
      as [Hroute_provider _Hvalue_provider].
    exact Hroute_provider.
  - intros Hno_receiver.
    destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_route_and_value_callback_provider_of_local_certificate
      Hroute_bridge Hvalue_bridge env env' Hprog Hno_receiver)
      as [_Hroute_provider Hvalue_provider].
    exact Hvalue_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_summary_route_value_callback_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_alpha_summary_route_value_callback_bridge;
    try eassumption.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
    exact Hbridge.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge.
    exact Hbridge.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_combined_route_value_callback_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_summary_provider_route_value_callback_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge env env' f s s'
    v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_callback_providers.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate
      env env' Hprog Hno_receiver) as [Hprovider _Halpha_provider].
    destruct (Hbridge env' Hprovider) as [Hroute_provider _Hvalue_provider].
    exact Hroute_provider.
  - intros Hno_receiver.
    destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_or_narrow_provider_bundle_of_local_certificate
      env env' Hprog Hno_receiver) as [Hprovider _Halpha_provider].
    destruct (Hbridge env' Hprovider) as [_Hroute_provider Hvalue_provider].
    exact Hvalue_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_cleanup_callback_providers :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
        env') ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_in_env
        env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hmixed_route_provider_when_no_receiver
    Hmixed_cleanup_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_callback_providers.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - exact Hmixed_route_provider_when_no_receiver.
  - intros Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_cleanup_callback_provider.
    exact (Hmixed_cleanup_provider_when_no_receiver Hno_receiver).
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_callback_provider_of_mixed_route_provider_when_no_receiver :
  forall env,
    (check_env_root_shadow_direct_receiver_method_present env = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env
        env) ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.
Proof.
  intros env Hroute_provider Hno_receiver.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_route_provider.
  exact (Hroute_provider Hno_receiver).
Qed.


Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_cleanup_callback_provider_of_statement_when_no_receiver :
  forall env,
    eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_in_env
      env.
Proof.
  intros env Hcleanup _Hno_receiver.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_of_statement.
  exact Hcleanup.
Qed.

Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_value_callback_provider_of_cleanup_callback_provider_when_no_receiver :
  forall env,
    (check_env_root_shadow_direct_receiver_method_present env = false ->
      component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_in_env
        env) ->
    check_env_root_shadow_direct_receiver_method_present env = false ->
    component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_in_env
      env.
Proof.
  intros env Hcleanup_provider Hno_receiver.
  eapply component_body_local_bounds_mixed_ready_body_or_narrow_value_callback_provider_of_cleanup_callback_provider.
  exact (Hcleanup_provider Hno_receiver).
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_value_cleanup_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_value_cleanup_bridge_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge env env' f s
    s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros _Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_statement.
    eapply Hbridge.
    + exact Hscope_synthetic.
    + exact eval_preserves_typing_ready_prefix_mutual.
    + exact eval_preserves_typing_roots_ready_prefix_mutual.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hframe_ready.
    + exact Hparam_ready.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_synthetic_branch_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsynthetic_branch_route
    env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_cleanup_callback_providers.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros _Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_synthetic_and_shadow_routes.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hsynthetic_branch_route.
    + intros env0.
      eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_provenance_ready_with_callee_summary.
      * exact Hroots_ready.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact Hframe_ready.
      * exact eval_preserves_typing_roots_ready_prefix_mutual.
      * exact Hparam_ready.
  - intros _Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_of_statement.
    eapply eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement_of_synthetic_shadow_and_narrow_routes.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hsynthetic_branch_route.
    + intros env0.
      eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_provenance_ready_with_callee_summary.
      * exact Hroots_ready.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact Hframe_ready.
      * exact eval_preserves_typing_roots_ready_prefix_mutual.
      * exact Hparam_ready.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_exact_body_call_route_package :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
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
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready
    Hexact_body_target Hbody_package.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_summary_route_value_callback_bridge.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_exact_body_call_route_package.
    + exact Hscope_synthetic.
    + exact eval_preserves_typing_ready_prefix_mutual.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hexact_body_target.
    + exact Hbody_package.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_providers :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_component_mixed_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver f_component Hin_component Hcomponent_check.
    split.
    + eapply Hsynthetic_provider_when_no_receiver; eassumption.
    + eapply Hshadow_provider_when_no_receiver; eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_synthetic_route_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hsynthetic_provider_when_no_receiver Hinitial Hin Hstore Heval.
  destruct (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_cases
    env env' Hprog) as [Hno_receiver | Hdirect_ready].
  - assert (Hunique : fn_env_unique_by_name env').
    { eapply infer_program_env_end2end_assoc_unique_by_name.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    assert (Hprovider :
      component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env
        env').
    { eapply check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_sound.
      - eapply infer_program_env_end2end_assoc_direct_receiver_mixed_local_certificate_check.
        exact Hprog.
      - exact Hno_receiver. }
    assert (Hcombined_check :
      check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
        env' = true).
    { eapply infer_program_env_end2end_assoc_combined_check_env_ready.
      eapply infer_program_env_end2end_assoc_direct_receiver_mixed_base.
      exact Hprog. }
    eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_check_big_step_safe_checked_initial_ready_with_component_mixed_ready_body_or_narrow_provider.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + exact Hcombined_check.
    + exact Hprovider.
    + eapply component_body_local_bounds_mixed_route_provider_of_synthetic_and_provenance_ready.
      * exact Hroots_ready.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact Hframe_ready.
      * exact Hparam_ready.
      * exact (Hsynthetic_provider_when_no_receiver Hno_receiver).
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

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_route_providers_diagnostic :
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
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
        In f_component (env_fns env') ->
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env' f_component = true ->
        eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family
          (global_env_with_local_bounds env' (fn_bounds f_component))) ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hcombined_check Hsynthetic_provider_when_no_receiver
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    pose proof
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_mixed_routes
        Hroot_names Hroot_keys env env' Hprog Hcombined_check Hno_receiver
        (Hsynthetic_provider_when_no_receiver Hno_receiver)
        (Hshadow_provider_when_no_receiver Hno_receiver)) as
        (_Hsummary_provider & Hroute_provider & _Hcallback_provider).
    exact Hroute_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_synthetic_route_provider_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      forall f_component,
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env env'
    f s s' v Hprog Hcombined_check Hsynthetic_provider_when_no_receiver
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    pose proof
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_and_synthetic_route_provider
        Hroot_names Hroot_keys Hsummary_to_route env env' Hprog Hcombined_check
        Hno_receiver (Hsynthetic_provider_when_no_receiver Hno_receiver)) as
        (_Hsummary_provider & Hroute_provider & _Hcallback_provider).
    exact Hroute_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_and_shadow_route_provider_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_shadow_summary_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env
    env' f s s' v Hprog Hready_body_provider_check
    Hshadow_provider_when_no_receiver Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    pose proof
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_shadow_route_provider
        Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
        Hready_body_provider_check Hno_receiver
        (Hshadow_provider_when_no_receiver Hno_receiver)) as
        (_Hsummary_provider & Hroute_provider & _Hcallback_provider).
    exact Hroute_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_and_shadow_summary_bridge_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    env_fns_root_shadow_summary_evidence env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env
    env' f s s' v Hprog Hready_body_provider_check Hshadow_summary Hinitial
    Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    pose proof
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_and_shadow_summary_bridge
        Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
        Hready_body_provider_check Hno_receiver Hshadow_summary) as
        (_Hsummary_provider & Hroute_provider & _Hcallback_provider).
    exact Hroute_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env
    env' f s s' v Hprog Hcombined_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_ready_body_route_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    pose proof
      (infer_program_env_end2end_assoc_direct_receiver_mixed_ready_body_provider_bundle_of_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks
        Hroot_names Hroot_keys Hsummary_to_route env env' Hprog
        Hcombined_check Hno_receiver) as
        (_Hsummary_provider & Hroute_provider & _Hcallback_provider).
    exact Hroute_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_and_shadow_checks_diagnostic :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  ready_body_summary_local_bounds_family_route_bridge ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check
      env' = true ->
    check_env_root_shadow_provenance_summary env' = true ->
    check_env_preservation_ready env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_to_route env
    env' f s s' v Hprog Hready_body_provider_check Hprov_check Hpres_check
    Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_diagnostic.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hsummary_to_route.
  - exact Hprog.
  - eapply check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check_with_shadow_checks_of_checks;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_summary_provider_check_diagnostic :
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
    check_env_root_shadow_no_receiver_component_body_summary_provider_check
      env' = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env env' f s s' v
    Hprog Hcomponent_body_provider_check Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_no_receiver_component_body_local_bounds_synthetic_summary_provider.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros Hno_receiver.
    eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary_local_bounds_synthetic_summary_provider_sound.
    eapply check_env_root_shadow_no_receiver_component_body_summary_provider_check_sound;
      eassumption.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_public_premises_mixed_route_and_cleanup_callback :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hmixed_route Hcleanup
    env env' f s s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_mixed_route_cleanup_callback_providers.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact Hprog.
  - intros _Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_of_statement.
    exact Hmixed_route.
  - intros _Hno_receiver.
    eapply component_body_local_bounds_mixed_ready_body_or_narrow_cleanup_callback_provider_of_statement.
    exact Hcleanup.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_public_premises_mixed_route_and_cleanup_callback :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hmixed_route Hcleanup.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_public_premises_mixed_route_and_cleanup_callback;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_public_premises_mixed_route_and_cleanup_callback :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_summary_at_prefix_call_statement_evidence_at_height_statement ->
  eval_preserves_typing_roots_store_safe_mixed_ready_body_or_narrow_body_call_cleanup_callback_height_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hmixed_route Hcleanup.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_public_premises_mixed_route_and_cleanup_callback;
    eassumption.
Qed.

Theorem infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_public_premises_and_value_cleanup_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_value_cleanup_bridge_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge env env' f s
    s' v Hprog Hinitial Hin Hstore Heval.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_value_cleanup_bridge;
    eassumption.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_value_cleanup_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_value_cleanup_bridge_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_public_premises_and_value_cleanup_bridge;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_value_cleanup_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_value_cleanup_bridge_statement ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_value_cleanup_bridge;
    eassumption.
Qed.




Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_synthetic_evidence_at_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsynthetic_evidence_at.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_value_cleanup_bridge.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - eapply mixed_ready_body_or_narrow_value_cleanup_bridge_statement_of_synthetic_evidence_at_route.
    exact Hsynthetic_evidence_at.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_synthetic_evidence_at_prefix_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsynthetic_evidence_at.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_synthetic_evidence_at_route.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - eapply eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_summary_at_prefix_call_statement_evidence_at.
    exact Hsynthetic_evidence_at.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_component_mixed_route_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_component_mixed_route_provider;
    eassumption.
Qed.


Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_component_mixed_route_provider :
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
    (check_env_root_shadow_direct_receiver_method_present env' = false ->
      component_body_local_bounds_mixed_route_provider_in_env env') ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_component_mixed_route_provider;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_alpha_summary_route_value_callback_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hroute_bridge
    Hvalue_bridge.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_endpoint_local_certificate_and_alpha_summary_route_value_callback_bridge;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_summary_route_value_callback_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
  mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hroute_bridge
    Hvalue_bridge.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_alpha_summary_route_value_callback_bridge;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_alpha_summary_route_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_alpha_summary_route_value_callback_bridge;
    try eassumption.
  eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_alpha_route_bridge.
  exact Hbridge.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_summary_route_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_summary_route_value_callback_bridge;
    try eassumption.
  eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_alpha_route_bridge.
  exact Hbridge.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_summary_route_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_alpha_summary_route_value_callback_bridge;
    try eassumption.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
    exact Hbridge.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge.
    exact Hbridge.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_route_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  mixed_ready_body_or_narrow_summary_provider_route_bridge ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hbridge.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_summary_route_value_callback_bridge;
    try eassumption.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
    exact Hbridge.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge.
    exact Hbridge.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_exact_body_call_route_package :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
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
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready
    Hexact_body_target Hbody_package.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_alpha_summary_route_value_callback_bridge.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_route_bridge_of_summary_route_bridge.
    eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_exact_body_call_route_package.
    + exact Hscope_synthetic.
    + exact eval_preserves_typing_ready_prefix_mutual.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hexact_body_target.
    + exact Hbody_package.
  - eapply mixed_ready_body_or_narrow_alpha_summary_provider_value_callback_bridge_of_summary_route_bridge.
    eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_exact_body_call_route_package.
    + exact Hscope_synthetic.
    + exact eval_preserves_typing_ready_prefix_mutual.
    + exact Hprefix_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hexact_body_target.
    + exact Hbody_package.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_package :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
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
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hprefix_ready
    Hroots_ready Hroot_names Hroot_keys Hframe_ready Hparam_ready
    Hexact_body_target Hbody_package.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_big_step_safe_checked_initial_ready_with_exact_body_call_route_package;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_synthetic_shadow_summary_at_all :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  (forall env fname,
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env fname) ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_at_all.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_summary_route_bridge.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - eapply mixed_ready_body_or_narrow_summary_provider_route_bridge_of_prefix_statement_and_synthetic_shadow_summary_at_all.
    + exact Hsynthetic_route.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hsummary_at_all.
    + intros env0.
      eapply eval_preserves_typing_roots_store_safe_shadow_summary_at_prefix_call_statement_evidence_at_height_statement_in_env_of_provenance_ready_with_callee_summary.
      * exact Hroots_ready.
      * exact Hroot_names.
      * exact Hroot_keys.
      * exact Hframe_ready.
      * exact eval_preserves_typing_roots_ready_prefix_mutual.
      * exact Hparam_ready.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_with_synthetic_shadow_summary_at_all :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  (forall env fname,
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      env fname) ->
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
    Hroot_names Hroot_keys Hframe_ready Hparam_ready Hsummary_at_all.
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix_with_synthetic_shadow_summary_at_all;
    eassumption.
Qed.

Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix :
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
  - exact Hstatic.
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
  eapply infer_program_env_end2end_big_step_safe_checked_initial_ready_prefix.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (preservation_ready_expr_static_runtime_named_prefix_of_store
      preservation_ready_expr_static_runtime_named_prefix_store_complete).
Qed.
