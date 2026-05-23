From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeShadowExprCheckerFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition ordinary_alpha_root_shadow_validator_ready
    (env : global_env) : Prop :=
  env_fns_root_shadow_summary_check_ready (alpha_normalize_global_env env).

Definition ordinary_alpha_direct_call_validated_root_shadow_validator_ready
    (env : global_env) : Prop :=
  ordinary_alpha_root_shadow_validator_ready env /\
  env_fns_preservation_ready (alpha_normalize_global_env env).

Definition ordinary_alpha_root_shadow_provenance_validator_ready
    (env : global_env) : Prop :=
  env_fns_root_shadow_provenance_summary_check_ready
    (alpha_normalize_global_env env).

Definition ordinary_alpha_root_shadow_direct_call_provenance_validator_ready
    (env : global_env) : Prop :=
  env_fns_root_shadow_direct_call_provenance_summary_check_ready
    (alpha_normalize_global_env env).

Definition ordinary_alpha_root_shadow_captured_call_provenance_validator_ready
    (env : global_env) : Prop :=
  env_fns_root_shadow_captured_call_provenance_summary_check_ready
    (alpha_normalize_global_env env).

Lemma check_program_env_alpha_validated_root_shadow_ready :
  forall env,
    check_program_env_alpha_validated_root_shadow env = true ->
    ordinary_alpha_direct_call_validated_root_shadow_validator_ready env.
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated_root_shadow in Hcheck.
  apply andb_true_iff in Hcheck as [_ Hshadow].
  split.
  - apply check_env_root_shadow_summary_ready.
    exact Hshadow.
  - apply check_env_root_shadow_summary_preservation_ready.
    exact Hshadow.
Qed.

Lemma check_program_env_alpha_validated_root_shadow_provenance_summary_ready :
  forall env,
    check_program_env_alpha_validated_root_shadow_provenance_summary env = true ->
    ordinary_alpha_root_shadow_provenance_validator_ready env.
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated_root_shadow_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [_ Hprov].
  apply check_env_root_shadow_provenance_summary_ready.
  exact Hprov.
Qed.

Lemma check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_ready :
  forall env,
    check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary env = true ->
    ordinary_alpha_root_shadow_direct_call_provenance_validator_ready env.
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [_ Hsummary].
  apply check_env_root_shadow_direct_call_provenance_summary_ready.
  exact Hsummary.
Qed.

Lemma check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary_ready :
  forall env,
    check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary env = true ->
    ordinary_alpha_root_shadow_captured_call_provenance_validator_ready env.
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [_ Hsummary].
  apply check_env_root_shadow_captured_call_provenance_summary_ready.
  exact Hsummary.
Qed.

Lemma check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary_ready :
  forall env env',
    check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary env = true ->
    infer_program_env_alpha_elab env = infer_ok env' ->
    env_fns_root_shadow_captured_call_provenance_summary_check_ready env'.
Proof.
  intros env env' Hcheck Helab.
  unfold
    check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [_ Hsummary].
  rewrite Helab in Hsummary.
  apply check_env_root_shadow_captured_call_provenance_summary_ready.
  exact Hsummary.
Qed.

Lemma infer_env_elab_fn_name :
  forall env f T Γ f',
    infer_env_elab env f = infer_ok (T, Γ, f') ->
    fn_name f' = fn_name f.
Proof.
  intros env f T Γ f' Helab.
  unfold infer_env_elab in Helab.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f))
             (fn_outlives f))) eqn:?; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f))
             (fn_ret f))) eqn:?; try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f)
    eqn:?; try discriminate.
  destruct (infer_core_env_elab env (fn_outlives f) (fn_lifetimes f)
             (fn_body_ctx f) (fn_body f))
    as [[[T_body Γ_out] body'] | err] eqn:?; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body))
    eqn:?; try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:?; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_out)
    eqn:?; try discriminate.
  inversion Helab; subst.
  unfold fn_with_body. reflexivity.
Qed.

Lemma infer_full_env_elab_fn_name :
  forall env f T Γ f',
    infer_full_env_elab env f = infer_ok (T, Γ, f') ->
    fn_name f' = fn_name f.
Proof.
  intros env f T Γ f' Hfull.
  unfold infer_full_env_elab in Hfull.
  destruct (infer_env_elab env f) as [[[T0 Γ0] f0] | err] eqn:Helab;
    try discriminate.
  destruct (borrow_check_env env [] (fn_body_ctx f0) (fn_body f0))
    as [pbs | err] eqn:?; try discriminate.
  inversion Hfull; subst.
  eapply infer_env_elab_fn_name. exact Helab.
Qed.

Lemma infer_fns_env_elab_fn_names :
  forall env fns fns',
    infer_fns_env_elab env fns = infer_ok fns' ->
    map fn_name fns' = map fn_name fns.
Proof.
  intros env fns.
  induction fns as [| f rest IH]; intros fns' Helab.
  - simpl in Helab. inversion Helab. reflexivity.
  - simpl in Helab.
    destruct (infer_full_env_elab env f) as [[[T Γ] f'] | err] eqn:Hfull;
      try discriminate.
    destruct (infer_fns_env_elab env rest) as [rest' | err] eqn:Hrest;
      try discriminate.
    inversion Helab; subst.
    simpl. f_equal.
    + eapply infer_full_env_elab_fn_name. exact Hfull.
    + apply IH. reflexivity.
Qed.

Lemma fn_name_strings_of_fn_names :
  forall fns1 fns2,
    map fn_name fns1 = map fn_name fns2 ->
    fn_name_strings fns1 = fn_name_strings fns2.
Proof.
  unfold fn_name_strings.
  induction fns1 as [| f1 rest1 IH]; destruct fns2 as [| f2 rest2];
    simpl; intros Hnames; try discriminate.
  - reflexivity.
  - injection Hnames as Hnames_tail Hnames_head.
    f_equal.
    + rewrite Hnames_tail. reflexivity.
    + apply IH. exact Hnames_head.
Qed.

Lemma infer_program_env_alpha_elab_unique_by_name :
  forall env env',
    top_level_names_unique_b (alpha_normalize_global_env env) = true ->
    infer_program_env_alpha_elab env = infer_ok env' ->
    fn_env_unique_by_name env'.
Proof.
  intros env env' Hunique Helab.
  unfold infer_program_env_alpha_elab in Helab.
  destruct (infer_fns_env_elab (alpha_normalize_global_env env)
              (env_fns (alpha_normalize_global_env env)))
    as [fns' | err] eqn:Hfns; try discriminate.
  inversion Helab; subst.
  apply fn_name_strings_nodup_unique_by_name.
  simpl.
  pose proof (top_level_names_unique_b_fn_names_nodup
    (alpha_normalize_global_env env) Hunique) as Hnodup.
  pose proof (infer_fns_env_elab_fn_names
    (alpha_normalize_global_env env)
    (env_fns (alpha_normalize_global_env env)) fns' Hfns) as Hnames.
  pose proof (fn_name_strings_of_fn_names fns'
    (env_fns (alpha_normalize_global_env env)) Hnames) as Hstrings.
  rewrite Hstrings.
  exact Hnodup.
Qed.

Lemma check_program_env_alpha_validated_root_shadow_provenance_ready :
  forall env,
    check_program_env_alpha_validated_root_shadow_provenance env = true ->
    ordinary_alpha_direct_call_validated_root_shadow_validator_ready env.
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated_root_shadow_provenance in Hcheck.
  apply andb_true_iff in Hcheck as [_ Hvalidators].
  apply andb_true_iff in Hvalidators as [Hprov Hpres].
  split.
  - eapply env_fns_root_shadow_summary_check_ready_of_provenance_and_preservation.
    + apply check_env_root_shadow_provenance_summary_ready.
      exact Hprov.
    + apply check_env_preservation_ready_sound.
      exact Hpres.
  - apply check_env_preservation_ready_sound.
    exact Hpres.
Qed.

Definition ordinary_alpha_root_shadow_sidecar_ready (env : global_env) : Prop :=
  env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env).

Definition ordinary_alpha_direct_call_meta_ready (env : global_env) : Prop :=
  fn_env_unique_by_name (alpha_normalize_global_env env) /\
  env_fns_preservation_ready (alpha_normalize_global_env env).

Definition ordinary_alpha_direct_call_sidecar_ready (env : global_env) : Prop :=
  ordinary_alpha_root_shadow_sidecar_ready env /\
  ordinary_alpha_direct_call_meta_ready env.

Definition ordinary_alpha_direct_call_validated_sidecar_ready
    (env : global_env) : Prop :=
  ordinary_alpha_root_shadow_sidecar_ready env /\
  env_fns_preservation_ready (alpha_normalize_global_env env).

Lemma ordinary_alpha_root_shadow_sidecar_ready_intro :
  forall env,
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    ordinary_alpha_root_shadow_sidecar_ready env.
Proof.
  intros env Hroot_shadow.
  exact Hroot_shadow.
Qed.

Lemma env_fns_root_shadow_summary_evidence_of_check_ready :
  forall env,
    env_fns_root_shadow_summary_check_ready env ->
    env_fns_root_shadow_summary_evidence env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  exact (Hcheck fname fdef Hlookup).
Qed.

Lemma ordinary_alpha_root_shadow_sidecar_ready_of_validator_ready :
  forall env,
    ordinary_alpha_root_shadow_validator_ready env ->
    ordinary_alpha_root_shadow_sidecar_ready env.
Proof.
  intros env Hvalidator.
  apply ordinary_alpha_root_shadow_sidecar_ready_intro.
  apply env_fns_root_shadow_summary_evidence_of_check_ready.
  exact Hvalidator.
Qed.

Lemma env_fns_root_shadow_provenance_summary_evidence_of_check_ready :
  forall env,
    env_fns_root_shadow_provenance_summary_check_ready env ->
    env_fns_root_shadow_provenance_summary_evidence env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  exact (Hcheck fname fdef Hlookup).
Qed.

Lemma ordinary_alpha_root_shadow_provenance_evidence_of_validator_ready :
  forall env,
    ordinary_alpha_root_shadow_provenance_validator_ready env ->
    env_fns_root_shadow_provenance_summary_evidence
      (alpha_normalize_global_env env).
Proof.
  intros env Hvalidator.
  apply env_fns_root_shadow_provenance_summary_evidence_of_check_ready.
  exact Hvalidator.
Qed.

Lemma ordinary_alpha_root_shadow_sidecar_ready_evidence :
  forall env,
    ordinary_alpha_root_shadow_sidecar_ready env ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env).
Proof.
  intros env Hroot_shadow.
  exact Hroot_shadow.
Qed.

Lemma ordinary_alpha_direct_call_meta_ready_intro :
  forall env,
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    ordinary_alpha_direct_call_meta_ready env.
Proof.
  intros env Hunique Hfns_ready.
  split; assumption.
Qed.

Lemma ordinary_alpha_direct_call_meta_ready_unique :
  forall env,
    ordinary_alpha_direct_call_meta_ready env ->
    fn_env_unique_by_name (alpha_normalize_global_env env).
Proof.
  intros env Hmeta.
  destruct Hmeta as [Hunique _].
  exact Hunique.
Qed.

Lemma ordinary_alpha_direct_call_meta_ready_preservation_ready :
  forall env,
    ordinary_alpha_direct_call_meta_ready env ->
    env_fns_preservation_ready (alpha_normalize_global_env env).
Proof.
  intros env Hmeta.
  destruct Hmeta as [_ Hfns_ready].
  exact Hfns_ready.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_intro :
  forall env,
    ordinary_alpha_root_shadow_sidecar_ready env ->
    ordinary_alpha_direct_call_meta_ready env ->
    ordinary_alpha_direct_call_sidecar_ready env.
Proof.
  intros env Hroot_shadow Hmeta.
  split; assumption.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_package :
  forall env,
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    ordinary_alpha_direct_call_sidecar_ready env.
Proof.
  intros env Hroot_shadow Hunique Hfns_ready.
  apply ordinary_alpha_direct_call_sidecar_ready_intro.
  - apply ordinary_alpha_root_shadow_sidecar_ready_intro.
    exact Hroot_shadow.
  - apply ordinary_alpha_direct_call_meta_ready_intro; assumption.
Qed.

Lemma ordinary_alpha_direct_call_validated_sidecar_ready_of_root_shadow_validator_ready :
  forall env,
    ordinary_alpha_direct_call_validated_root_shadow_validator_ready env ->
    ordinary_alpha_direct_call_validated_sidecar_ready env.
Proof.
  intros env Hvalidator.
  destruct Hvalidator as [Hroot_shadow Hfns_ready].
  split.
  - apply ordinary_alpha_root_shadow_sidecar_ready_of_validator_ready.
    exact Hroot_shadow.
  - exact Hfns_ready.
Qed.

Lemma check_program_env_alpha_validated_unique :
  forall env,
    check_program_env_alpha_validated env = true ->
    fn_env_unique_by_name (alpha_normalize_global_env env).
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hunique _].
  apply top_level_names_unique_b_fn_env_unique_by_name.
  exact Hunique.
Qed.

Lemma check_program_env_alpha_validated_checked :
  forall env,
    check_program_env_alpha_validated env = true ->
    check_program_env_alpha env = true.
Proof.
  intros env Hcheck.
  unfold check_program_env_alpha_validated in Hcheck.
  apply andb_true_iff in Hcheck.
  exact (proj2 Hcheck).
Qed.

Lemma ordinary_alpha_direct_call_validated_sidecar_ready_package :
  forall env,
    check_program_env_alpha_validated env = true ->
    ordinary_alpha_direct_call_validated_sidecar_ready env ->
    ordinary_alpha_direct_call_sidecar_ready env.
Proof.
  intros env Hcheck Hsidecar.
  destruct Hsidecar as [Hroot_shadow Hfns_ready].
  apply ordinary_alpha_direct_call_sidecar_ready_intro.
  - exact Hroot_shadow.
  - apply ordinary_alpha_direct_call_meta_ready_intro.
    + apply check_program_env_alpha_validated_unique.
      exact Hcheck.
    + exact Hfns_ready.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_root_shadow :
  forall env,
    ordinary_alpha_direct_call_sidecar_ready env ->
    ordinary_alpha_root_shadow_sidecar_ready env.
Proof.
  intros env Hsidecar.
  destruct Hsidecar as [Hroot_shadow _].
  exact Hroot_shadow.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_meta :
  forall env,
    ordinary_alpha_direct_call_sidecar_ready env ->
    ordinary_alpha_direct_call_meta_ready env.
Proof.
  intros env Hsidecar.
  destruct Hsidecar as [_ Hmeta].
  exact Hmeta.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_root_shadow_evidence :
  forall env,
    ordinary_alpha_direct_call_sidecar_ready env ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env).
Proof.
  intros env Hsidecar.
  apply ordinary_alpha_root_shadow_sidecar_ready_evidence.
  apply ordinary_alpha_direct_call_sidecar_ready_root_shadow.
  exact Hsidecar.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_unique :
  forall env,
    ordinary_alpha_direct_call_sidecar_ready env ->
    fn_env_unique_by_name (alpha_normalize_global_env env).
Proof.
  intros env Hsidecar.
  apply ordinary_alpha_direct_call_meta_ready_unique.
  apply ordinary_alpha_direct_call_sidecar_ready_meta.
  exact Hsidecar.
Qed.

Lemma ordinary_alpha_direct_call_sidecar_ready_preservation_ready :
  forall env,
    ordinary_alpha_direct_call_sidecar_ready env ->
    env_fns_preservation_ready (alpha_normalize_global_env env).
Proof.
  intros env Hsidecar.
  apply ordinary_alpha_direct_call_meta_ready_preservation_ready.
  apply ordinary_alpha_direct_call_sidecar_ready_meta.
  exact Hsidecar.
Qed.
