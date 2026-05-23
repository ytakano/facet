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
