From Facet.TypeSystem Require Import Program TypeChecker EnvStructuralRules
  EnvFullSoundness.
From Facet.Validation Require Import Validator.
From Stdlib Require Import Bool List.

Theorem valid_global_env_components : forall env,
  ValidEnv env ->
  string_no_dup_b (global_names env) = true /\
  structs_acyclic_b (env_structs env) = true /\
  forallb (struct_wf_b (env_structs env) (env_traits env)) (env_structs env) = true /\
  forallb (trait_wf_b (env_traits env)) (env_traits env) = true /\
  impl_no_dup_b (env_impls env) = true /\
  forallb (impl_wf_b (env_structs env) (env_traits env)) (env_impls env) = true /\
  forallb (fn_types_wf_b (env_structs env)) (env_fns env) = true.
Proof.
  intros env H.
  unfold ValidEnv, valid_global_env_b in H.
  apply andb_true_iff in H as [H Hfns].
  apply andb_true_iff in H as [H Himpls].
  apply andb_true_iff in H as [H Himplnodup].
  apply andb_true_iff in H as [H Htraits].
  apply andb_true_iff in H as [H Hstructs].
  apply andb_true_iff in H as [Hnames Hacyclic].
  repeat split; assumption.
Qed.

Theorem validate_env_components : forall env env',
  validate_env env = Some env' ->
  env' = env /\
  string_no_dup_b (global_names env') = true /\
  structs_acyclic_b (env_structs env') = true /\
  forallb (struct_wf_b (env_structs env') (env_traits env')) (env_structs env') = true /\
  forallb (trait_wf_b (env_traits env')) (env_traits env') = true /\
  impl_no_dup_b (env_impls env') = true /\
  forallb (impl_wf_b (env_structs env') (env_traits env')) (env_impls env') = true /\
  forallb (fn_types_wf_b (env_structs env')) (env_fns env') = true.
Proof.
  intros env env' H.
  unfold validate_env in H.
  destruct (valid_global_env_b env) eqn:Hvalid; inversion H; subst.
  split; [reflexivity |].
  apply valid_global_env_components. exact Hvalid.
Qed.

Theorem validate_env_sound : forall env env',
  validate_env env = Some env' ->
  env' = env /\ ValidEnv env'.
Proof.
  intros env env' H.
  unfold validate_env in H.
  destruct (valid_global_env_b env) eqn:Hvalid; inversion H; subst.
  split; [reflexivity | exact Hvalid].
Qed.

Theorem validate_fns_sound : forall fenv env,
  validate_fns fenv = Some env ->
  env = empty_global_env fenv /\ ValidEnv env.
Proof.
  intros fenv env H.
  unfold validate_fns in H.
  apply validate_env_sound in H.
  exact H.
Qed.

Theorem infer_full_env_structural_sound : forall env f T Γ',
  ValidEnv env ->
  infer_full_env env f = infer_ok (T, Γ') ->
  checked_fn_env_structural env f.
Proof.
  intros env f T Γ' _ Hfull.
  eapply infer_full_env_structural_sound_unvalidated. exact Hfull.
Qed.

Theorem validate_env_infer_full_env_structural_sound : forall env env' f T Γ',
  validate_env env = Some env' ->
  infer_full_env env' f = infer_ok (T, Γ') ->
  checked_fn_env_structural env' f.
Proof.
  intros env env' f T Γ' Hvalidate Hfull.
  destruct (validate_env_sound env env' Hvalidate) as [_ Hvalid].
  eapply infer_full_env_structural_sound; eassumption.
Qed.

Theorem validate_fns_infer_full_env_structural_sound : forall fenv env f T Γ',
  validate_fns fenv = Some env ->
  infer_full_env env f = infer_ok (T, Γ') ->
  checked_fn_env_structural env f.
Proof.
  intros fenv env f T Γ' Hvalidate Hfull.
  destruct (validate_fns_sound fenv env Hvalidate) as [_ Hvalid].
  eapply infer_full_env_structural_sound; eassumption.
Qed.
