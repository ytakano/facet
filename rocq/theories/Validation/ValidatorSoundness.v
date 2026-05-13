From Facet.TypeSystem Require Import Program.
From Facet.Validation Require Import Validator.

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
