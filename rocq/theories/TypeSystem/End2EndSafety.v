From Facet.TypeSystem Require Import Types Syntax Program RootProvenance TypeChecker EnvRootSoundness.
From Stdlib Require Import List Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* End-to-end checker entrypoint soundness                              *)
(* ------------------------------------------------------------------ *)

Theorem infer_fn_env_end2end_sound :
  forall env f T Γ_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) ->
    checked_fn_env_roots env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Γ_out R_out roots Hend.
  unfold infer_fn_env_end2end in Hend.
  remember (initial_root_env_for_params (fn_params f ++ fn_captures f))
    as R0 eqn:HR0.
  destruct (infer_full_env_roots env f R0)
    as [[[[T0 Γ0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_captured_call_provenance_summary env f);
    try discriminate.
  injection Hend as <- <- <- <-.
  eapply infer_full_env_roots_sound. exact Hroots.
Qed.

Lemma infer_fns_env_end2end_in_sound :
  forall env fns f,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end env f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots env f
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
    env' = alpha_normalize_global_env env /\
    exists T Γ_out R_out roots,
      infer_fn_env_end2end env' f = infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_fns_env_end2end env_alpha (env_fns env_alpha))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  split; [reflexivity |].
  eapply infer_fns_env_end2end_in_sound; eauto.
Qed.

Theorem check_program_env_end2end_sound :
  forall env f,
    check_program_env_end2end env = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    exists T Γ_out R_out roots,
      infer_fn_env_end2end (alpha_normalize_global_env env) f =
        infer_ok (T, Γ_out, R_out, roots) /\
      checked_fn_env_roots (alpha_normalize_global_env env) f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env f Hcheck Hin.
  unfold check_program_env_end2end in Hcheck.
  destruct (infer_program_env_end2end env) as [env' | err] eqn:Hprog;
    try discriminate.
  assert (Hin' : In f (env_fns env')).
  { unfold infer_program_env_end2end in Hprog.
    set (env_alpha := alpha_normalize_global_env env) in *.
    destruct (global_names_unique_b env_alpha); try discriminate.
    destruct (infer_fns_env_end2end env_alpha (env_fns env_alpha)) as [[] | err];
      try discriminate.
    injection Hprog as <-. exact Hin. }
  destruct (infer_program_env_end2end_sound env env' f Hprog Hin')
    as [Heq Hsound].
  rewrite Heq in Hsound. exact Hsound.
Qed.
