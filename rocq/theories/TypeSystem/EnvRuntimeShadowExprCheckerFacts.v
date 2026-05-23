From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeShadowEvalFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma direct_call_target_expr_synthetic_call :
  forall e fname args synthetic_body,
    direct_call_target_expr e = Some (fname, args, synthetic_body) ->
    synthetic_body = ECall fname args.
Proof.
  intros e fname args synthetic_body Htarget.
  unfold direct_call_target_expr in Htarget.
  destruct e; try discriminate.
  - inversion Htarget. reflexivity.
  - destruct e; try discriminate.
    inversion Htarget. reflexivity.
Qed.

Lemma direct_call_target_expr_ok_is_call :
  forall fuel env Ω n R Σ e T Σ' R' roots fname args synthetic_body,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    direct_call_target_expr e = Some (fname, args, synthetic_body) ->
    e = ECall fname args /\ synthetic_body = ECall fname args.
Proof.
  intros fuel env Ω n R Σ e T Σ' R' roots fname args synthetic_body
    Hinfer Htarget.
  unfold direct_call_target_expr in Htarget.
  destruct e; try discriminate.
  - inversion Htarget; subst. split; reflexivity.
  - destruct e; try discriminate.
    destruct fuel; simpl in Hinfer; discriminate.
Qed.

Lemma captured_call_target_expr_ok_is_make_closure_call :
  forall fuel env Ω n R Σ e T Σ' R' roots fname captures args,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    captured_call_target_expr e = Some (fname, captures, args) ->
    e = ECallExpr (EMakeClosure fname captures) args.
Proof.
  intros fuel env Ω n R Σ e T Σ' R' roots fname captures args
    Hinfer Htarget.
  unfold captured_call_target_expr in Htarget.
  destruct e; try discriminate.
  destruct e; try discriminate.
  inversion Htarget. reflexivity.
Qed.

Lemma check_expr_root_shadow_captured_call_provenance_summary_fuel_sound :
  forall fuel env Ω n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_captured_call_provenance_summary_fuel
      fuel env Ω n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots ret_roots.
Proof.
  eapply check_expr_root_shadow_captured_call_provenance_summary_fuel_sound_early;
    eassumption.
Qed.

Lemma check_expr_root_shadow_captured_call_provenance_summary_sound :
  forall env Ω n R Γ e T Γ' R' roots,
    infer_core_env_roots_shadow_safe env Ω n R Γ e =
      infer_ok (T, Γ', R', roots) ->
    check_expr_root_shadow_captured_call_provenance_summary
      env Ω n R Γ e = true ->
    exists ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R (sctx_of_ctx Γ) e T (sctx_of_ctx Γ') R' roots ret_roots.
Proof.
  unfold check_expr_root_shadow_captured_call_provenance_summary,
    infer_core_env_roots_shadow_safe.
  intros env Ω n R Γ e T Γ' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Ω n R
    (sctx_of_ctx Γ) e) as [[[[T0 Σ0] R0] roots0] | err] eqn:Hstate;
    try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_captured_call_provenance_summary_fuel_sound;
    eassumption.
Qed.

Lemma check_fn_root_shadow_summary_preservation_ready :
  forall env fdef,
    check_fn_root_shadow_summary env fdef = true ->
    preservation_ready_expr (fn_body fdef).
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready _].
  apply preservation_ready_expr_b_sound. exact Hready.
Qed.

Lemma check_env_root_shadow_summary_preservation_ready :
  forall env,
    check_env_root_shadow_summary env = true ->
    env_fns_preservation_ready env.
Proof.
  intros env Hcheck fdef Hin.
  unfold check_env_root_shadow_summary in Hcheck.
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_summary_preservation_ready with (env := env).
  exact Hcheck.
Qed.

Lemma check_env_preservation_ready_sound :
  forall env,
    check_env_preservation_ready env = true ->
    env_fns_preservation_ready env.
Proof.
  intros env Hcheck fdef Hin.
  unfold check_env_preservation_ready in Hcheck.
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply preservation_ready_expr_b_sound. exact Hcheck.
Qed.

Lemma env_fns_root_shadow_summary_check_ready_of_provenance_and_preservation :
  forall env,
    env_fns_root_shadow_provenance_summary_check_ready env ->
    env_fns_preservation_ready env ->
    env_fns_root_shadow_summary_check_ready env.
Proof.
  intros env Hprov Hpres fname fdef Hlookup.
  pose proof
    (env_fns_root_shadow_summary_evidence_of_provenance_and_preservation
      env Hprov Hpres) as Hsummary.
  exact (Hsummary fname fdef Hlookup).
Qed.
