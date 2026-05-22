From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export TypeSafety EnvRootSoundness.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition callee_body_root_check_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    infer_env_roots env fcall R_params =
      infer_ok (T_body, Γ_out, R_body, roots_body) /\
    preservation_ready_expr (fn_body fcall) /\
    roots_exclude_params_b (fn_params fcall) roots_body = true /\
    root_env_excludes_params_b (fn_params fcall) R_body = true.

Definition direct_call_callee_body_root_check_evidence
    (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    root_env_store_roots_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_check_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Lemma callee_body_root_ready_at_of_check_ready_at :
  forall env fcall R_params,
    callee_body_root_check_ready_at env fcall R_params ->
    callee_body_root_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hcheck.
  unfold callee_body_root_check_ready_at in Hcheck.
  destruct Hcheck as
    (T_body & Γ_out & R_body & roots_body &
      Hinfer & Hready & Hexclude_roots & Hexclude_env).
  pose proof (infer_env_roots_sound env fcall R_params T_body Γ_out
    R_body roots_body Hinfer) as Htyped_fn.
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as
    (T_body' & Γ_out' & Htyped & Hcompat & _).
  unfold callee_body_root_ready_at.
  exists T_body', Γ_out', R_body, roots_body.
  repeat split.
  - apply preservation_ready_implies_provenance_ready.
    exact Hready.
  - exact Hready.
  - exact Htyped.
  - exact Hcompat.
  - apply roots_exclude_params_b_sound.
    exact Hexclude_roots.
  - apply root_env_excludes_params_b_sound.
    exact Hexclude_env.
Qed.

Definition fn_root_summary_check_ready
    (env : global_env) (fdef : fn_def) : Prop :=
  exists T_body Γ_out R_body roots_body,
    infer_env_roots env fdef (initial_root_env_for_fn fdef) =
      infer_ok (T_body, Γ_out, R_body, roots_body) /\
    preservation_ready_expr (fn_body fdef) /\
    roots_exclude_params_b (fn_params fdef) roots_body = true /\
    root_env_excludes_params_b (fn_params fdef) R_body = true.

Definition env_fns_root_summary_check_ready (env : global_env) : Prop :=
  forall fdef,
    In fdef (env_fns env) ->
    fn_root_summary_check_ready env fdef.

Definition direct_call_callee_body_root_check_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_summary_check_ready env ->
  direct_call_callee_body_root_check_evidence env.

Lemma callee_body_root_ready_at_of_fn_root_summary_check :
  forall env fdef,
    fn_root_summary_check_ready env fdef ->
    callee_body_root_ready_at env fdef (initial_root_env_for_fn fdef).
Proof.
  intros env fdef Hsummary.
  unfold fn_root_summary_check_ready in Hsummary.
  destruct Hsummary as
    (T_body & Γ_out & R_body & roots_body &
      Hinfer & Hready & Hexclude_roots & Hexclude_env).
  apply callee_body_root_ready_at_of_check_ready_at.
  unfold callee_body_root_check_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma callee_body_root_ready_at_of_env_root_summary_check :
  forall env fdef,
    env_fns_root_summary_check_ready env ->
    In fdef (env_fns env) ->
    callee_body_root_ready_at env fdef (initial_root_env_for_fn fdef).
Proof.
  intros env fdef Hsummary Hin.
  apply callee_body_root_ready_at_of_fn_root_summary_check.
  exact (Hsummary fdef Hin).
Qed.

Lemma env_fns_root_summary_evidence_of_check :
  forall env,
    env_fns_root_summary_check_ready env ->
    env_fns_root_summary_evidence env.
Proof.
  intros env Hsummary fname fdef Hlookup.
  unfold env_fns_root_summary_evidence, callee_body_root_summary.
  apply callee_body_root_ready_at_of_env_root_summary_check.
  - exact Hsummary.
  - apply lookup_fn_in_name in Hlookup.
    exact (proj1 Hlookup).
Qed.

Lemma direct_call_callee_body_root_evidence_of_check :
  forall env,
    direct_call_callee_body_root_check_evidence env ->
    direct_call_callee_body_root_evidence env.
Proof.
  intros env Hcheck Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall
    σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args Hprov_args
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  apply callee_body_root_ready_at_of_check_ready_at.
  eapply Hcheck; eassumption.
Qed.
