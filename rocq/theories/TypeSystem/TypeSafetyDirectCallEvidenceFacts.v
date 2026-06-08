From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness
  CheckerRootSidecars.
From Facet.TypeSystem Require Export TypeSafetyDirectCallBody.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition direct_call_callee_root_evidence (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    exists T_body Γ_out R_params R_body roots_body,
      store_roots_within R_params
        (bind_params (fn_params fcall) vs s_args) /\
      store_no_shadow (bind_params (fn_params fcall) vs s_args) /\
      root_env_no_shadow R_params /\
      root_env_covers_params (fn_params fcall) R_params /\
      provenance_ready_expr (fn_body fcall) /\
      preservation_ready_expr (fn_body fcall) /\
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
        (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    preservation_ready_expr (fn_body fcall) /\
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    preservation_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_direct_call_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    preservation_direct_call_ready_expr (fn_body fcall) /\
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_direct_call_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    preservation_direct_call_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_synthetic_direct_call_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists fname args synthetic_body T_body Γ_out R_body roots_body,
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    preservation_direct_call_ready_expr synthetic_body /\
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_synthetic_direct_call_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists fname args synthetic_body T_body Γ_out R_body roots_body,
    direct_call_target_expr (fn_body fcall) =
      Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    preservation_direct_call_ready_expr synthetic_body /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_provenance_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_provenance_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_provenance_ready_at_result_subset
    (env : global_env) (fcall : fn_def) (R_params : root_env)
    (roots_bound : root_set) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body /\
    root_set_stores_subset roots_body roots_bound.

Lemma callee_body_root_ready_at_of_shadow_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_ready_at env fcall R_params ->
    callee_body_root_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hshadow.
  unfold callee_body_root_shadow_ready_at in Hshadow.
  destruct Hshadow as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Hready & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma callee_body_root_direct_call_ready_at_of_ready_at :
  forall env fcall R_params,
    callee_body_root_ready_at env fcall R_params ->
    callee_body_root_direct_call_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hready.
  unfold callee_body_root_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      _ & Hpres & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_direct_call_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  apply PDCR_Ready. exact Hpres.
Qed.

Lemma callee_body_root_direct_call_ready_at_of_shadow_direct_call_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_direct_call_ready_at env fcall R_params ->
    callee_body_root_direct_call_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hshadow.
  unfold callee_body_root_shadow_direct_call_ready_at in Hshadow.
  destruct Hshadow as
    (T_body & Γ_out & R_body & roots_body &
      Hready & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_direct_call_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma callee_body_root_shadow_direct_call_ready_at_of_shadow_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_ready_at env fcall R_params ->
    callee_body_root_shadow_direct_call_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hready.
  unfold callee_body_root_shadow_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      _ & Hpres & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_shadow_direct_call_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  apply PDCR_Ready. exact Hpres.
Qed.

Lemma callee_body_root_synthetic_direct_call_ready_at_of_shadow :
  forall env fcall R_params,
    callee_body_root_shadow_synthetic_direct_call_ready_at env fcall
      R_params ->
    callee_body_root_synthetic_direct_call_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hshadow.
  unfold callee_body_root_shadow_synthetic_direct_call_ready_at in Hshadow.
  destruct Hshadow as
    (fname & args & synthetic_body & T_body & Γ_out & R_body &
      roots_body & Htarget & Hsynthetic & Hready & Htyped & Hcompat &
      Hexclude_roots & Hexclude_env).
  unfold callee_body_root_synthetic_direct_call_ready_at.
  exists fname, args, synthetic_body, T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_provenance_ready_at env fcall R_params ->
    callee_body_root_provenance_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hshadow.
  unfold callee_body_root_shadow_provenance_ready_at in Hshadow.
  destruct Hshadow as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma callee_body_root_provenance_ready_at_of_ready_at :
  forall env fcall R_params,
    callee_body_root_ready_at env fcall R_params ->
    callee_body_root_provenance_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hready.
  unfold callee_body_root_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & _ & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma callee_body_root_shadow_provenance_ready_at_of_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_ready_at env fcall R_params ->
    callee_body_root_shadow_provenance_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hready.
  unfold callee_body_root_shadow_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & _ & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_shadow_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma callee_body_root_shadow_ready_at_of_provenance_and_preservation :
  forall env fcall R_params,
    callee_body_root_shadow_provenance_ready_at env fcall R_params ->
    preservation_ready_expr (fn_body fcall) ->
    callee_body_root_shadow_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hprov_ready Hpres_ready.
  unfold callee_body_root_shadow_provenance_ready_at in Hprov_ready.
  destruct Hprov_ready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_shadow_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Definition callee_body_root_summary (env : global_env) (fdef : fn_def)
    : Prop :=
  callee_body_root_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_shadow_summary (env : global_env) (fdef : fn_def)
    : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_direct_call_ready_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_direct_call_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_shadow_direct_call_ready_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_direct_call_ready_at env fdef
    (initial_root_env_for_fn fdef).

Definition callee_body_root_synthetic_direct_call_ready_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_synthetic_direct_call_ready_at env fdef
    (initial_root_env_for_fn fdef).

Definition callee_body_root_shadow_synthetic_direct_call_ready_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_synthetic_direct_call_ready_at env fdef
    (initial_root_env_for_fn fdef).

Definition callee_body_root_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_provenance_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_shadow_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_provenance_ready_at env fdef
    (initial_root_env_for_fn fdef).

Definition env_fns_root_summary_evidence (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_summary env fdef.

Definition env_fns_root_shadow_summary_evidence (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_summary env fdef.

Definition env_fns_root_direct_call_ready_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_direct_call_ready_summary env fdef.

Definition env_fns_root_shadow_direct_call_ready_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_direct_call_ready_summary env fdef.

Definition env_fns_root_synthetic_direct_call_ready_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_synthetic_direct_call_ready_summary env fdef.

Definition env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary env fdef.

Definition env_fns_root_provenance_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_provenance_summary env fdef.

Definition env_fns_root_shadow_provenance_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.

Lemma env_fns_root_shadow_summary_evidence_in_unique :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    fn_env_unique_by_name env ->
    forall fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_summary env fdef.
Proof.
  intros env Hsummary Hunique fname fdef Hin Hname.
  unfold env_fns_root_shadow_summary_evidence in Hsummary.
  eapply Hsummary.
  eapply lookup_fn_in_unique_by_name; eassumption.
Qed.

Lemma env_fns_root_summary_evidence_of_shadow :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_summary_evidence in Hshadow.
  unfold callee_body_root_summary, callee_body_root_shadow_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [_ Hready].
  eapply callee_body_root_ready_at_of_shadow_ready_at.
  exact Hready.
Qed.

Lemma env_fns_root_shadow_provenance_summary_evidence_of_shadow :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_shadow_provenance_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_summary_evidence in Hshadow.
  unfold callee_body_root_shadow_summary,
    callee_body_root_shadow_provenance_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [Hnodup Hready].
  split.
  - exact Hnodup.
  - eapply callee_body_root_shadow_provenance_ready_at_of_ready_at.
    exact Hready.
Qed.

Lemma env_fns_root_direct_call_ready_summary_evidence_of_shadow :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_direct_call_ready_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_summary_evidence in Hshadow.
  unfold callee_body_root_shadow_summary,
    callee_body_root_direct_call_ready_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [_ Hready].
  eapply callee_body_root_direct_call_ready_at_of_ready_at.
  eapply callee_body_root_ready_at_of_shadow_ready_at.
  exact Hready.
Qed.

Lemma env_fns_root_shadow_direct_call_ready_summary_evidence_of_shadow :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_shadow_direct_call_ready_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_summary_evidence in Hshadow.
  unfold callee_body_root_shadow_summary,
    callee_body_root_shadow_direct_call_ready_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [Hnodup Hready].
  split.
  - exact Hnodup.
  - eapply callee_body_root_shadow_direct_call_ready_at_of_shadow_ready_at.
    exact Hready.
Qed.

Lemma env_fns_root_provenance_summary_evidence_of_shadow_provenance :
  forall env,
    env_fns_root_shadow_provenance_summary_evidence env ->
    env_fns_root_provenance_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_provenance_summary_evidence in Hshadow.
  unfold callee_body_root_provenance_summary,
    callee_body_root_shadow_provenance_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [_ Hready].
  eapply callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at.
  exact Hready.
Qed.

Lemma env_fns_root_shadow_summary_evidence_of_provenance_and_preservation :
  forall env,
    env_fns_root_shadow_provenance_summary_evidence env ->
    env_fns_preservation_ready env ->
    env_fns_root_shadow_summary_evidence env.
Proof.
  intros env Hprov Hpres fname fdef Hlookup.
  unfold env_fns_root_shadow_provenance_summary_evidence in Hprov.
  unfold callee_body_root_shadow_provenance_summary,
    callee_body_root_shadow_summary in *.
  destruct (Hprov fname fdef Hlookup) as [Hnodup Hready].
  split.
  - exact Hnodup.
  - eapply callee_body_root_shadow_ready_at_of_provenance_and_preservation.
    + exact Hready.
    + apply Hpres.
      destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
        as [Hin _].
      exact Hin.
Qed.

Definition direct_call_callee_body_root_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_shadow_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_shadow_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_shadow_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_evidence (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_direct_call_ready_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_direct_call_ready_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_direct_call_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_shadow_direct_call_ready_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_shadow_direct_call_ready_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_shadow_direct_call_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_synthetic_direct_call_ready_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_synthetic_direct_call_ready_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_synthetic_direct_call_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_shadow_synthetic_direct_call_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_direct_call_ready_evidence
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
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_direct_call_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_synthetic_direct_call_ready_evidence
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
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_synthetic_direct_call_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Lemma direct_call_callee_body_root_evidence_of_summary_bridge :
  forall env,
    env_fns_root_summary_evidence env ->
    direct_call_callee_body_root_summary_bridge env ->
    direct_call_callee_body_root_evidence env.
Proof.
  intros env Hsummary Hbridge Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply Hbridge; eassumption.
Qed.

Lemma direct_call_callee_body_root_evidence_of_shadow_summary_bridge :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    direct_call_callee_body_root_shadow_summary_bridge env ->
    direct_call_callee_body_root_evidence env.
Proof.
  intros env Hsummary Hbridge Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply callee_body_root_ready_at_of_shadow_ready_at.
  eapply Hbridge; eassumption.
Qed.

Lemma direct_call_callee_body_root_direct_call_ready_summary_bridge_of_summary_bridge :
  forall env,
    env_fns_root_summary_evidence env ->
    direct_call_callee_body_root_summary_bridge env ->
    direct_call_callee_body_root_direct_call_ready_summary_bridge env.
Proof.
  intros env Hsummary Hbridge _ Ω n R Σ Σ_args R_args arg_roots fname
    args fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args
    Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply callee_body_root_direct_call_ready_at_of_ready_at.
  eapply Hbridge; eassumption.
Qed.

Lemma direct_call_callee_body_root_shadow_direct_call_ready_summary_bridge_of_shadow_summary_bridge :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    direct_call_callee_body_root_shadow_summary_bridge env ->
    direct_call_callee_body_root_shadow_direct_call_ready_summary_bridge env.
Proof.
  intros env Hsummary Hbridge _ Ω n R Σ Σ_args R_args arg_roots fname
    args fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args
    Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply callee_body_root_shadow_direct_call_ready_at_of_shadow_ready_at.
  eapply Hbridge; eassumption.
Qed.

Lemma direct_call_callee_body_root_direct_call_ready_evidence_of_evidence :
  forall env,
    direct_call_callee_body_root_evidence env ->
    direct_call_callee_body_root_direct_call_ready_evidence env.
Proof.
  intros env Hevidence Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply callee_body_root_direct_call_ready_at_of_ready_at.
  eapply Hevidence; eassumption.
Qed.

Lemma direct_call_callee_body_root_direct_call_ready_evidence_of_summary_bridge :
  forall env,
    env_fns_root_direct_call_ready_summary_evidence env ->
    direct_call_callee_body_root_direct_call_ready_summary_bridge env ->
    direct_call_callee_body_root_direct_call_ready_evidence env.
Proof.
  intros env Hsummary Hbridge Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply Hbridge; eassumption.
Qed.

Lemma direct_call_callee_body_root_direct_call_ready_evidence_of_shadow_summary_bridge :
  forall env,
    env_fns_root_shadow_direct_call_ready_summary_evidence env ->
    direct_call_callee_body_root_shadow_direct_call_ready_summary_bridge env ->
    direct_call_callee_body_root_direct_call_ready_evidence env.
Proof.
  intros env Hsummary Hbridge Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply callee_body_root_direct_call_ready_at_of_shadow_direct_call_ready_at.
  eapply Hbridge; eassumption.
Qed.
