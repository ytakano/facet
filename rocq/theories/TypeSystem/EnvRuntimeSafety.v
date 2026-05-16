From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness TypeSafety EnvRootSoundness.
From Stdlib Require Import List.
Import ListNotations.

Definition initial_store_for_fn (env : global_env) (f : fn_def) (s : store) : Prop :=
  store_typed env s (sctx_of_ctx (params_ctx (fn_params f))).

Lemma initial_root_env_for_params_covers :
  forall ps,
    root_env_covers_params ps (initial_root_env_for_params ps).
Proof.
  induction ps as [| p ps IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Hx | Hin].
    + subst x. exists [RParam (param_name p)].
      simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl.
      destruct (ident_eqb x (param_name p)) eqn:Heq.
      * exists [RParam (param_name p)]. reflexivity.
      * destruct (IH x Hin) as [roots Hlookup].
        exists roots. exact Hlookup.
Qed.

Lemma initial_root_env_for_fn_covers :
  forall f,
    root_env_covers_params (fn_params f) (initial_root_env_for_fn f).
Proof.
  intros f.
  unfold initial_root_env_for_fn.
  apply initial_root_env_for_params_covers.
Qed.

Lemma call_body_start_state_param_scope :
  forall env Ω s_args vs ps,
    eval_args_values_have_types env Ω s_args vs ps ->
    store_param_scope ps (bind_params ps vs s_args) s_args /\
    root_env_covers_params ps (initial_root_env_for_params ps).
Proof.
  intros env Ω s_args vs ps Hargs.
  split.
  - eapply store_param_scope_bind_params. exact Hargs.
  - apply initial_root_env_for_params_covers.
Qed.

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
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
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
    σ s s_args vs used' Htyped_args Heval_args Hrename.
  apply callee_body_root_ready_at_of_check_ready_at.
  eapply Hcheck; eassumption.
Qed.

Theorem infer_full_env_roots_big_step_safe_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (params_ctx (fn_params f)))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Htyped)
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_check_evidence env ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  destruct (eval_preserves_typing_direct_call_roots_ready
      env s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (params_ctx (fn_params f)))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Htyped
      Hunique Hfns_ready
      (direct_call_callee_body_root_evidence_of_check env
        Hcallee_body_roots))
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.
