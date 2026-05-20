From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness TypeSafety
  EnvRootSoundness.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition initial_store_for_fn (env : global_env) (f : fn_def) (s : store) : Prop :=
  store_typed env s (sctx_of_ctx (fn_body_ctx f)).

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

Lemma runtime_struct_expr_true : forall e,
  struct_expr e = true.
Proof.
  fix IH 1.
  intro e.
  destruct e; simpl; try reflexivity.
  - rewrite IH, IH. reflexivity.
  - rewrite IH, IH. reflexivity.
  - induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l1 as [| [fname field] rest IHfields]; simpl.
    + reflexivity.
    + rewrite IH, IHfields. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, IH, IH. reflexivity.
Qed.

Lemma infer_core_env_runtime_structural_sound :
  forall env Ω n Γ e T Γ',
    infer_core_env env Ω n Γ e = infer_ok (T, Γ') ->
    typed_env_structural env Ω n (sctx_of_ctx Γ) e T (sctx_of_ctx Γ').
Proof.
  unfold infer_core_env, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n Γ e T Γ' Hinfer.
  destruct (infer_core_env_state_fuel 10000 env Ω n Γ e) as [[T0 Σ] | err]
    eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_struct_structural_sound.
  - apply runtime_struct_expr_true.
  - exact Hcore.
Qed.

Lemma infer_env_runtime_structural_sound :
  forall env f T Γ',
    infer_env env f = infer_ok (T, Γ') ->
    typed_fn_env_structural env f.
Proof.
  unfold infer_env, typed_fn_env_structural.
  intros env f T Γ' Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env env (fn_outlives f) (fn_lifetimes f)
              (fn_body_ctx f) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompatible; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_out) eqn:Hparams;
    try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ'.
  repeat split.
  - eapply infer_core_env_runtime_structural_sound. exact Hcore.
  - exact Hcompatible.
  - exact Hparams.
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
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Htyped)
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready
    Hroots Hstore_shadow Hroot_shadow Heval.
  eapply infer_full_env_roots_big_step_safe_ready; eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_structural_ready :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_ready_expr (fn_body f) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v Hinfer Hstore Hready Heval.
  unfold infer_full_env in Hinfer.
  destruct (infer_env (alpha_normalize_global_env env) f)
    as [[T0 Γ0] | err] eqn:Hinfer_env; try discriminate.
  destruct (borrow_check_env (alpha_normalize_global_env env) []
              (fn_body_ctx f) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  eapply typed_fn_env_structural_big_step_safe_ready.
  - eapply infer_env_runtime_structural_sound. exact Hinfer_env.
  - exact Hready.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_check_evidence env ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  destruct (eval_preserves_typing_direct_call_roots_ready
      env s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique Hfns_ready
      (direct_call_callee_body_root_evidence_of_check env
        Hcallee_body_roots))
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_big_step_safe_direct_call_evidence :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name env ->
    env_fns_preservation_ready env ->
    direct_call_callee_body_root_evidence env ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Hcallee_body_roots Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped [Hcompat _]]]].
  destruct (eval_preserves_typing_direct_call_roots_ready
      env s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique Hfns_ready Hcallee_body_roots)
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_direct_call_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_check_evidence (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready Hroots
    Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready Hcallee_roots Heval.
  eapply infer_full_env_roots_big_step_safe_direct_call_ready; eassumption.
Qed.

Theorem infer_full_env_roots_alpha_big_step_safe_direct_call_evidence :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_evidence (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hstore Hready Hroots
    Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready Hcallee_roots Heval.
  eapply infer_full_env_roots_big_step_safe_direct_call_evidence;
    eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_summary_check_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_summary_bridge (alpha_normalize_global_env env) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hsummary
    Hbridge Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_evidence;
    try eassumption.
  eapply direct_call_callee_body_root_evidence_of_summary_bridge.
  - apply env_fns_root_summary_evidence_of_check. exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_shadow_summary_bridge
      (alpha_normalize_global_env env) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hsummary
    Hbridge Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_evidence;
    try eassumption.
  eapply direct_call_callee_body_root_evidence_of_shadow_summary_bridge.
  - exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge_of_unique :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hroots_infer Hsummary
    Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge;
    try eassumption.
  apply direct_call_callee_body_root_shadow_summary_bridge_of_unique.
  exact Hunique.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_shadow_summary_sidecar :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v Hinfer Hroots_infer Hsummary
    Hstore Hready Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique
    Hfns_ready Heval.
  eapply infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge_of_unique;
    eassumption.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_shadow_summary_evidence :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    env_fns_root_shadow_summary_evidence (alpha_normalize_global_env env) ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within (initial_root_env_for_fn f) s ->
    store_no_shadow s ->
    root_env_store_roots_named (initial_root_env_for_fn f) s ->
    root_env_store_keys_named (initial_root_env_for_fn f) s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v _ Hsummary Hin Hstore Hready Hroots
    Hstore_shadow Hnamed Hkeys Hunique Hfns_ready Heval.
  destruct (env_fns_root_shadow_summary_evidence_in_unique
              (alpha_normalize_global_env env) Hsummary Hunique
              (fn_name f) f Hin eq_refl)
    as [Hnodup Hbody_summary].
  unfold callee_body_root_shadow_ready_at in Hbody_summary.
  destruct Hbody_summary as
    (T_body & Γ_out & R_body & roots_body &
      _ & _ & Htyped_shadow & Hcompat & _ & _).
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
  destruct (eval_preserves_typing_direct_call_roots_ready
      (alpha_normalize_global_env env) s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
      (typed_env_roots_shadow_safe_roots
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
        Htyped_shadow)
      Hunique Hfns_ready
      (direct_call_callee_body_root_evidence_of_shadow_summary_bridge
        (alpha_normalize_global_env env)
        Hsummary
        (direct_call_callee_body_root_shadow_summary_bridge_of_unique
          (alpha_normalize_global_env env) Hunique)))
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Definition initial_root_runtime_ready_for_fn (f : fn_def) (s : store) : Prop :=
  store_roots_within (initial_root_env_for_fn f) s /\
  store_no_shadow s /\
  root_env_store_roots_named (initial_root_env_for_fn f) s /\
  root_env_store_keys_named (initial_root_env_for_fn f) s.

Fixpoint ident_in_b (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: ys => ident_eqb x y || ident_in_b x ys
  end.

Lemma ident_in_b_true_in :
  forall x xs,
    ident_in_b x xs = true ->
    In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; simpl; intros Hin.
  - discriminate.
  - apply orb_true_iff in Hin as [Heq | Hin].
    + apply ident_eqb_eq in Heq. subst y. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

Lemma ident_in_b_false_not_in :
  forall x xs,
    ident_in_b x xs = false ->
    ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; simpl; intros Hnot Hin.
  - contradiction.
  - apply orb_false_iff in Hnot as [Hneq Hnot].
    destruct Hin as [Heq | Hin].
    + subst y. rewrite ident_eqb_refl in Hneq. discriminate.
    + apply (IH Hnot). exact Hin.
Qed.

Fixpoint ident_names_unique_b (xs : list ident) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (ident_in_b x xs') && ident_names_unique_b xs'
  end.

Lemma ident_names_unique_b_nodup :
  forall xs,
    ident_names_unique_b xs = true ->
    NoDup xs.
Proof.
  induction xs as [| x xs IH]; simpl; intros Hunique.
  - constructor.
  - apply andb_true_iff in Hunique as [Hfresh Hrest].
    apply negb_true_iff in Hfresh.
    constructor.
    + apply ident_in_b_false_not_in. exact Hfresh.
    + apply IH. exact Hrest.
Qed.

Definition root_atom_in_b (a : root_atom) (roots : root_set) : bool :=
  existsb (root_atom_eqb a) roots.

Lemma root_atom_in_b_true_in :
  forall a roots,
    root_atom_in_b a roots = true ->
    In a roots.
Proof.
  unfold root_atom_in_b.
  intros a roots H.
  apply existsb_exists in H as [atom [Hin Heq]].
  apply root_atom_eqb_eq in Heq. subst atom.
  exact Hin.
Qed.

Fixpoint root_set_store_roots_named_b
    (roots : root_set) (s : store) : bool :=
  match roots with
  | [] => true
  | RStore z :: rest =>
      ident_in_b z (store_names s) &&
      root_set_store_roots_named_b rest s
  | RParam _ :: rest => root_set_store_roots_named_b rest s
  end.

Lemma root_set_store_roots_named_b_sound :
  forall roots s,
    root_set_store_roots_named_b roots s = true ->
    root_set_store_roots_named roots s.
Proof.
  induction roots as [| atom rest IH]; intros s Hnamed z Hin.
  - inversion Hin.
  - destruct atom as [y | y]; simpl in Hnamed, Hin.
    + apply andb_true_iff in Hnamed as [Hy Hrest].
      destruct Hin as [Hz | Hin].
      * inversion Hz; subst y. apply ident_in_b_true_in. exact Hy.
      * eapply IH; eassumption.
    + destruct Hin as [Hz | Hin].
      * discriminate.
      * eapply IH; eassumption.
Qed.

Fixpoint root_env_store_roots_named_b
    (R : root_env) (s : store) : bool :=
  match R with
  | [] => true
  | (_, roots) :: rest =>
      root_set_store_roots_named_b roots s &&
      root_env_store_roots_named_b rest s
  end.

Lemma root_env_store_roots_named_b_sound :
  forall R s,
    root_env_store_roots_named_b R s = true ->
    root_env_store_roots_named R s.
Proof.
  unfold root_env_store_roots_named.
  induction R as [| [y roots] rest IH]; intros s Hnamed x roots0 z Hlookup Hin.
  - simpl in Hlookup. discriminate.
  - simpl in Hnamed, Hlookup.
    apply andb_true_iff in Hnamed as [Hhead Htail].
    destruct (ident_eqb x y) eqn:Heq.
    + inversion Hlookup; subst roots0.
      eapply root_set_store_roots_named_b_sound; eassumption.
    + eapply IH; eassumption.
Qed.

Fixpoint root_env_store_keys_named_b (R : root_env) (s : store) : bool :=
  match R with
  | [] => true
  | (x, _) :: rest =>
      ident_in_b x (store_names s) &&
      root_env_store_keys_named_b rest s
  end.

Lemma root_env_store_keys_named_b_sound :
  forall R s,
    root_env_store_keys_named_b R s = true ->
    root_env_store_keys_named R s.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  induction R as [| [x roots] rest IH]; intros s Hkeys y Hin.
  - inversion Hin.
  - simpl in Hkeys, Hin.
    apply andb_true_iff in Hkeys as [Hx Hrest].
    destruct Hin as [Hy | Hin].
    + subst y. apply ident_in_b_true_in. exact Hx.
    + eapply IH; eassumption.
Qed.

Definition value_roots_within_leaf_b (roots : root_set) (v : value) : bool :=
  match v with
  | VUnit => true
  | VInt _ => true
  | VFloat _ => true
  | VBool _ => true
  | VStruct _ [] => true
  | VStruct _ (_ :: _) => false
  | VRef x _ => root_atom_in_b (RStore x) roots
  | VClosure _ captured =>
      match captured with
      | [] => true
      | _ :: _ => false
      end
  end.

Fixpoint value_fields_roots_within_b
    (roots : root_set) (fields : list (string * value)) : bool :=
  match fields with
  | [] => true
  | (_, v) :: rest =>
      value_roots_within_leaf_b roots v &&
      value_fields_roots_within_b roots rest
  end.

Definition value_roots_within_b (roots : root_set) (v : value) : bool :=
  match v with
  | VStruct _ fields => value_fields_roots_within_b roots fields
  | _ => value_roots_within_leaf_b roots v
  end.

Lemma value_roots_within_leaf_b_sound :
  forall roots v,
    value_roots_within_leaf_b roots v = true ->
    value_roots_within roots v.
Proof.
  intros roots v Hwithin.
  destruct v as [| i | f | b | name fields | x path | fname captured];
    simpl in Hwithin.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct fields as [| field rest]; try discriminate.
    apply VRW_Struct. constructor.
  - apply VRW_Ref.
    apply root_atom_in_b_true_in. exact Hwithin.
  - destruct captured as [| se captured]; try discriminate.
    apply VRW_ClosureEmpty.
Qed.

Lemma value_fields_roots_within_b_sound :
  forall roots fields,
    value_fields_roots_within_b roots fields = true ->
    value_fields_roots_within roots fields.
Proof.
  induction fields as [| [name v] rest IH]; simpl; intros Hwithin.
  - constructor.
  - apply andb_true_iff in Hwithin as [Hvalue Hrest].
    constructor.
    + apply value_roots_within_leaf_b_sound. exact Hvalue.
    + apply IH. exact Hrest.
Qed.

Lemma value_roots_within_b_sound :
  forall roots v,
    value_roots_within_b roots v = true ->
    value_roots_within roots v.
Proof.
  intros roots v Hwithin.
  destruct v as [| i | f | b | name fields | x path | fname captured];
    simpl in Hwithin; try (apply value_roots_within_leaf_b_sound; exact Hwithin).
  apply VRW_Struct.
  apply value_fields_roots_within_b_sound. exact Hwithin.
Qed.

Definition store_entry_roots_within_b (R : root_env) (se : store_entry)
    : bool :=
  match root_env_lookup (se_name se) R with
  | Some roots => value_roots_within_b roots (se_val se)
  | None => false
  end.

Lemma store_entry_roots_within_b_sound :
  forall R se,
    store_entry_roots_within_b R se = true ->
    store_entry_roots_within R se.
Proof.
  intros R [sx sT sv sst] Hwithin.
  unfold store_entry_roots_within_b in Hwithin. simpl in Hwithin.
  destruct (root_env_lookup sx R) as [roots |] eqn:Hlookup;
    try discriminate.
  apply SERW_Entry with (roots := roots).
  - exact Hlookup.
  - apply value_roots_within_b_sound. exact Hwithin.
Qed.

Fixpoint store_roots_within_b (R : root_env) (s : store) : bool :=
  match s with
  | [] => true
  | se :: rest =>
      store_entry_roots_within_b R se &&
      store_roots_within_b R rest
  end.

Lemma store_roots_within_b_sound :
  forall R s,
    store_roots_within_b R s = true ->
    store_roots_within R s.
Proof.
  induction s as [| se rest IH]; simpl; intros Hwithin.
  - constructor.
  - apply andb_true_iff in Hwithin as [Hentry Hrest].
    constructor.
    + apply store_entry_roots_within_b_sound. exact Hentry.
    + apply IH. exact Hrest.
Qed.

Definition store_no_shadow_b (s : store) : bool :=
  ident_names_unique_b (store_names s).

Lemma store_no_shadow_b_sound :
  forall s,
    store_no_shadow_b s = true ->
    store_no_shadow s.
Proof.
  intros s Hshadow.
  unfold store_no_shadow_b in Hshadow.
  unfold store_no_shadow.
  apply ident_names_unique_b_nodup. exact Hshadow.
Qed.

Definition check_initial_root_runtime_ready (f : fn_def) (s : store) : bool :=
  let R := initial_root_env_for_fn f in
  store_roots_within_b R s &&
  store_no_shadow_b s &&
  root_env_store_roots_named_b R s &&
  root_env_store_keys_named_b R s.

Lemma check_initial_root_runtime_ready_sound :
  forall f s,
    check_initial_root_runtime_ready f s = true ->
    initial_root_runtime_ready_for_fn f s.
Proof.
  intros f s Hready.
  unfold check_initial_root_runtime_ready in Hready.
  apply andb_true_iff in Hready as [Hready Hkeys].
  apply andb_true_iff in Hready as [Hready Hnamed].
  apply andb_true_iff in Hready as [Hroots Hshadow].
  unfold initial_root_runtime_ready_for_fn.
  repeat split.
  - apply store_roots_within_b_sound. exact Hroots.
  - apply store_no_shadow_b_sound. exact Hshadow.
  - apply root_env_store_roots_named_b_sound. exact Hnamed.
  - apply root_env_store_keys_named_b_sound. exact Hkeys.
Qed.

Lemma preservation_ready_expr_b_sound :
  forall e,
    preservation_ready_expr_b e = true ->
    preservation_ready_expr e.
Proof.
  assert (Hsize : forall n e,
    expr_size e < n ->
    preservation_ready_expr_b e = true ->
    preservation_ready_expr e).
  {
    induction n as [| n IH]; intros e Hlt Hready.
    - lia.
    - destruct e; simpl in Hready; try discriminate.
      + constructor.
      + constructor.
      + constructor.
      + constructor.
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Place_Direct. exact Hpath.
      + apply PRE_Struct.
        induction l1 as [| [name field] rest IHfields].
        * constructor.
        * simpl in Hready.
          apply andb_true_iff in Hready as [Hfield Hrest].
          constructor.
          -- apply IH with (e := field).
             ++ pose proof (expr_size_struct_field_lt s l l0
                  ((name, field) :: rest) name field (or_introl eq_refl)).
                lia.
             ++ exact Hfield.
          -- apply IHfields.
             ++ simpl. simpl in Hlt. lia.
             ++ exact Hrest.
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Replace.
        * exact Hpath.
        * apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Assign.
        * exact Hpath.
        * apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Borrow. exact Hpath.
      + apply PRE_Drop.
        apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + apply andb_true_iff in Hready as [H12 H3].
        apply andb_true_iff in H12 as [H1 H2].
        eapply PRE_If.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
        * apply IH with (e := e3); [simpl in Hlt; lia | exact H3].
  }
  intros e Hready.
  eapply Hsize with (n := S (expr_size e)); [lia | exact Hready].
Qed.

Lemma preservation_ready_args_b_sound :
  forall args,
    preservation_ready_args_b args = true ->
    preservation_ready_args args.
Proof.
  unfold preservation_ready_args_b.
  induction args as [| e rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply preservation_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Lemma preservation_ready_fields_b_sound :
  forall fields,
    preservation_ready_fields_b fields = true ->
    preservation_ready_fields fields.
Proof.
  induction fields as [| [name e] rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply preservation_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Lemma direct_call_ready_expr_b_sound :
  forall e,
    direct_call_ready_expr_b e = true ->
    exists fname args synthetic,
      direct_call_target_expr e = Some (fname, args, synthetic) /\
      preservation_ready_args args /\
      synthetic = ECall fname args.
Proof.
  intros e Hready.
  unfold direct_call_ready_expr_b in Hready.
  destruct (direct_call_target_expr e) as [[[fname args] synthetic] |]
    eqn:Htarget; try discriminate.
  exists fname, args, synthetic.
  split; [reflexivity|].
  split; [apply preservation_ready_args_b_sound; exact Hready|].
  unfold direct_call_target_expr in Htarget.
    destruct e; try discriminate.
  - inversion Htarget. reflexivity.
  - destruct e; try discriminate.
    inversion Htarget. reflexivity.
Qed.

Lemma provenance_ready_expr_b_sound :
  forall e,
    provenance_ready_expr_b e = true ->
    provenance_ready_expr e.
Proof.
  assert (Hsize : forall n e,
    expr_size e < n ->
    provenance_ready_expr_b e = true ->
    provenance_ready_expr e).
  {
    induction n as [| n IH]; intros e Hlt Hready.
    - lia.
    - destruct e; simpl in Hready; try discriminate.
      + constructor.
      + constructor.
      + constructor.
      + apply andb_true_iff in Hready as [H1 H2].
        eapply ProvReady_Let.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
      + apply andb_true_iff in Hready as [H1 H2].
        eapply ProvReady_LetInfer.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
      + constructor.
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_Place_Direct. exact Hpath.
      + apply ProvReady_Struct.
        induction l1 as [| [name field] rest IHfields].
        * constructor.
        * simpl in Hready.
          apply andb_true_iff in Hready as [Hfield Hrest].
          constructor.
          -- apply IH with (e := field).
             ++ pose proof (expr_size_struct_field_lt s l l0
                  ((name, field) :: rest) name field (or_introl eq_refl)).
                lia.
             ++ exact Hfield.
          -- apply IHfields.
             ++ simpl. simpl in Hlt. lia.
             ++ exact Hrest.
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_Replace.
        * exact Hpath.
        * apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_Assign.
        * exact Hpath.
        * apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_Borrow. exact Hpath.
      + destruct e; simpl in Hready; try discriminate.
        destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_DerefBorrow. exact Hpath.
      + apply ProvReady_Drop.
        apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + apply andb_true_iff in Hready as [H12 H3].
        apply andb_true_iff in H12 as [H1 H2].
        eapply ProvReady_If.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
        * apply IH with (e := e3); [simpl in Hlt; lia | exact H3].
  }
  intros e Hready.
  eapply Hsize with (n := S (expr_size e)); [lia | exact Hready].
Qed.

Lemma provenance_ready_args_b_sound :
  forall args,
    provenance_ready_args_b args = true ->
    provenance_ready_args args.
Proof.
  unfold provenance_ready_args_b.
  induction args as [| e rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply provenance_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Lemma provenance_ready_fields_b_sound :
  forall fields,
    provenance_ready_fields_b fields = true ->
    provenance_ready_fields fields.
Proof.
  induction fields as [| [name e] rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply provenance_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Definition env_fns_root_shadow_summary_check_ready (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_summary env fdef.

Definition env_fns_root_shadow_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.

Definition callee_body_root_shadow_direct_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_provenance_summary env fdef \/
  exists fname args raw_body synthetic_body fcallee T_body Γ_out R_body roots_body,
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_provenance_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_direct_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_direct_call_provenance_summary env fdef.

Definition callee_body_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_direct_call_provenance_summary env fdef \/
  exists fname args raw_body synthetic_body fcallee T_body Γ_out R_body roots_body,
    fn_body fdef = raw_body /\
    local_fn_value_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_provenance_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_non_capturing_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_non_capturing_call_provenance_summary env fdef.

Definition callee_body_root_shadow_captured_callee_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) /\
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fdef) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef ++ fn_captures fdef) roots_body /\
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef) R_body.

Definition callee_hidden_capture_args_disjoint
    (callee : fn_def) (args : list expr) : Prop :=
  Forall
    (fun x => ~ In x (args_local_store_names args))
    (ctx_names (params_ctx (fn_captures callee))).

Definition callee_body_root_shadow_captured_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_non_capturing_call_provenance_summary env fdef \/
  exists fname captures args fcallee captured_tys
      T_body Γ_out R_body roots_body,
    fn_body fdef = ECallExpr (EMakeClosure fname captures) args /\
    captured_call_target_expr (fn_body fdef) = Some (fname, captures, args) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    fn_lifetimes fcallee = 0 /\
    callee_hidden_capture_args_disjoint fcallee args /\
    check_make_closure_captures_exact_sctx env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee) = infer_ok captured_tys /\
    callee_body_root_shadow_captured_callee_provenance_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_captured_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_provenance_summary env fdef.

Lemma callee_hidden_capture_args_disjoint_b_sound :
  forall callee args,
    callee_hidden_capture_args_disjoint_b callee args = true ->
    callee_hidden_capture_args_disjoint callee args.
Proof.
  intros callee args Hcheck.
  unfold callee_hidden_capture_args_disjoint_b in Hcheck.
  unfold callee_hidden_capture_args_disjoint.
  apply Forall_forall.
  intros x Hin Harg.
  apply forallb_forall with (x := x) in Hcheck; [| exact Hin].
  apply negb_true_iff in Hcheck.
  assert (Hexists :
    existsb (ident_eqb x) (args_local_store_names args) = true).
  { apply existsb_exists.
    exists x. split; [exact Harg|].
    apply ident_eqb_refl. }
  rewrite Hexists in Hcheck. discriminate.
Qed.

Lemma fn_params_roots_exclude_b_sound :
  forall ps roots,
    fn_params_roots_exclude_b ps roots = true ->
    roots_exclude_params ps roots.
Proof.
  intros ps roots Hexclude.
  apply roots_exclude_params_b_sound.
  unfold roots_exclude_params_b, fn_params_roots_exclude_b in *.
  exact Hexclude.
Qed.

Lemma fn_params_root_env_excludes_b_sound :
  forall ps R,
    fn_params_root_env_excludes_b ps R = true ->
    root_env_excludes_params ps R.
Proof.
  intros ps R Hexclude.
  apply root_env_excludes_params_b_sound.
  unfold root_env_excludes_params_b, fn_params_root_env_excludes_b in *.
  exact Hexclude.
Qed.

Lemma check_fn_root_shadow_summary_sound :
  forall env fdef,
    check_fn_root_shadow_summary env fdef = true ->
    callee_body_root_shadow_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready Hsummary].
  destruct (infer_env_roots_shadow_safe env fdef
    (initial_root_env_for_fn fdef))
    as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
    try discriminate.
  apply andb_true_iff in Hsummary as [Hroots Henv].
  split.
  - eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer.
  - pose proof (infer_env_roots_shadow_safe_sound
                  env fdef (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    unfold callee_body_root_shadow_ready_at.
    exists T_body, Γ_out, R_out, roots.
    repeat split.
    + apply preservation_ready_implies_provenance_ready.
      apply preservation_ready_expr_b_sound. exact Hready.
    + apply preservation_ready_expr_b_sound. exact Hready.
    + exact Htyped.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_provenance_summary env fdef = true ->
    callee_body_root_shadow_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_provenance_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready Hsummary].
  destruct (infer_env_roots_shadow_safe env fdef
    (initial_root_env_for_fn fdef))
    as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
    try discriminate.
  apply andb_true_iff in Hsummary as [Hroots Henv].
  split.
  - eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer.
  - pose proof (infer_env_roots_shadow_safe_sound
                  env fdef (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    unfold callee_body_root_shadow_provenance_ready_at.
    exists T_body, Γ_out, R_out, roots.
    repeat split.
    + apply provenance_ready_expr_b_sound. exact Hready.
    + exact Htyped.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_direct_call_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_direct_call_provenance_summary env fdef = true ->
    callee_body_root_shadow_direct_call_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_direct_call_provenance_summary in Hcheck.
  destruct (check_fn_root_shadow_provenance_summary env fdef) eqn:Hold.
  - left. apply check_fn_root_shadow_provenance_summary_sound. exact Hold.
  - right.
    destruct (direct_call_target_expr (fn_body fdef))
      as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee Hsummary].
    destruct (infer_env_roots_shadow_safe env
      (fn_with_body fdef synthetic_body)
      (initial_root_env_for_fn fdef))
      as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
      try discriminate.
    apply andb_true_iff in Hsummary as [Hroots Henv].
    destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
      as [Hin_callee Hname_callee].
    pose proof (infer_env_roots_shadow_safe_sound
                  env (fn_with_body fdef synthetic_body)
                  (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    exists fname, args, (fn_body fdef), synthetic_body, fcallee,
      T_body, Γ_out, R_out, roots.
    split; [reflexivity|].
    split; [exact Htarget|].
    split.
    { unfold direct_call_target_expr in Htarget.
      destruct (fn_body fdef); try discriminate.
      - inversion Htarget. reflexivity.
      - destruct e; try discriminate.
        inversion Htarget. reflexivity. }
    split; [apply preservation_ready_args_b_sound; exact Hready_args|].
    split; [exact Hin_callee|].
    split; [exact Hname_callee|].
    split; [apply check_fn_root_shadow_provenance_summary_sound; exact Hcallee|].
    split.
    { change (NoDup
        (ctx_names
          (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
      eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer. }
    split; [exact Htyped|].
    split; [exact Hcompat|].
    split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
    apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_non_capturing_call_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_non_capturing_call_provenance_summary env fdef = true ->
    callee_body_root_shadow_non_capturing_call_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_non_capturing_call_provenance_summary in Hcheck.
  destruct (check_fn_root_shadow_direct_call_provenance_summary env fdef)
    eqn:Hold.
  - left. apply check_fn_root_shadow_direct_call_provenance_summary_sound.
    exact Hold.
  - right.
    destruct (local_fn_value_call_target_expr (fn_body fdef))
      as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee Hsummary].
    destruct (infer_env_roots_shadow_safe env
      (fn_with_body fdef synthetic_body)
      (initial_root_env_for_fn fdef))
      as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
      try discriminate.
    apply andb_true_iff in Hsummary as [Hroots Henv].
    destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
      as [Hin_callee Hname_callee].
    pose proof (infer_env_roots_shadow_safe_sound
                  env (fn_with_body fdef synthetic_body)
                  (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    exists fname, args, (fn_body fdef), synthetic_body, fcallee,
      T_body, Γ_out, R_out, roots.
    split; [reflexivity|].
    split; [exact Htarget|].
    split; [apply preservation_ready_args_b_sound; exact Hready_args|].
    split; [exact Hin_callee|].
    split; [exact Hname_callee|].
    split; [apply check_fn_root_shadow_provenance_summary_sound; exact Hcallee|].
    split.
    { change (NoDup
        (ctx_names
          (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
      eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer. }
    split; [exact Htyped|].
    split; [exact Hcompat|].
    split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
    apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_captured_callee_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_callee_provenance_summary env fdef = true ->
    callee_body_root_shadow_captured_callee_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_callee_provenance_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready Hsummary].
  destruct (infer_env_roots_shadow_safe env fdef
    (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef)))
    as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
    try discriminate.
  apply andb_true_iff in Hsummary as [Hroots Henv].
  split.
  - eapply infer_env_roots_shadow_safe_binding_params_nodup. exact Hinfer.
  - pose proof (infer_env_roots_shadow_safe_sound
                  env fdef
                  (initial_root_env_for_params
                    (fn_params fdef ++ fn_captures fdef))
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    exists T_body, Γ_out, R_out, roots.
    repeat split.
    + apply provenance_ready_expr_b_sound. exact Hready.
    + exact Htyped.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_captured_call_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_provenance_summary env fdef = true ->
    callee_body_root_shadow_captured_call_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_provenance_summary in Hcheck.
  destruct (check_fn_root_shadow_non_capturing_call_provenance_summary env fdef)
    eqn:Hold.
  - left. apply check_fn_root_shadow_non_capturing_call_provenance_summary_sound.
    exact Hold.
  - right.
    destruct (captured_call_target_expr (fn_body fdef))
      as [[[fname captures] args] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee_head Hrest].
    apply andb_true_iff in Hcallee_head as [Hlt Hdisjoint].
    apply PeanoNat.Nat.eqb_eq in Hlt.
    destruct (check_make_closure_captures_exact_sctx env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee)) as [captured_tys | err] eqn:Hcaptures;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee Hsummary].
    destruct (infer_env_roots_shadow_safe env fdef
      (initial_root_env_for_fn fdef))
      as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
      try discriminate.
    apply andb_true_iff in Hsummary as [Hroots Henv].
    destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
      as [Hin_callee Hname_callee].
    pose proof (infer_env_roots_shadow_safe_sound
                  env fdef
                  (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    assert (Hbody :
      fn_body fdef = ECallExpr (EMakeClosure fname captures) args).
    { unfold captured_call_target_expr in Htarget.
      destruct (fn_body fdef); try discriminate.
      destruct e; try discriminate.
      inversion Htarget. reflexivity. }
    exists fname, captures, args, fcallee, captured_tys,
      T_body, Γ_out, R_out, roots.
    split; [exact Hbody|].
    split; [reflexivity|].
    split; [apply preservation_ready_args_b_sound; exact Hready_args|].
    split; [exact Hin_callee|].
    split; [exact Hname_callee|].
    split; [exact Hlt|].
    split.
    { apply callee_hidden_capture_args_disjoint_b_sound.
      exact Hdisjoint. }
    split; [exact Hcaptures|].
    split.
    { apply check_fn_root_shadow_captured_callee_provenance_summary_sound.
      exact Hcallee. }
    split.
    { eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer. }
    split; [exact Htyped|].
    split; [exact Hcompat|].
    split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
    apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_env_root_shadow_summary_ready :
  forall env,
    check_env_root_shadow_summary env = true ->
    env_fns_root_shadow_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_provenance_summary_ready :
  forall env,
    check_env_root_shadow_provenance_summary env = true ->
    env_fns_root_shadow_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_provenance_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_direct_call_provenance_summary_ready :
  forall env,
    check_env_root_shadow_direct_call_provenance_summary env = true ->
    env_fns_root_shadow_direct_call_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_direct_call_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_direct_call_provenance_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_non_capturing_call_provenance_summary_ready :
  forall env,
    check_env_root_shadow_non_capturing_call_provenance_summary env = true ->
    env_fns_root_shadow_non_capturing_call_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_non_capturing_call_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_non_capturing_call_provenance_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_captured_call_provenance_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_provenance_summary env = true ->
    env_fns_root_shadow_captured_call_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_provenance_summary_sound.
  exact Hcheck.
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

Theorem infer_full_env_alpha_big_step_safe_with_direct_call_sidecar_ready :
  forall env f T Γ' s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    ordinary_alpha_direct_call_sidecar_ready env ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    initial_root_runtime_ready_for_fn f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f T Γ' s s' v Hinfer Hsidecar Hin Hstore Hready
    Hroot_runtime Heval.
  pose proof (ordinary_alpha_direct_call_sidecar_ready_root_shadow_evidence
                env Hsidecar) as Hsummary.
  pose proof (ordinary_alpha_direct_call_sidecar_ready_unique env Hsidecar)
    as Hunique.
  pose proof (ordinary_alpha_direct_call_sidecar_ready_preservation_ready
                env Hsidecar) as Hfns_ready.
  destruct Hroot_runtime as [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  eapply infer_full_env_alpha_big_step_safe_with_shadow_summary_evidence;
    eassumption.
Qed.

Theorem check_program_env_alpha_big_step_safe_with_direct_call_sidecar_ready :
  forall env f s s' v,
    check_program_env_alpha env = true ->
    ordinary_alpha_direct_call_sidecar_ready env ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    initial_root_runtime_ready_for_fn f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hsidecar Hin Hstore Hready
    Hroot_runtime Heval.
  unfold check_program_env_alpha, check_program_env in Hcheck.
  apply forallb_forall with (x := f) in Hcheck; [| exact Hin].
  destruct (infer_full_env (alpha_normalize_global_env env) f) as
    [[T Γ'] | err] eqn:Hinfer.
  - eapply infer_full_env_alpha_big_step_safe_with_direct_call_sidecar_ready;
      eassumption.
  - simpl in Hcheck. discriminate.
Qed.

Theorem check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_ready :
  forall env f s s' v,
    check_program_env_alpha_validated env = true ->
    ordinary_alpha_direct_call_validated_sidecar_ready env ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    initial_root_runtime_ready_for_fn f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hsidecar Hin Hstore Hready
    Hroot_runtime Heval.
  eapply check_program_env_alpha_big_step_safe_with_direct_call_sidecar_ready.
  - apply check_program_env_alpha_validated_checked.
    exact Hcheck.
  - eapply ordinary_alpha_direct_call_validated_sidecar_ready_package;
      eassumption.
  - exact Hin.
  - exact Hstore.
  - exact Hready.
  - exact Hroot_runtime.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_env_ready :
  forall env f s s' v,
    check_program_env_alpha_validated env = true ->
    ordinary_alpha_direct_call_validated_sidecar_ready env ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    initial_root_runtime_ready_for_fn f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hsidecar Hin Hstore Hroot_runtime Heval.
  destruct Hsidecar as [Hroot_shadow Hfns_ready].
  eapply check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_ready.
  - exact Hcheck.
  - split; eassumption.
  - exact Hin.
  - exact Hstore.
  - apply preservation_ready_direct_call_ready.
    apply Hfns_ready.
    exact Hin.
  - exact Hroot_runtime.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_big_step_safe_with_root_shadow_validator_ready :
  forall env f s s' v,
    check_program_env_alpha_validated env = true ->
    ordinary_alpha_direct_call_validated_root_shadow_validator_ready env ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    initial_root_runtime_ready_for_fn f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hvalidator Hin Hstore Hroot_runtime Heval.
  eapply check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_env_ready.
  - exact Hcheck.
  - apply ordinary_alpha_direct_call_validated_sidecar_ready_of_root_shadow_validator_ready.
    exact Hvalidator.
  - exact Hin.
  - exact Hstore.
  - exact Hroot_runtime.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_big_step_safe :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow env = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    initial_root_runtime_ready_for_fn f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hin Hstore Hroot_runtime Heval.
  unfold check_program_env_alpha_validated_root_shadow in Hcheck.
  apply andb_true_iff in Hcheck as [Hvalidated Hshadow].
  eapply check_program_env_alpha_validated_big_step_safe_with_root_shadow_validator_ready.
  - exact Hvalidated.
  - apply check_program_env_alpha_validated_root_shadow_ready.
    unfold check_program_env_alpha_validated_root_shadow.
    apply andb_true_iff. split; assumption.
  - exact Hin.
  - exact Hstore.
  - exact Hroot_runtime.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_big_step_safe_checked_initial :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  eapply check_program_env_alpha_validated_root_shadow_big_step_safe.
  - exact Hcheck.
  - exact Hin.
  - exact Hstore.
  - apply check_initial_root_runtime_ready_sound. exact Hinitial.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_provenance_big_step_safe_checked_initial :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_provenance env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  eapply check_program_env_alpha_validated_big_step_safe_with_root_shadow_validator_ready.
  - unfold check_program_env_alpha_validated_root_shadow_provenance in Hcheck.
    apply andb_true_iff in Hcheck as [Hvalidated _].
    exact Hvalidated.
  - apply check_program_env_alpha_validated_root_shadow_provenance_ready.
    exact Hcheck.
  - exact Hin.
  - exact Hstore.
  - apply check_initial_root_runtime_ready_sound. exact Hinitial.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_big_step_safe_with_root_shadow_provenance_validator_ready_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated env = true ->
    ordinary_alpha_root_shadow_provenance_validator_ready env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hvalidated Hvalidator Hinitial Hin Hstore Heval.
  pose proof (check_program_env_alpha_validated_unique env Hvalidated)
    as Hunique.
  pose proof
    (ordinary_alpha_root_shadow_provenance_evidence_of_validator_ready
      env Hvalidator) as Hsummary.
  pose proof
    (lookup_fn_in_unique_by_name (alpha_normalize_global_env env)
      (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  pose proof (Hsummary (fn_name f) f Hlookup) as Hfn_summary.
  destruct Hfn_summary as [Hnodup Hbody_summary].
  unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
  destruct Hbody_summary as
    (T_body & Γ_out & R_body & roots_body &
      Hprov_body & Htyped_shadow & Hcompat & _ & _).
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      (alpha_normalize_global_env env) s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hprov_body Hstore Hroots Hstore_shadow Hroot_shadow
      (typed_env_roots_shadow_safe_roots
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
        Htyped_shadow))
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_provenance_summary env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  eapply check_program_env_alpha_validated_big_step_safe_with_root_shadow_provenance_validator_ready_checked_initial_ready.
  - unfold check_program_env_alpha_validated_root_shadow_provenance_summary
      in Hcheck.
    apply andb_true_iff in Hcheck as [Hvalidated _].
    exact Hvalidated.
  - apply check_program_env_alpha_validated_root_shadow_provenance_summary_ready.
    exact Hcheck.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  unfold check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hvalidated Hsummary_check].
  pose proof (check_program_env_alpha_validated_unique env Hvalidated)
    as Hunique.
  pose proof
    (check_env_root_shadow_direct_call_provenance_summary_ready
      (alpha_normalize_global_env env) Hsummary_check)
    as Hsummary.
  pose proof (lookup_fn_in_unique_by_name (alpha_normalize_global_env env)
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  pose proof (Hsummary (fn_name f) f Hlookup) as Hfn_summary.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct Hfn_summary as [Hprov_summary | Hdirect_summary].
  - destruct Hprov_summary as [Hnodup Hbody_summary].
    unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
    destruct Hbody_summary as
      (T_body & Γ_out & R_body & roots_body &
        Hprov_body & Htyped_shadow & Hcompat & _ & _).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
        (alpha_normalize_global_env env) s (fn_body f) s' v Heval
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        T_body (sctx_of_ctx Γ_out) R_body roots_body
        Hprov_body Hstore Hroots Hstore_shadow Hroot_shadow
        (typed_env_roots_shadow_safe_roots
          (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f))
          (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
          Htyped_shadow))
      as [_ [Hv _]].
    eapply VHT_Compatible.
    + exact Hv.
    + apply ty_compatible_b_sound. exact Hcompat.
  - destruct Hdirect_summary as
      (fname & args & raw_body & synthetic_body & fcallee & T_body &
        Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
        Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
        Hnodup & Htyped_shadow & Hcompat & _ & _).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    rewrite Hbody in Heval.
    assert (Htyped_call :
      typed_env_roots_shadow_safe (alpha_normalize_global_env env)
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
        T_body (sctx_of_ctx Γ_out) R_body roots_body).
    { rewrite <- Hsynthetic. exact Htyped_shadow. }
    assert (Heval_call :
      eval (alpha_normalize_global_env env) s (ECall fname args) s' v).
    { unfold direct_call_target_expr in Htarget.
      destruct raw_body; try discriminate.
      - inversion Htarget; subst. exact Heval.
      - destruct raw_body; try discriminate.
        inversion Htarget; subst.
        apply eval_call_expr_fn_as_call. exact Heval. }
    destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
        (alpha_normalize_global_env env) s s' v fname args Heval_call
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        T_body (sctx_of_ctx Γ_out) R_body roots_body fcallee
        Hready_args Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
        (typed_env_roots_shadow_safe_roots
          (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f))
          (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body roots_body
          Htyped_call)
        Hunique Hin_callee Hname_callee Hcallee_summary)
      as [_ [Hv _]].
    eapply VHT_Compatible.
    + exact Hv.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Lemma eval_local_unrestricted_fn_value_call_as_synthetic_call :
  forall env s s' v m x T fname args,
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EFn fname) (ECallExpr (EVar x) args)) s' v ->
    eval env s
      (ELet m x T (EFn fname) (ECall fname args)) s' v.
Proof.
  intros env s s' v m x T fname args Husage Heval.
  inversion Heval; subst; clear Heval.
  match goal with
  | Hfn : eval _ _ (EFn _) _ _ |- _ =>
      inversion Hfn; subst
  end.
  match goal with
  | Hcall : eval _ _ (ECallExpr (EVar _) _) _ _ |- _ =>
      inversion Hcall; subst; clear Hcall
  end.
  match goal with
  | Hcallee : eval _ _ (EVar _) _ _ |- _ =>
      inversion Hcallee; subst; clear Hcallee
  end.
  - match goal with
    | Hlookup : store_lookup _ (store_add _ _ _ _) = Some _ |- _ =>
        simpl in Hlookup; rewrite ident_eqb_refl in Hlookup;
        inversion Hlookup; subst; clear Hlookup
    end.
    repeat match goal with
    | Hclosure : VClosure _ _ = VClosure _ _ |- _ =>
        inversion Hclosure; subst; clear Hclosure
    | Hclosure : VClosure _ _ = _ |- _ =>
        inversion Hclosure; subst; clear Hclosure
    | Hclosure : _ = VClosure _ _ |- _ =>
        inversion Hclosure; subst; clear Hclosure
    end.
    simpl in *.
    eapply Eval_Let.
    + match goal with
      | Hfn : eval _ _ (EFn _) _ _ |- _ => exact Hfn
      end.
    + match goal with
      | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?fdef_fn,
        Hcaps_fn : fn_captures ?fdef_fn = [],
        Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?fdef,
        Hargs : eval_args env _ args _ _,
        Hrename : alpha_rename_fn_def ?used_names ?fdef = (?fcall, ?used'),
        Hbody : eval env (bind_params _ _ _) _ _ _ |- _ =>
          assert (Hsame : fdef_fn = fdef)
            by (eapply lookup_fn_deterministic; eassumption);
          subst fdef;
          assert (Hcaps_call : fn_captures fcall = [])
            by (rewrite (alpha_rename_fn_def_captures
                  used_names fdef_fn fcall used' Hrename);
                exact Hcaps_fn);
          rewrite Hcaps_call;
          simpl;
          eapply Eval_Call;
          [ exact Hlookup | exact Hcaps_fn | exact Hargs | exact Hrename | exact Hbody ]
      end.
  - match goal with
    | Hlookup : store_lookup _ (store_add _ _ _ _) = Some _ |- _ =>
        simpl in Hlookup; rewrite ident_eqb_refl in Hlookup;
        inversion Hlookup; subst; clear Hlookup
    end.
    match goal with
    | Hconsume : needs_consume _ = true |- _ =>
        simpl in Hconsume; unfold needs_consume in Hconsume;
        simpl in Hconsume; rewrite Husage in Hconsume;
        discriminate
    end.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  unfold check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hvalidated Hsummary_check].
  pose proof (check_program_env_alpha_validated_unique env Hvalidated)
    as Hunique.
  pose proof
    (check_env_root_shadow_non_capturing_call_provenance_summary_ready
      (alpha_normalize_global_env env) Hsummary_check)
    as Hsummary.
  pose proof (lookup_fn_in_unique_by_name (alpha_normalize_global_env env)
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  pose proof (Hsummary (fn_name f) f Hlookup) as Hfn_summary.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct Hfn_summary as [Hdirect_or_prov | Hlocal_summary].
  - destruct Hdirect_or_prov as [Hprov_summary | Hdirect_summary].
    + destruct Hprov_summary as [Hnodup Hbody_summary].
      unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
      destruct Hbody_summary as
        (T_body & Γ_out & R_body & roots_body &
          Hprov_body & Htyped_shadow & Hcompat & _ & _).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
      destruct (proj1 eval_preserves_typing_roots_ready_mutual
          (alpha_normalize_global_env env) s (fn_body f) s' v Heval
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f))
          T_body (sctx_of_ctx Γ_out) R_body roots_body
          Hprov_body Hstore Hroots Hstore_shadow Hroot_shadow
          (typed_env_roots_shadow_safe_roots
            (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
            (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f))
            (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
            Htyped_shadow))
        as [_ [Hv _]].
      eapply VHT_Compatible.
      * exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hdirect_summary as
        (fname & args & raw_body & synthetic_body & fcallee & T_body &
          Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
          Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
          Hnodup & Htyped_shadow & Hcompat & _ & _).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
      rewrite Hbody in Heval.
      assert (Htyped_call :
        typed_env_roots_shadow_safe (alpha_normalize_global_env env)
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
          T_body (sctx_of_ctx Γ_out) R_body roots_body).
      { rewrite <- Hsynthetic. exact Htyped_shadow. }
      assert (Heval_call :
        eval (alpha_normalize_global_env env) s (ECall fname args) s' v).
      { unfold direct_call_target_expr in Htarget.
        destruct raw_body; try discriminate.
        - inversion Htarget; subst. exact Heval.
        - destruct raw_body; try discriminate.
          inversion Htarget; subst.
          apply eval_call_expr_fn_as_call. exact Heval. }
      destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
          (alpha_normalize_global_env env) s s' v fname args Heval_call
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f))
          T_body (sctx_of_ctx Γ_out) R_body roots_body fcallee
          Hready_args Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
          (typed_env_roots_shadow_safe_roots
            (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
            (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f))
            (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body roots_body
            Htyped_call)
          Hunique Hin_callee Hname_callee Hcallee_summary)
        as [_ [Hv _]].
      eapply VHT_Compatible.
      * exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat.
  - destruct Hlocal_summary as
      (fname & args & raw_body & synthetic_body & fcallee & T_body &
        Γ_out & R_body & roots_body & Hbody & Htarget & Hready_args &
        Hin_callee & Hname_callee & Hcallee_summary & Hnodup &
        Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    rewrite Hbody in Heval.
    unfold local_fn_value_call_target_expr in Htarget.
	    destruct raw_body as
	      [| lit | z | m x T e1 e2 | m x e1 e2 | fname_alias
	       | fname_make captures_make | p | fname_direct args_direct | callee args_call
	       | sname lts tys fields
	       | p e_new | p e_new | rk p | e | e | e1 e2 e3];
      try discriminate.
	    + destruct e1 as
	        [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12 | fname_value
	         | fname_make1 captures_make1 | p1 | fname1 args1 | callee1 args1
	         | sname1 lts1 tys1 fields1
	         | p1 e_new1 | p1 e_new1 | rk1 p1 | e1 | e1 | e11 e12 e13];
        try discriminate.
	      destruct e2 as
	        [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22 | fname2
	         | fname_make2 captures_make2 | p2 | fname2 args2 | callee2 args2
	         | sname2 lts2 tys2 fields2
	         | p2 e_new2 | p2 e_new2 | rk2 p2 | e2 | e2 | e21 e22 e23];
        try discriminate.
	      destruct callee2 as
	        [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2 | fnamec
	         | fname_makec captures_makec | pc | fnamec argsc | calleec argsc
	         | snamec ltsc tysc fieldsc
	         | pc e_newc | pc e_newc | rkc pc | ec | ec | ec1 ec2 ec3];
        try discriminate.
      destruct (ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted)
        eqn:Halias; try discriminate.
      inversion Htarget; subst; clear Htarget.
      apply andb_true_iff in Halias as [Hname_eq Husage_eq].
      apply ident_eqb_eq in Hname_eq. subst y.
      apply usage_eqb_true in Husage_eq.
      match goal with
      | He : eval ?env0 ?s0
          (ELet ?m0 ?x0 ?T0 (EFn ?fname0)
            (ECallExpr (EVar ?x0) ?args0)) ?sfinal ?vfinal |- _ =>
          assert (Heval_synthetic :
            eval env0 s0
              (ELet m0 x0 T0 (EFn fname0) (ECall fname0 args0))
              sfinal vfinal)
          by (eapply eval_local_unrestricted_fn_value_call_as_synthetic_call;
              [ exact Husage_eq | exact He ])
      end.
      inversion Heval_synthetic; subst; clear Heval_synthetic.
      match goal with
      | Hfn : eval _ _ (EFn _) _ _ |- _ =>
          inversion Hfn; subst; clear Hfn
      end.
      dependent destruction Htyped_shadow.
      match goal with
      | Hfn_typed : typed_env_roots_shadow_safe _ _ _ _ _ (EFn _) _ _ _ _ |- _ =>
          dependent destruction Hfn_typed
      end.
      match goal with
      | Htyped_call_shadow :
          typed_env_roots_shadow_safe _ _ _ (root_env_add _ _ _)
            (sctx_add _ _ _ _) (ECall _ _) _ _ _ _ |- _ =>
          pose proof (typed_env_roots_shadow_safe_roots
            (alpha_normalize_global_env env) (fn_outlives f)
            (fn_lifetimes f) _ _ _ _ _ _ _ Htyped_call_shadow)
            as Htyped_call
      end.
      assert (Hfresh_store : store_lookup x0 s1 = None)
        by (eapply store_roots_within_lookup_none; eassumption).
      assert (Hadd_pres :
        store_ref_targets_preserved (alpha_normalize_global_env env) s1
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
        by (apply store_add_fresh_ref_targets_preserved;
            exact Hfresh_store).
      assert (Hv_closure_actual :
        value_has_type (alpha_normalize_global_env env) s1
          (VClosure (fn_name fcallee) []) (fn_value_ty fdef))
        by (eapply VHT_ClosureIn; [exact H | exact x]).
      assert (Hv_closure :
        value_has_type (alpha_normalize_global_env env) s1
          (VClosure (fn_name fcallee) []) T)
      by (eapply VHT_Compatible;
          [ exact Hv_closure_actual
          | apply ty_compatible_b_sound; exact H0 ]).
      assert (Hstore_add :
        store_typed (alpha_normalize_global_env env)
          (store_add x0 T (VClosure (fn_name fcallee) []) s1)
          (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f))))
      by (eapply store_typed_add;
          [ exact Hstore | exact Hv_closure | exact Hadd_pres ]).
      assert (Hroots_add :
        store_roots_within (root_env_add x0 [] (initial_root_env_for_fn f))
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (eapply store_add_roots_within;
          [ exact Hroots | eassumption | constructor ]).
      assert (Hshadow_add :
        store_no_shadow
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (apply store_no_shadow_add; assumption).
      assert (Hrn_add :
        root_env_no_shadow (root_env_add x0 [] (initial_root_env_for_fn f)))
      by (apply root_env_no_shadow_add; assumption).
      assert (Hempty_named : root_set_store_roots_named [] s1)
        by (intros z Hin_empty; contradiction).
      assert (Hnamed_add :
        root_env_store_roots_named
          (root_env_add x0 [] (initial_root_env_for_fn f))
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (eapply root_env_store_roots_named_add_env_store_add;
          eassumption).
      assert (Hkeys_add :
        root_env_store_keys_named
          (root_env_add x0 [] (initial_root_env_for_fn f))
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (eapply root_env_store_keys_named_add_env_store_add;
          exact Hkeys).
      match goal with
      | Heval_call : eval _ _ (ECall (fn_name fcallee) args) s2 v |- _ =>
          destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
              (alpha_normalize_global_env env)
              (store_add x0 T (VClosure (fn_name fcallee) []) s1) s2 v
              (fn_name fcallee) args Heval_call
              (fn_outlives f) (fn_lifetimes f)
              (root_env_add x0 [] (initial_root_env_for_fn f))
              (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f)))
              T2 Σ2 R2 roots2 fcallee
              Hready_args Hstore_add Hroots_add Hshadow_add Hrn_add
              Hnamed_add Hkeys_add Htyped_call Hunique Hin_callee
              eq_refl Hcallee_summary)
            as [_ [Hv_inner [_ [_ [Hv_roots _]]]]]
      end.
      assert (Hexclude_v : value_refs_exclude_root x0 v)
        by (eapply value_roots_exclude_root; eassumption).
      assert (Hv_removed :
        value_has_type (alpha_normalize_global_env env) (store_remove x0 s2)
          v T2)
        by (eapply value_has_type_store_remove_excluding_root; eassumption).
      eapply VHT_Compatible.
      * exact Hv_removed.
      * apply ty_compatible_b_sound. exact Hcompat.
    + inversion Heval.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  unfold check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hvalidated Hsummary_check].
  pose proof (check_program_env_alpha_validated_unique env Hvalidated)
    as Hunique.
  pose proof
    (check_env_root_shadow_captured_call_provenance_summary_ready
      (alpha_normalize_global_env env) Hsummary_check)
    as Hsummary.
  pose proof (lookup_fn_in_unique_by_name (alpha_normalize_global_env env)
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  pose proof (Hsummary (fn_name f) f Hlookup) as Hfn_summary.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct Hfn_summary as [Hnoncapturing | Hcaptured_summary].
  - destruct Hnoncapturing as [Hdirect_or_prov | Hlocal_summary].
    + destruct Hdirect_or_prov as [Hprov_summary | Hdirect_summary].
      * destruct Hprov_summary as [Hnodup Hbody_summary].
        unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
        destruct Hbody_summary as
          (T_body & Γ_out & R_body & roots_body &
            Hprov_body & Htyped_shadow & Hcompat & _ & _).
        pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
          as Hroot_shadow.
        destruct (proj1 eval_preserves_typing_roots_ready_mutual
            (alpha_normalize_global_env env) s (fn_body f) s' v Heval
            (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f))
            T_body (sctx_of_ctx Γ_out) R_body roots_body
            Hprov_body Hstore Hroots Hstore_shadow Hroot_shadow
            (typed_env_roots_shadow_safe_roots
              (alpha_normalize_global_env env) (fn_outlives f)
              (fn_lifetimes f) (initial_root_env_for_fn f)
              (sctx_of_ctx (fn_body_ctx f))
              (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_shadow))
          as [_ [Hv _]].
        eapply VHT_Compatible.
        -- exact Hv.
        -- apply ty_compatible_b_sound. exact Hcompat.
      * destruct Hdirect_summary as
          (fname & args & raw_body & synthetic_body & fcallee & T_body &
            Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
            Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
            Hnodup & Htyped_shadow & Hcompat & _ & _).
        pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
          as Hroot_shadow.
        rewrite Hbody in Heval.
        assert (Htyped_call :
          typed_env_roots_shadow_safe (alpha_normalize_global_env env)
            (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
            T_body (sctx_of_ctx Γ_out) R_body roots_body).
        { rewrite <- Hsynthetic. exact Htyped_shadow. }
        assert (Heval_call :
          eval (alpha_normalize_global_env env) s (ECall fname args) s' v).
        { unfold direct_call_target_expr in Htarget.
          destruct raw_body; try discriminate.
          - inversion Htarget; subst. exact Heval.
          - destruct raw_body; try discriminate.
            inversion Htarget; subst.
            apply eval_call_expr_fn_as_call. exact Heval. }
        destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
            (alpha_normalize_global_env env) s s' v fname args Heval_call
            (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f))
            T_body (sctx_of_ctx Γ_out) R_body roots_body fcallee
            Hready_args Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
            (typed_env_roots_shadow_safe_roots
              (alpha_normalize_global_env env) (fn_outlives f)
              (fn_lifetimes f) (initial_root_env_for_fn f)
              (sctx_of_ctx (fn_body_ctx f))
              (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body
              roots_body Htyped_call)
            Hunique Hin_callee Hname_callee Hcallee_summary)
          as [_ [Hv _]].
        eapply VHT_Compatible.
        -- exact Hv.
        -- apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hlocal_summary as
        (fname & args & raw_body & synthetic_body & fcallee & T_body &
          Γ_out & R_body & roots_body & Hbody & Htarget & Hready_args &
          Hin_callee & Hname_callee & Hcallee_summary & Hnodup &
          Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
        as Hroot_shadow.
      rewrite Hbody in Heval.
      unfold local_fn_value_call_target_expr in Htarget.
      destruct raw_body as
        [| lit | z | m x T e1 e2 | m x e1 e2 | fname_alias
         | fname_make captures_make | p | fname_direct args_direct
         | callee args_call | sname lts tys fields
         | p e_new | p e_new | rk p | e | e | e1 e2 e3];
        try discriminate.
      * destruct e1 as
          [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
           | fname_value | fname_make1 captures_make1 | p1
           | fname1 args1 | callee1 args1 | sname1 lts1 tys1 fields1
           | p1 e_new1 | p1 e_new1 | rkc1 p1 | e1 | e1 | e11 e12 e13];
          try discriminate.
        destruct e2 as
          [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
           | fname2 | fname_make2 captures_make2 | p2
           | fname2 args2 | callee2 args2 | sname2 lts2 tys2 fields2
           | p2 e_new2 | p2 e_new2 | rkc2 p2 | e2 | e2 | e21 e22 e23];
          try discriminate.
        destruct callee2 as
          [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
           | fnamec | fname_makec captures_makec | pc
           | fnamec argsc | calleec argsc | snamec ltsc tysc fieldsc
           | pc e_newc | pc e_newc | rkc pc | ec | ec | ec1 ec2 ec3];
          try discriminate.
        destruct (ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted)
          eqn:Halias; try discriminate.
        inversion Htarget; subst; clear Htarget.
        apply andb_true_iff in Halias as [Hname_eq Husage_eq].
        apply ident_eqb_eq in Hname_eq. subst y.
        apply usage_eqb_true in Husage_eq.
        match goal with
        | He : eval ?env0 ?s0
            (ELet ?m0 ?x0 ?T0 (EFn ?fname0)
              (ECallExpr (EVar ?x0) ?args0)) ?sfinal ?vfinal |- _ =>
            assert (Heval_synthetic :
              eval env0 s0
                (ELet m0 x0 T0 (EFn fname0) (ECall fname0 args0))
                sfinal vfinal)
            by (eapply eval_local_unrestricted_fn_value_call_as_synthetic_call;
                [ exact Husage_eq | exact He ])
        end.
        inversion Heval_synthetic; subst; clear Heval_synthetic.
        match goal with
        | Hfn : eval _ _ (EFn _) _ _ |- _ =>
            inversion Hfn; subst; clear Hfn
        end.
        dependent destruction Htyped_shadow.
        match goal with
        | Hfn_typed : typed_env_roots_shadow_safe _ _ _ _ _ (EFn _) _ _ _ _ |- _ =>
            dependent destruction Hfn_typed
        end.
        match goal with
        | Htyped_call_shadow :
            typed_env_roots_shadow_safe _ _ _ (root_env_add _ _ _)
              (sctx_add _ _ _ _) (ECall _ _) _ _ _ _ |- _ =>
            pose proof (typed_env_roots_shadow_safe_roots
              (alpha_normalize_global_env env) (fn_outlives f)
              (fn_lifetimes f) _ _ _ _ _ _ _ Htyped_call_shadow)
              as Htyped_call
        end.
        assert (Hfresh_store : store_lookup x0 s1 = None)
          by (eapply store_roots_within_lookup_none; eassumption).
        assert (Hadd_pres :
          store_ref_targets_preserved (alpha_normalize_global_env env) s1
            (store_add x0 T (VClosure (fn_name fcallee) []) s1))
          by (apply store_add_fresh_ref_targets_preserved;
              exact Hfresh_store).
        assert (Hv_closure_actual :
          value_has_type (alpha_normalize_global_env env) s1
            (VClosure (fn_name fcallee) []) (fn_value_ty fdef))
          by (eapply VHT_ClosureIn; [exact H | exact x]).
        assert (Hv_closure :
          value_has_type (alpha_normalize_global_env env) s1
            (VClosure (fn_name fcallee) []) T)
        by (eapply VHT_Compatible;
            [ exact Hv_closure_actual
            | apply ty_compatible_b_sound; exact H0 ]).
        assert (Hstore_add :
          store_typed (alpha_normalize_global_env env)
            (store_add x0 T (VClosure (fn_name fcallee) []) s1)
            (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f))))
        by (eapply store_typed_add;
            [ exact Hstore | exact Hv_closure | exact Hadd_pres ]).
        assert (Hroots_add :
          store_roots_within (root_env_add x0 [] (initial_root_env_for_fn f))
            (store_add x0 T (VClosure (fn_name fcallee) []) s1))
        by (eapply store_add_roots_within;
            [ exact Hroots | eassumption | constructor ]).
        assert (Hshadow_add :
          store_no_shadow
            (store_add x0 T (VClosure (fn_name fcallee) []) s1))
        by (apply store_no_shadow_add; assumption).
        assert (Hrn_add :
          root_env_no_shadow (root_env_add x0 [] (initial_root_env_for_fn f)))
        by (apply root_env_no_shadow_add; assumption).
        assert (Hempty_named : root_set_store_roots_named [] s1)
          by (intros z Hin_empty; contradiction).
        assert (Hnamed_add :
          root_env_store_roots_named
            (root_env_add x0 [] (initial_root_env_for_fn f))
            (store_add x0 T (VClosure (fn_name fcallee) []) s1))
        by (eapply root_env_store_roots_named_add_env_store_add;
            eassumption).
        assert (Hkeys_add :
          root_env_store_keys_named
            (root_env_add x0 [] (initial_root_env_for_fn f))
            (store_add x0 T (VClosure (fn_name fcallee) []) s1))
        by (eapply root_env_store_keys_named_add_env_store_add;
            exact Hkeys).
        match goal with
        | Heval_call : eval _ _ (ECall (fn_name fcallee) args) s2 v |- _ =>
            destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
                (alpha_normalize_global_env env)
                (store_add x0 T (VClosure (fn_name fcallee) []) s1) s2 v
                (fn_name fcallee) args Heval_call
                (fn_outlives f) (fn_lifetimes f)
                (root_env_add x0 [] (initial_root_env_for_fn f))
                (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f)))
                T2 Σ2 R2 roots2 fcallee
                Hready_args Hstore_add Hroots_add Hshadow_add Hrn_add
                Hnamed_add Hkeys_add Htyped_call Hunique Hin_callee
                eq_refl Hcallee_summary)
              as [_ [Hv_inner [_ [_ [Hv_roots _]]]]]
        end.
        assert (Hexclude_v : value_refs_exclude_root x0 v)
          by (eapply value_roots_exclude_root; eassumption).
        assert (Hv_removed :
          value_has_type (alpha_normalize_global_env env) (store_remove x0 s2)
            v T2)
          by (eapply value_has_type_store_remove_excluding_root; eassumption).
        eapply VHT_Compatible.
        -- exact Hv_removed.
        -- apply ty_compatible_b_sound. exact Hcompat.
      * inversion Heval.
  - destruct Hcaptured_summary as
      (fname & captures & args & fcallee & captured_tys &
        T_body & Γ_out & R_body & roots_body &
        Hbody & Htarget & Hready_args & Hin_callee & Hname_callee &
        Hcallee_lts & Hdisjoint & Hcaptures & Hcallee_summary &
        Hnodup & Htyped_shadow & Hcompat & _ & _).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    rewrite Hbody in Heval.
    rewrite Hbody in Htyped_shadow.
    dependent destruction Heval.
    pose proof Heval1 as Heval_make.
    dependent destruction Heval1.
    dependent destruction Htyped_shadow.
    repeat match goal with
    | Hlookup : lookup_fn ?fname_call
        (env_fns (alpha_normalize_global_env env)) =
        Some ?f_runtime |- _ =>
        lazymatch f_runtime with
        | fcallee => fail
        | _ =>
            let Hsame := fresh "Hsame_callee" in
            assert (Hsame : f_runtime = fcallee)
              by (eapply lookup_fn_unique_by_name;
                  [ exact Hlookup | exact Hin_callee | exact Hname_callee
                  | exact Hunique ]);
            subst f_runtime
        end
    | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
      Hname_typed : fn_name ?f_typed = ?fname_call |- _ =>
        lazymatch f_typed with
        | fcallee => fail
        | _ =>
            let Hsame := fresh "Hsame_typed_callee" in
            assert (Hsame : f_typed = fcallee)
              by (eapply Hunique;
                  [ exact Hin_typed | exact Hin_callee
                  | rewrite Hname_typed; exact Hname_callee ]);
            subst f_typed
        end
    end.
    match goal with
    | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
      Hname_eq : fn_name fcallee = fn_name ?f_typed |- _ =>
        lazymatch f_typed with
        | fcallee => fail
        | _ =>
            let Hsame := fresh "Hsame_typed_callee" in
            assert (Hsame : f_typed = fcallee)
              by (eapply Hunique;
                  [ exact Hin_typed | exact Hin_callee
                  | symmetry; exact Hname_eq ]);
            subst f_typed
        end
    end.
    destruct Hcallee_summary as
      [Hnodup_binding
       (T_callee & Γ_callee & R_callee & roots_callee &
        Hprov_callee & Htyped_callee & Hcompat_callee &
        Hexclude_roots_callee & Hexclude_env_callee)].
    assert (Hnodup_caps :
      NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
    { rewrite params_ctx_app, ctx_names_app in Hnodup_binding.
      eapply NoDup_app_right_ts. exact Hnodup_binding. }
    match goal with
    | Hlookup : lookup_fn ?fname_call
        (env_fns (alpha_normalize_global_env env)) =
        Some fcallee,
      Hcopy : copy_capture_store_as captures (fn_captures fcallee) s =
        Some captured,
      Htyped_args_shadow : typed_args_roots_shadow_safe
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        args (fn_params fcallee) ?Sigma_args ?R_args ?arg_roots,
      Heval_args : eval_args (alpha_normalize_global_env env) s args s_args vs,
      Hrename : alpha_rename_fn_def (store_names (captured ++ s_args))
        fcallee = (fcall, used'),
      Heval_body : eval (alpha_normalize_global_env env)
        (bind_params (fn_params fcall) vs (captured ++ s_args))
        (fn_body fcall) s_body ?ret |- _ =>
      pose proof (typed_args_roots_shadow_safe_roots
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        args (fn_params fcallee) Sigma_args R_args arg_roots
        Htyped_args_shadow)
        as Htyped_args_roots;
      destruct (eval_make_closure_captured_call_expr_preserves_typing_with_callee_components
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        args fname_call captures captured fcallee fcall used' s s_args s_body vs ret
        R_args Sigma_args arg_roots captured_tys T_callee Γ_callee
        R_callee roots_callee
        Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
        (Eval_MakeClosure (alpha_normalize_global_env env) s fname_call captures
          captured fcallee Hlookup Hcopy)
        Hlookup Heval_args Hrename Heval_body Hcaptures Hnodup_caps Hready_args
        Htyped_args_roots Hnodup_binding Hprov_callee Htyped_callee Hcompat_callee
        Hexclude_roots_callee Hexclude_env_callee)
      as [_ [_ Hv]]
    end.
    eapply VHT_Compatible.
    + rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_sidecar :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_check_evidence (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hstore Hready
    Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready
    Hcallee_roots Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_ready;
    eassumption.
Qed.
