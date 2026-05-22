From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeShadowSummaryFacts.
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

Lemma existsb_ident_eqb_false_notin :
  forall x xs,
    existsb (ident_eqb x) xs = false ->
    ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; intros Hexists Hin.
  - contradiction.
  - simpl in Hexists.
    apply orb_false_iff in Hexists as [Hy Hys].
    destruct Hin as [Hin | Hin].
    + subst y. rewrite ident_eqb_refl in Hy. discriminate.
    + eapply IH; eassumption.
Qed.

Lemma store_lookup_none_not_in_store_names :
  forall x s,
    store_lookup x s = None ->
    ~ In x (store_names s).
Proof.
  intros x s Hlookup Hin.
  induction s as [| se rest IH]; simpl in Hin; try contradiction.
  simpl in Hlookup.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - discriminate.
  - destruct Hin as [Hin | Hin].
    + subst x. rewrite ident_eqb_refl in Heq. discriminate.
    + apply IH; assumption.
Qed.

Lemma args_free_vars_checker_eq :
  forall args,
    args_free_vars_checker args = args_free_vars_ts args.
Proof.
  induction args as [| e rest IH]; unfold args_free_vars_checker in *;
    simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma local_captured_call_target_expr_sound :
  forall e fname captures args m x T direct_body let_body,
    local_captured_call_target_expr e =
      Some (fname, captures, args, m, x, T, direct_body, let_body) ->
    e =
      ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args) /\
    direct_body = ECallExpr (EMakeClosure fname captures) args /\
    let_body = ELet m x T (EMakeClosure fname captures) direct_body /\
    ty_usage T = UUnrestricted /\
    ~ In x captures /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args).
Proof.
  intros e fname captures args m x T direct_body let_body Htarget.
  unfold local_captured_call_target_expr in Htarget.
  destruct e as
    [| lit | z | m0 x0 T0 e1 e2 | m0 x0 e1 e2 | fname_value
     | fname_make captures_make | p | fname_direct args_direct
     | callee args_call | sname lts tys fields
     | p e_new | p e_new | rk p | e | e | e1 e2 e3];
    try discriminate.
  destruct e1 as
    [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
     | fname_value1 | fname_make captures_make | p1
     | fname1 args1 | callee1 args1 | sname1 lts1 tys1 fields1
     | p1 e_new1 | p1 e_new1 | rk1 p1 | e1 | e1 | e11 e12 e13];
    try discriminate.
  destruct e2 as
    [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
     | fname_value2 | fname_make2 captures_make2 | p2
     | fname2 args2 | callee2 args2 | sname2 lts2 tys2 fields2
     | p2 e_new2 | p2 e_new2 | rk2 p2 | e2 | e2 | e21 e22 e23];
    try discriminate.
  destruct callee2 as
    [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
     | fnamec | fname_makec captures_makec | pc
     | fnamec argsc | calleec argsc | snamec ltsc tysc fieldsc
     | pc e_newc | pc e_newc | rkc pc | ec | ec | ec1 ec2 ec3];
    try discriminate.
  destruct
    (ident_eqb x0 y &&
     usage_eqb (ty_usage T0) UUnrestricted &&
     negb (existsb (ident_eqb x0) captures_make) &&
     negb (existsb (ident_eqb x0) (args_free_vars_checker args2)) &&
     negb (existsb (ident_eqb x0) (args_local_store_names args2)))
    eqn:Hguards; try discriminate.
  inversion Htarget; subst; clear Htarget.
  apply andb_true_iff in Hguards as [Hguards Hlocal].
  apply andb_true_iff in Hguards as [Hguards Hfree].
  apply andb_true_iff in Hguards as [Hguards Hcaps].
  apply andb_true_iff in Hguards as [Hid Husage].
  apply ident_eqb_eq in Hid. subst y.
  apply usage_eqb_true in Husage.
  apply negb_true_iff in Hcaps.
  apply negb_true_iff in Hfree.
  apply negb_true_iff in Hlocal.
  repeat split; try reflexivity; try exact Husage.
  - eapply existsb_ident_eqb_false_notin. exact Hcaps.
  - rewrite <- args_free_vars_checker_eq.
    eapply existsb_ident_eqb_false_notin. exact Hfree.
  - eapply existsb_ident_eqb_false_notin. exact Hlocal.
Qed.

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

Lemma direct_call_target_expr_ok_is_call_early :
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

Lemma captured_call_target_expr_ok_is_make_closure_call_early :
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

Lemma check_expr_root_shadow_captured_call_provenance_summary_fuel_sound_early :
  forall fuel env Ω n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_captured_call_provenance_summary_fuel
      fuel env Ω n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Ω n R Σ e T Σ' R' roots
    Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_captured_call_provenance_summary_fuel]
      in Hcheck.
    rewrite Hinfer in Hcheck.
    apply orb_true_iff in Hcheck as [Hnon_if | Hif].
    + apply orb_true_iff in Hnon_if as [Hprov_or_direct | Hcaptured].
      * apply orb_true_iff in Hprov_or_direct as [Hprov | Hdirect].
        -- eexists. eapply ERSCE_Provenance.
           ++ apply provenance_ready_expr_b_sound. exact Hprov.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
        -- destruct (direct_call_target_expr e)
             as [[[fname args] synthetic_body] |] eqn:Htarget;
             try discriminate.
           apply andb_true_iff in Hdirect as [Hready_args Hdirect].
           destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
             eqn:Hlookup_b; try discriminate.
           apply andb_true_iff in Hdirect as [Hcallee Hsynthetic_ok].
           destruct (infer_core_env_state_fuel_roots_shadow_safe
             (S fuel') env Ω n R Σ synthetic_body)
             as [[[[T_syn Σ_syn] R_syn] roots_syn] | err]
             eqn:Hsynthetic; try discriminate.
           destruct (direct_call_target_expr_ok_is_call_early
             (S fuel') env Ω n R Σ e T Σ' R' roots fname args
             synthetic_body Hinfer Htarget)
             as [He Hsynthetic_body].
           subst e synthetic_body.
           rewrite Hinfer in Hsynthetic. inversion Hsynthetic; subst.
           destruct (lookup_fn_b_sound fname (env_fns env) fcallee
             Hlookup_b) as [Hin_callee Hname_callee].
           eexists. eapply ERSCE_DirectCall.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply preservation_ready_args_b_sound. exact Hready_args.
           ++ exact Hin_callee.
           ++ exact Hname_callee.
           ++ apply check_fn_root_shadow_provenance_summary_sound.
              exact Hcallee.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
      * destruct (captured_call_target_expr e)
          as [[[fname captures] args] |] eqn:Htarget; try discriminate.
        apply andb_true_iff in Hcaptured as [Hready_args Hcaptured].
        destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
          eqn:Hlookup_b; try discriminate.
        apply andb_true_iff in Hcaptured as [Hcaptured_head Hcallee].
        apply andb_true_iff in Hcaptured_head as [Hlt Hdisjoint].
        apply PeanoNat.Nat.eqb_eq in Hlt.
        destruct (check_make_closure_captures_exact_sctx_with_env env Ω Σ
          captures (fn_captures fcallee)) as [[env_lt captured_tys] | err]
          eqn:Hcaptures; try discriminate.
        destruct (capture_root_bound R captures (fn_captures fcallee))
          as [capture_roots |] eqn:Hcapture_bound; try discriminate.
        pose proof (captured_call_target_expr_ok_is_make_closure_call_early
          (S fuel') env Ω n R Σ e T Σ' R' roots fname captures args
          Hinfer Htarget) as He.
        subst e.
        destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
          as [Hin_callee Hname_callee].
        pose proof
          (check_fn_root_shadow_captured_callee_provenance_summary_sound
            env fcallee Hcallee) as Hcallee_summary.
        destruct Hcallee_summary as
          [Hnodup_binding
           (T_body & Γ_out & R_body & roots_body & Hprov_body &
            Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env)].
        eexists. eapply ERSCE_CapturedCall.
        -- apply preservation_ready_args_b_sound. exact Hready_args.
        -- exact Hin_callee.
        -- exact Hname_callee.
        -- exact Hlt.
        -- apply callee_hidden_capture_args_disjoint_b_sound.
           exact Hdisjoint.
        -- exact Hcaptures.
        -- exact Hnodup_binding.
        -- exact Hprov_body.
        -- exact Htyped_body.
        -- exact Hcompat_body.
        -- exact Hexclude_roots.
        -- exact Hexclude_env.
        -- exact Hcapture_bound.
        -- eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
           exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hif.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err] eqn:Hcond;
        try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans)
        eqn:Hcond_core; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
        Σ1 e2) as [[[[T2 Σ2] R2] roots2] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
        Σ1 e3) as [[[[T3 Σ3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2 R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3)) as [Γ4 |]
        eqn:Hmerge; try discriminate.
      apply andb_true_iff in Hif as [Hif_head Helse_check].
      apply andb_true_iff in Hif_head as [Hif_head Hthen_check].
      apply andb_true_iff in Hif_head as [Hcond_bool Hprov_cond].
      destruct (IH env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 Hthen
        Hthen_check) as [ret_roots2 Hthen_summary].
      destruct (IH env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      eexists. eapply ERSCE_If.
      * apply provenance_ready_expr_b_sound. exact Hprov_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true_equiv. exact Hroot_eq.
Qed.

Lemma check_expr_root_shadow_captured_call_provenance_summary_sound_early :
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
  eapply check_expr_root_shadow_captured_call_provenance_summary_fuel_sound_early;
    eassumption.
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
  - apply orb_true_iff in Hcheck as [Hcheck | Hlocal_check].
    apply orb_true_iff in Hcheck as [Hcheck | Hif_check].
    + right. left.
    destruct (captured_call_target_expr (fn_body fdef))
      as [[[fname captures] args] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee_head Hrest].
    apply andb_true_iff in Hcallee_head as [Hlt Hdisjoint].
    apply PeanoNat.Nat.eqb_eq in Hlt.
    destruct (check_make_closure_captures_exact_sctx_with_env env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee)) as [[env_lt captured_tys] | err]
      eqn:Hcaptures;
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
    exists fname, captures, args, fcallee, env_lt, captured_tys,
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
    + right. right. left.
      destruct (fn_body fdef) eqn:Hbody_if; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fdef)
        (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (fn_body_ctx fdef)
        (EIf e1 e2 e3))
        as [[[[T_body Γ_out] R_body] roots_body] | err]
        eqn:Hcore; try discriminate.
      destruct (infer_env_roots_shadow_safe env fdef
        (initial_root_env_for_fn fdef))
        as [[[[T_env Γ_env] R_env] roots_env] | err]
        eqn:Hinfer_env; try discriminate.
      apply andb_true_iff in Hif_check as [Hif_head Henv].
      apply andb_true_iff in Hif_head as [Hif_head Hroots].
      apply andb_true_iff in Hif_head as [Hexpr Hcompat].
      destruct
        (check_expr_root_shadow_captured_call_provenance_summary_sound_early
          env (fn_outlives fdef) (fn_lifetimes fdef)
          (initial_root_env_for_fn fdef) (fn_body_ctx fdef)
          (EIf e1 e2 e3) T_body Γ_out R_body roots_body Hcore Hexpr)
        as [ret_roots Hexpr_summary].
      exists T_body, Γ_out, R_body, roots_body, ret_roots.
      repeat split.
      * eapply infer_env_roots_shadow_safe_params_nodup.
        exact Hinfer_env.
      * exact Hexpr_summary.
      * exact Hcompat.
      * apply fn_params_roots_exclude_b_sound. exact Hroots.
      * apply fn_params_root_env_excludes_b_sound. exact Henv.
    + right. right. right.
      destruct (local_captured_call_target_expr (fn_body fdef))
        as [[[[[[[[fname captures] args] m] x] T] direct_body]
              let_body] |] eqn:Htarget; try discriminate.
      apply andb_true_iff in Hlocal_check as [Hready_args Hrest].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
        eqn:Hlookup_b; try discriminate.
      apply andb_true_iff in Hrest as [Hcallee_head Hrest].
      apply andb_true_iff in Hcallee_head as [Hcallee_head Hnot_cap_name].
      apply andb_true_iff in Hcallee_head as [Hlt Hdisjoint].
      apply PeanoNat.Nat.eqb_eq in Hlt.
      apply negb_true_iff in Hnot_cap_name.
      destruct (check_make_closure_captures_exact_sctx_with_env env
        (fn_outlives fdef)
        (sctx_of_ctx (fn_body_ctx fdef))
        captures
        (fn_captures fcallee)) as [[env_lt captured_tys] | err]
        eqn:Hcaptures;
        try discriminate.
      apply andb_true_iff in Hrest as [Hcallee Hsummary].
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef direct_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_direct_check Γ_direct_check] R_direct] roots_direct] | err]
        eqn:Hinfer_direct; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef let_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_let_check Γ_let_check] R_let] roots_let] | err]
        eqn:Hinfer_let; try discriminate.
      apply andb_true_iff in Hsummary as [Hroots Henv].
      destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
        as [Hin_callee Hname_callee].
      destruct (local_captured_call_target_expr_sound
                  (fn_body fdef) fname captures args m x T direct_body
                  let_body Htarget)
        as (Hbody & Hdirect & Hlet & Husage & Hnot_caps & Hnot_free &
            Hnot_local).
      pose proof (infer_env_roots_shadow_safe_sound
                    env (fn_with_body fdef direct_body)
                    (initial_root_env_for_fn fdef)
                    T_direct_check Γ_direct_check R_direct roots_direct
                    Hinfer_direct) as Htyped_direct_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_direct_fn.
      destruct Htyped_direct_fn as
        (T_direct_body & Γ_direct_out & Htyped_direct & Hcompat_direct & _).
      cbn in Htyped_direct, Hcompat_direct.
      pose proof (infer_env_roots_shadow_safe_sound
                    env (fn_with_body fdef let_body)
                    (initial_root_env_for_fn fdef)
                    T_let_check Γ_let_check R_let roots_let
                    Hinfer_let) as Htyped_let_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_let_fn.
      destruct Htyped_let_fn as
        (T_let_body & Γ_let_out & Htyped_let & _).
      cbn in Htyped_let.
      exists fname, captures, args, m, x, T, direct_body, let_body,
        fcallee, env_lt, captured_tys, T_direct_body, Γ_direct_out, R_direct,
        roots_direct, T_let_body, Γ_let_out, R_let, roots_let.
      split; [exact Hbody|].
      split; [reflexivity|].
      split; [exact Hdirect|].
      split; [exact Hlet|].
      split; [exact Husage|].
      split; [exact Hnot_caps|].
      split.
      { eapply existsb_ident_eqb_false_notin. exact Hnot_cap_name. }
      split; [exact Hnot_free|].
      split; [exact Hnot_local|].
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
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef direct_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup.
        exact Hinfer_direct. }
      split; [exact Htyped_direct|].
      split; [exact Hcompat_direct|].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
      split; [apply fn_params_root_env_excludes_b_sound; exact Henv|].
      exact Htyped_let.
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

Lemma eval_make_closure_captured_call_expr_shadow_preserves_typing_with_callee_components :
  forall env Ω n R Σ args fname captures fdef s s' ret T Σ' R' roots
      env_lt captured_tys T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (ECallExpr (EMakeClosure fname captures) args) s' ret ->
    typed_env_roots_shadow_safe env Ω n R Σ
      (ECallExpr (EMakeClosure fname captures) args) T Σ' R' roots ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    store_typed env s' Σ' /\
    value_has_type env s' ret T.
Proof.
  intros env Ω n R Σ args fname captures fdef s s' ret T Σ' R' roots
    env_lt captured_tys T_body Γ_out R_body roots_body Hstore Hroots
    Hshadow Hrn Hnamed Hkeys Heval_expr Htyped Hunique Hin Hfname Hcaptures
    Hnodup_caps Hready_args Hnodup_binding Hprov_callee Htyped_callee
    Hcompat_callee Hexclude_roots_callee Hexclude_env_callee.
  dependent destruction Heval_expr.
  pose proof Heval_expr1 as Heval_make.
  dependent destruction Heval_expr1.
  dependent destruction Htyped.
  repeat match goal with
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      lazymatch f_runtime with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_callee" in
          assert (Hsame : f_runtime = fdef)
            by (eapply lookup_fn_unique_by_name;
                [ exact Hlookup | exact Hin | exact Hfname | exact Hunique ]);
          subst f_runtime
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_typed : fn_name ?f_typed = ?fname_call |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin
                | rewrite Hname_typed; exact Hfname ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name fdef = fn_name ?f_typed |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | symmetry; exact Hname_eq ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : ?fname_call = fn_name ?f_typed |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin
                | rewrite <- Hname_eq; exact Hfname ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name ?f_typed = fn_name fdef |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | exact Hname_eq ]);
          subst f_typed
      end
  end.
  match goal with
  | Htyped_args_shadow : typed_args_roots_shadow_safe env Ω n R Σ args
      (fn_params fdef) ?Sigma_args ?R_args ?arg_roots,
    Hlookup : lookup_fn ?fname_call (env_fns env) = Some fdef,
    Hcopy : copy_capture_store_as captures (fn_captures fdef) s =
      Some ?captured,
    Heval_args : eval_args env s args ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names (?captured ++ ?s_args))
      fdef = (?fcall, ?used'),
    Heval_body : eval env
      (bind_params (fn_params ?fcall) ?vs (?captured ++ ?s_args))
      (fn_body ?fcall) ?s_body ret |- _ =>
      pose proof (typed_args_roots_shadow_safe_roots
        env Ω n R Σ args (fn_params fdef) Sigma_args R_args arg_roots
        Htyped_args_shadow) as Htyped_args_roots;
      destruct
        (eval_make_closure_captured_call_expr_preserves_typing_with_callee_components
          env Ω n R Σ args fname_call captures captured fdef fcall used'
          s s_args s_body vs ret R_args Sigma_args arg_roots env_lt
          captured_tys T_body Γ_out R_body roots_body Hstore Hroots
          Hshadow Hrn Hnamed Hkeys
          (Eval_MakeClosure env s fname_call captures captured fdef
            Hlookup Hcopy)
          Hlookup Heval_args Hrename Heval_body Hcaptures Hnodup_caps
          Hready_args Htyped_args_roots Hnodup_binding Hprov_callee
          Htyped_callee Hcompat_callee Hexclude_roots_callee
          Hexclude_env_callee) as [_ [Hstore_final Hv]]
  end.
  split.
  - exact Hstore_final.
  - rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
Qed.

Lemma eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed env s' Σ' /\ value_has_type env s' ret T.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Heval Hunique.
  - destruct (proj1 eval_preserves_typing_roots_ready_mutual
        env s e s' ret Heval Ω n R Σ T Σ' R' roots
        H Hstore Hroots Hshadow Hrn
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e T Σ' R' roots H0))
      as [Hstore' [Hv _]].
    split; assumption.
  - subst synthetic_body.
    assert (Heval_call : eval env s (ECall fname args) s' ret).
    { unfold direct_call_target_expr in H.
      destruct e; try discriminate.
      - inversion H; subst. exact Heval.
      - destruct e; try discriminate.
        inversion H; subst.
        apply eval_call_expr_fn_as_call. exact Heval. }
    destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
        env s s' ret fname args Heval_call Ω n R Σ T Σ' R' roots
        fcallee H1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ (ECall fname args) T Σ' R' roots H6)
        Hunique H2 H3 H4)
      as [Hstore' [Hv _]].
    split; assumption.
  - assert (Hnodup_caps :
        NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
    { rewrite params_ctx_app, ctx_names_app in H5.
      eapply NoDup_app_right_ts. exact H5. }
    eapply eval_make_closure_captured_call_expr_shadow_preserves_typing_with_callee_components;
      eauto.
  - dependent destruction Heval.
    + destruct (proj1 eval_preserves_typing_roots_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hstore1 [_ _]].
      destruct (proj1 eval_preserves_roots_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hroots1 [_ [Hshadow1 Hrn1]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hnamed
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hnamed1 _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hkeys
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as Hkeys1.
      destruct (IHHsummary1 s1 s2 v Hstore1 Hroots1 Hshadow1 Hrn1
          Hnamed1 Hkeys1 Heval2 Hunique) as [Hstore2 Hv].
      split.
      * eapply store_typed_ctx_merge_left; eassumption.
      * eapply value_has_type_if_left_result. exact Hv.
    + destruct (proj1 eval_preserves_typing_roots_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hstore1 [_ _]].
      destruct (proj1 eval_preserves_roots_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hroots1 [_ [Hshadow1 Hrn1]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hnamed
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hnamed1 _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hkeys
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as Hkeys1.
      destruct (IHHsummary2 s1 s2 v Hstore1 Hroots1 Hshadow1 Hrn1
          Hnamed1 Hkeys1 Heval2 Hunique) as [Hstore3 Hv].
      assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3).
      { eapply typed_env_structural_branch_type_eq.
        - eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots.
          eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
          exact Hsummary1.
        - eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots.
          eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
          exact Hsummary2. }
      split.
      * eapply store_typed_ctx_merge_right; eassumption.
      * eapply value_has_type_if_right_result. exact Hv.
Unshelve.
  all: eauto.
Qed.

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
  induction fuel as [| fuel' IH]; intros env Ω n R Σ e T Σ' R' roots
    Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_captured_call_provenance_summary_fuel]
      in Hcheck.
    rewrite Hinfer in Hcheck.
    apply orb_true_iff in Hcheck as [Hnon_if | Hif].
    + apply orb_true_iff in Hnon_if as [Hprov_or_direct | Hcaptured].
      * apply orb_true_iff in Hprov_or_direct as [Hprov | Hdirect].
        -- eexists. eapply ERSCE_Provenance.
           ++ apply provenance_ready_expr_b_sound. exact Hprov.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
        -- destruct (direct_call_target_expr e)
             as [[[fname args] synthetic_body] |] eqn:Htarget;
             try discriminate.
           apply andb_true_iff in Hdirect as [Hready_args Hdirect].
           destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
             eqn:Hlookup_b; try discriminate.
           apply andb_true_iff in Hdirect as [Hcallee Hsynthetic_ok].
           destruct (infer_core_env_state_fuel_roots_shadow_safe
             (S fuel') env Ω n R Σ synthetic_body)
             as [[[[T_syn Σ_syn] R_syn] roots_syn] | err]
             eqn:Hsynthetic; try discriminate.
           destruct (direct_call_target_expr_ok_is_call
             (S fuel') env Ω n R Σ e T Σ' R' roots fname args
             synthetic_body Hinfer Htarget)
             as [He Hsynthetic_body].
           subst e synthetic_body.
           rewrite Hinfer in Hsynthetic. inversion Hsynthetic; subst.
           destruct (lookup_fn_b_sound fname (env_fns env) fcallee
             Hlookup_b) as [Hin_callee Hname_callee].
           eexists. eapply ERSCE_DirectCall.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply preservation_ready_args_b_sound. exact Hready_args.
           ++ exact Hin_callee.
           ++ exact Hname_callee.
           ++ apply check_fn_root_shadow_provenance_summary_sound.
              exact Hcallee.
	           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
	              exact Hinfer.
	           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
	              exact Hinfer.
      * destruct (captured_call_target_expr e)
          as [[[fname captures] args] |] eqn:Htarget; try discriminate.
        apply andb_true_iff in Hcaptured as [Hready_args Hcaptured].
        destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
          eqn:Hlookup_b; try discriminate.
        apply andb_true_iff in Hcaptured as [Hcaptured_head Hcallee].
        apply andb_true_iff in Hcaptured_head as [Hlt Hdisjoint].
        apply PeanoNat.Nat.eqb_eq in Hlt.
        destruct (check_make_closure_captures_exact_sctx_with_env env Ω Σ
          captures (fn_captures fcallee)) as [[env_lt captured_tys] | err]
          eqn:Hcaptures; try discriminate.
        destruct (capture_root_bound R captures (fn_captures fcallee))
          as [capture_roots |] eqn:Hcapture_bound; try discriminate.
        pose proof (captured_call_target_expr_ok_is_make_closure_call
          (S fuel') env Ω n R Σ e T Σ' R' roots fname captures args
          Hinfer Htarget) as He.
        subst e.
        destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
          as [Hin_callee Hname_callee].
        pose proof
          (check_fn_root_shadow_captured_callee_provenance_summary_sound
            env fcallee Hcallee) as Hcallee_summary.
        destruct Hcallee_summary as
          [Hnodup_binding
           (T_body & Γ_out & R_body & roots_body & Hprov_body &
            Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env)].
        eexists. eapply ERSCE_CapturedCall.
        -- apply preservation_ready_args_b_sound. exact Hready_args.
        -- exact Hin_callee.
        -- exact Hname_callee.
        -- exact Hlt.
        -- apply callee_hidden_capture_args_disjoint_b_sound.
           exact Hdisjoint.
        -- exact Hcaptures.
        -- exact Hnodup_binding.
        -- exact Hprov_body.
        -- exact Htyped_body.
        -- exact Hcompat_body.
        -- exact Hexclude_roots.
        -- exact Hexclude_env.
        -- exact Hcapture_bound.
        -- eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
           exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hif.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err] eqn:Hcond;
        try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans)
        eqn:Hcond_core; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
        Σ1 e2) as [[[[T2 Σ2] R2] roots2] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
        Σ1 e3) as [[[[T3 Σ3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2 R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3)) as [Γ4 |]
        eqn:Hmerge; try discriminate.
      apply andb_true_iff in Hif as [Hif_head Helse_check].
      apply andb_true_iff in Hif_head as [Hif_head Hthen_check].
      apply andb_true_iff in Hif_head as [Hcond_bool Hprov_cond].
      destruct (IH env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 Hthen
        Hthen_check) as [ret_roots2 Hthen_summary].
      destruct (IH env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      eexists. eapply ERSCE_If.
      * apply provenance_ready_expr_b_sound. exact Hprov_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true_equiv. exact Hroot_eq.
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
      [Hcaptured_summary | [Hif_summary | Hlocal_captured_summary]].
    + destruct Hcaptured_summary as
      (fname & captures & args & fcallee & env_lt & captured_tys &
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
        R_args Sigma_args arg_roots env_lt captured_tys T_callee Γ_callee
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
	    * rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
	    * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hif_summary as
        (T_body & Γ_out & R_body & roots_body & ret_roots & Hnodup &
          Hexpr_summary & Hcompat & _ & _).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
      destruct
        (eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing
          (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
          (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
          ret_roots Hexpr_summary s s' v Hstore Hroots Hstore_shadow
          Hroot_shadow Hnamed Hkeys Heval Hunique) as [_ Hv].
      eapply VHT_Compatible.
      * exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hlocal_captured_summary as
        (fname & captures & args & m & x & T & direct_body & let_body &
          fcallee & env_lt & captured_tys & T_direct & Γ_direct & R_direct &
          roots_direct & T_let & Γ_let & R_let & roots_let &
          Hbody & Htarget & Hdirect & Hlet & Husage & Hnot_caps &
          Hfresh_cap_names & Hfree_args & Hlocal_args & Hready_args &
          Hin_callee & Hname_callee & Hcallee_lts & Hdisjoint &
          Hcaptures & Hcallee_summary & Hnodup & Htyped_direct &
          Hcompat_direct & _ & _ & Htyped_let).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	      pose proof (lookup_fn_in_unique_by_name
	                    (alpha_normalize_global_env env) fname fcallee
	                    Hin_callee Hname_callee Hunique) as Hlookup_callee.
	      rewrite Hbody in Heval.
	      rewrite Hlet in Htyped_let.
	      rewrite Hdirect in Htyped_let.
	      rewrite Hdirect in Htyped_direct.
	      dependent destruction Htyped_direct.
	      repeat match goal with
	      | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
	        Hname_typed : fn_name ?f_typed = ?fname0,
	        Hname_callee0 : fn_name fcallee = ?fname0 |- _ =>
	          lazymatch f_typed with
	          | fcallee => fail
	          | _ =>
	              let Hsame := fresh "Hsame_typed_callee" in
	              assert (Hsame : f_typed = fcallee)
	                by (eapply Hunique;
	                    [ exact Hin_typed | exact Hin_callee
	                    | rewrite Hname_typed; symmetry; exact Hname_callee0 ]);
	              subst f_typed
	          end
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
	      | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
	        Hname_eq : fn_name ?f_typed = fn_name fcallee |- _ =>
	          lazymatch f_typed with
	          | fcallee => fail
	          | _ =>
	              let Hsame := fresh "Hsame_typed_callee" in
	              assert (Hsame : f_typed = fcallee)
	                by (eapply Hunique;
	                    [ exact Hin_typed | exact Hin_callee
	                    | exact Hname_eq ]);
	              subst f_typed
	          end
	      end.
      match goal with
      | Htyped_args_shadow : typed_args_roots_shadow_safe
          (alpha_normalize_global_env env) (fn_outlives f)
          (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) args (fn_params fcallee)
          ?Sigma_args ?R_args ?arg_roots |- _ =>
          pose proof (typed_args_roots_shadow_safe_roots
            (alpha_normalize_global_env env) (fn_outlives f)
            (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f)) args (fn_params fcallee)
            Sigma_args R_args arg_roots Htyped_args_shadow)
            as Htyped_args_roots
      end.
		      dependent destruction Htyped_let.
      match goal with
      | Hmake : typed_env_roots_shadow_safe _ _ _ ?R0 ?Σ0
          (EMakeClosure _ _) _ ?Σ1 ?R1 ?roots1 |- _ =>
          assert (Σ1 = Σ0 /\ R1 = R0 /\ roots1 = []) as Hmake_frame
      end.
      { match goal with
        | Hmake : typed_env_roots_shadow_safe _ _ _ _ _
            (EMakeClosure _ _) _ _ _ _ |- _ =>
            inversion Hmake; subst; repeat split
        end. }
      destruct Hmake_frame as [-> [-> ->]].
			      assert (Hfresh_store_lookup : store_lookup x0 s = None).
		      { match goal with
		        | Hlookup_x : root_env_lookup ?x (initial_root_env_for_fn f) = None
		            |- store_lookup ?x s = None =>
		            eapply store_roots_within_lookup_none; eassumption
		        end. }
	      assert (Hfresh_s : ~ In x0 (store_names s)).
	      { apply store_lookup_none_not_in_store_names.
	        exact Hfresh_store_lookup. }
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
      | Htyped_args_roots : typed_args_roots
          (alpha_normalize_global_env env) (fn_outlives f)
          (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) args (fn_params fcallee)
          ?Sigma_args ?R_args ?arg_roots |- _ =>
          destruct
	            (eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components
	              (alpha_normalize_global_env env) (fn_outlives f)
	              (fn_lifetimes f) (initial_root_env_for_fn f)
	              (sctx_of_ctx (fn_body_ctx f)) m x0 T args (fn_name fcallee) captures
	              fcallee s s' v R_args Sigma_args arg_roots env_lt captured_tys
              T_callee Γ_callee R_callee roots_callee
              Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
              Husage Heval Hcaptures Hnodup_caps Hready_args
              Htyped_args_roots Hnodup_binding Hprov_callee Htyped_callee
              Hcompat_callee Hexclude_roots_callee Hexclude_env_callee
              Hlookup_callee Hfresh_s Hfresh_cap_names Hfree_args
              Hlocal_args)
            as [_ Hv]
      end.
      eapply VHT_Compatible.
      * rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat_direct.
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
