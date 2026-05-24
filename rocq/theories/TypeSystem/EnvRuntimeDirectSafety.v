From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeBaseSafety.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

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
  pose proof (check_program_env_alpha_checked env Hcheck) as Hchecked.
  unfold check_program_env in Hchecked.
  apply forallb_forall with (x := f) in Hchecked; [| exact Hin].
  destruct (infer_full_env (alpha_normalize_global_env env) f) as
    [[T Γ'] | err] eqn:Hinfer.
  - eapply infer_full_env_alpha_big_step_safe_with_direct_call_sidecar_ready;
      eassumption.
  - simpl in Hchecked. discriminate.
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
  pose (body_env :=
    global_env_with_local_bounds (alpha_normalize_global_env env)
      (fn_bounds f)).
  assert (Hstore_body_env :
      store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds. exact Hstore. }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hprov_body Hstore_body_env Hroots Hstore_shadow Hroot_shadow
      (typed_env_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
        Htyped_shadow))
    as [_ [Hv _]].
  assert (Hv_env :
      value_has_type (alpha_normalize_global_env env) s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
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
	    pose (body_env :=
	      global_env_with_local_bounds (alpha_normalize_global_env env)
	        (fn_bounds f)).
	    assert (Hstore_body_env :
	        store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	    { subst body_env.
	      eapply store_typed_global_env_with_local_bounds. exact Hstore. }
	    assert (Heval_body_env : eval body_env s (fn_body f) s' v).
	    { subst body_env.
	      eapply eval_global_env_with_local_bounds. exact Heval. }
	    destruct (proj1 eval_preserves_typing_roots_ready_mutual
	        body_env s (fn_body f) s' v Heval_body_env
	        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
	        (sctx_of_ctx (fn_body_ctx f))
	        T_body (sctx_of_ctx Γ_out) R_body roots_body
	        Hprov_body Hstore_body_env Hroots Hstore_shadow Hroot_shadow
	        (typed_env_roots_shadow_safe_roots
	          body_env (fn_outlives f) (fn_lifetimes f)
	          (initial_root_env_for_fn f)
	          (sctx_of_ctx (fn_body_ctx f))
	          (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
	          Htyped_shadow))
	      as [_ [Hv _]].
	    assert (Hv_env :
	        value_has_type (alpha_normalize_global_env env) s' v T_body).
	    { subst body_env.
	      eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	    eapply VHT_Compatible.
	    + exact Hv_env.
	    + apply ty_compatible_b_sound. exact Hcompat.
	  - destruct Hdirect_summary as
	      (fname & args & raw_body & synthetic_body & fcallee & T_body &
	        Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
	        Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
	        Hnodup & Htyped_shadow & Hcompat & _ & _).
	    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	    rewrite Hbody in Heval.
	    pose (body_env :=
	      global_env_with_local_bounds (alpha_normalize_global_env env)
	        (fn_bounds f)).
	    assert (Hstore_body_env :
	        store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	    { subst body_env.
	      eapply store_typed_global_env_with_local_bounds. exact Hstore. }
	    assert (Heval_body_env : eval body_env s raw_body s' v).
	    { subst body_env.
	      eapply eval_global_env_with_local_bounds. exact Heval. }
	    assert (Htyped_call :
	      typed_env_roots_shadow_safe body_env
	        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
	        (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
	        T_body (sctx_of_ctx Γ_out) R_body roots_body).
	    { rewrite <- Hsynthetic. exact Htyped_shadow. }
	    assert (Heval_call :
	      eval body_env s (ECall fname args) s' v).
	    { unfold direct_call_target_expr in Htarget.
	      destruct raw_body; try discriminate.
	      - inversion Htarget; subst. exact Heval_body_env.
	      - destruct raw_body; try discriminate.
	        inversion Htarget; subst.
	        apply eval_call_expr_fn_as_call. exact Heval_body_env. }
	    assert (Hcallee_summary_body :
	        callee_body_root_shadow_provenance_summary body_env fcallee).
	    { subst body_env.
	      apply
	        callee_body_root_shadow_provenance_summary_global_env_with_local_bounds.
	      exact Hcallee_summary. }
	    destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
	        body_env s s' v fname args Heval_call
	        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
	        (sctx_of_ctx (fn_body_ctx f))
	        T_body (sctx_of_ctx Γ_out) R_body roots_body fcallee
	        Hready_args Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
	        (typed_env_roots_shadow_safe_roots
	          body_env (fn_outlives f) (fn_lifetimes f)
	          (initial_root_env_for_fn f)
	          (sctx_of_ctx (fn_body_ctx f))
	          (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body roots_body
	          Htyped_call)
	        Hunique Hin_callee Hname_callee Hcallee_summary_body)
	      as [_ [Hv _]].
	    assert (Hv_env :
	        value_has_type (alpha_normalize_global_env env) s' v T_body).
	    { subst body_env.
	      eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	    eapply VHT_Compatible.
	    + exact Hv_env.
	    + apply ty_compatible_b_sound. exact Hcompat.
Qed.
