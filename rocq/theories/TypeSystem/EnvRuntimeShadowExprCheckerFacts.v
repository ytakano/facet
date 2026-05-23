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
      * apply root_env_eqb_true. exact Hroot_eq.
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
