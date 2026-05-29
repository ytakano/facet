From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers.
From Facet.TypeSystem Require Export EnvRuntimeValidatorFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition initial_store_for_fn (env : global_env) (f : fn_def) (s : store) : Prop :=
  store_typed env s (sctx_of_ctx (fn_body_ctx f)) /\
  store_function_closure_targets_summary env s.

Lemma initial_store_for_fn_store_typed :
  forall env f s,
    initial_store_for_fn env f s ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)).
Proof.
  intros env f s Hinitial. exact (proj1 Hinitial).
Qed.

Lemma initial_store_for_fn_closure_targets_summary :
  forall env f s,
    initial_store_for_fn env f s ->
    store_function_closure_targets_summary env s.
Proof.
  intros env f s Hinitial. exact (proj2 Hinitial).
Qed.

Lemma eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_store_function_closure_targets_summary :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    env_fns_root_shadow_provenance_summary_evidence env ->
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_function_closure_targets_summary env s'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hevidence Hsummary
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys _ Heval_callee Hunique.
  destruct (eval_expr_root_shadow_captured_call_provenance_summary_exact_package
    env Ω n R Σ e T Σ' R' roots ret_roots Hsummary s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval_callee Hunique)
    as [Hstore' _].
  eapply store_typed_function_closure_targets_summary; eassumption.
Qed.

Lemma eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary :
  forall env s s' x fname fdef,
    store_function_closure_targets_summary env s ->
    eval env s (EVar x) s' (VClosure fname []) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.
Proof.
  intros env s s' x fname fdef Hstore Heval_callee Hlookup.
  inversion Heval_callee; subst;
    match goal with
    | Hlookup_store : store_lookup ?x_lookup ?s_lookup = Some ?se |- _ =>
        pose proof
          (store_function_closure_targets_summary_lookup env s_lookup x_lookup se
            Hstore Hlookup_store) as Hvalue_summary
    end;
    match goal with
    | Hvalue_eq : se_val _ = VClosure _ _ |- _ =>
        rewrite Hvalue_eq in Hvalue_summary
    | Hvalue_eq : VClosure _ _ = se_val _ |- _ =>
        rewrite <- Hvalue_eq in Hvalue_summary
    end;
    simpl in Hvalue_summary;
    destruct Hvalue_summary as (fdef_summary & Hlookup_summary & Hsummary);
    assert (fdef_summary = fdef) as -> by
      (eapply lookup_fn_deterministic; eassumption);
    exact Hsummary.
Qed.

Inductive expr_root_shadow_store_safe_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSS_Exact : forall R Σ e T Σ' R' roots ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Omega n R Σ e T Σ' R' roots ret_roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots
  | ERSS_FunctionValueCall : forall R Σ x args T_callee Gamma_callee
      R_callee roots_callee T Σ' R' roots,
      preservation_ready_args args ->
      infer_core_env_roots_shadow_safe env Omega n R (ctx_of_sctx Σ)
        (EVar x) = infer_ok
          (T_callee, Gamma_callee, R_callee, roots_callee) ->
      supported_non_type_generic_function_value_call_callee_shape T_callee ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExpr (EVar x) args) T Σ' R' roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ECallExpr (EVar x) args) T Σ' R' roots roots
  | ERSS_Let : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSS_If : forall R R1 R2 R3 Σ Σ1 Sigma2 Sigma3 Sigma4
      e1 e2 e3 T_cond T2 T3 roots_cond roots2 roots3 ret_roots2 ret_roots3,
      provenance_ready_expr e1 ->
      typed_env_roots_shadow_safe env Omega n R Σ e1 T_cond Σ1 R1
        roots_cond ->
      ty_core T_cond = TBooleans ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e2 T2 Sigma2 R2 roots2 ret_roots2 ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 ret_roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Sigma2) (ctx_of_sctx Sigma3) = Some Sigma4 ->
      R2 = R3 ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        (sctx_of_ctx Sigma4) R2 (root_set_union roots2 roots3)
        (root_set_union ret_roots2 ret_roots3).

Lemma expr_root_shadow_store_safe_summary_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Omega n R Σ e T Σ' R' roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
    exact H.
  - exact H2.
  - eapply TERS_Let; eauto.
  - subst R3. eapply TERS_If; eauto. apply root_env_equiv_refl.
Qed.

Inductive store_safe_function_value_call_arg
    (env : global_env) : expr -> Prop :=
  | SSFVCArg_Var : forall x,
      store_safe_function_value_call_arg env (EVar x)
  | SSFVCArg_Fn : forall fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_provenance_summary env fdef ->
      store_safe_function_value_call_arg env (EFn fname).

Inductive store_safe_function_value_call_args
    (env : global_env) : list expr -> Prop :=
  | SSFVCArgs_Nil :
      store_safe_function_value_call_args env []
  | SSFVCArgs_Cons : forall arg rest,
      store_safe_function_value_call_arg env arg ->
      store_safe_function_value_call_args env rest ->
      store_safe_function_value_call_args env (arg :: rest).

Lemma store_safe_function_value_call_arg_preservation_ready :
  forall env arg,
    store_safe_function_value_call_arg env arg ->
    preservation_ready_expr arg.
Proof.
  intros env arg Harg.
  destruct Harg; constructor.
Qed.

Lemma store_safe_function_value_call_args_preservation_ready :
  forall env args,
    store_safe_function_value_call_args env args ->
    preservation_ready_args args.
Proof.
  intros env args Hargs.
  induction Hargs; constructor; auto.
  eapply store_safe_function_value_call_arg_preservation_ready; eassumption.
Qed.

Lemma store_safe_function_value_call_arg_eval_preserves_store_function_closure_targets_summary :
  forall env arg s s' v,
    store_safe_function_value_call_arg env arg ->
    store_function_closure_targets_summary env s ->
    eval env s arg s' v ->
    store_function_closure_targets_summary env s'.
Proof.
  intros env arg s s' v Harg Hsummary Heval_callee.
  destruct Harg.
  - eapply store_function_closure_targets_summary_eval_var; eassumption.
  - inversion Heval_callee; subst; auto.
Qed.

Lemma store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary :
  forall env args s s' vs,
    store_safe_function_value_call_args env args ->
    store_function_closure_targets_summary env s ->
    eval_args env s args s' vs ->
    store_function_closure_targets_summary env s'.
Proof.
  intros env args s s' vs Hargs Hsummary Heval_callee.
  revert s s' vs Hsummary Heval_callee.
  induction Hargs as [| arg rest Harg Hrest IH]; intros s s' vs Hsummary Heval_callee.
  - inversion Heval_callee; subst. exact Hsummary.
  - inversion Heval_callee; subst.
    eapply IH.
    + eapply store_safe_function_value_call_arg_eval_preserves_store_function_closure_targets_summary;
        eassumption.
    + eassumption.
Qed.

Lemma store_safe_function_value_call_args_b_sound :
  forall env args,
    store_safe_function_value_call_args_b env args = true ->
    store_safe_function_value_call_args env args.
Proof.
  intros env args.
  induction args as [| arg rest IH]; intros Hcheck.
  - constructor.
  - destruct arg; try discriminate; simpl in Hcheck.
    + constructor.
      * constructor.
      * apply IH. exact Hcheck.
    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hcallee Hrest].
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup)
        as [Hin Hname].
      constructor.
      * eapply SSFVCArg_Fn.
        -- exact Hin.
        -- exact Hname.
        -- apply check_fn_root_shadow_provenance_summary_sound. exact Hcallee.
      * apply IH. exact Hrest.
Qed.

Inductive expr_root_shadow_store_safe_narrow_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSSN_FunctionValueCall : forall R Σ x args T_callee Gamma_callee
      R_callee roots_callee T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      infer_core_env_roots_shadow_safe env Omega n R (ctx_of_sctx Σ)
        (EVar x) = infer_ok
          (T_callee, Gamma_callee, R_callee, roots_callee) ->
      supported_non_type_generic_function_value_call_callee_shape T_callee ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExpr (EVar x) args) T Σ' R' roots ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ECallExpr (EVar x) args) T Σ' R' roots roots
  | ERSSN_Let : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      non_function_value_ty_b T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots.

Lemma expr_root_shadow_store_safe_narrow_summary_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Omega n R Σ e T Σ' R' roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - exact H2.
  - eapply TERS_Let; eauto.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots s s',
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    store_typed env s Σ ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_typed env s' Σ' ->
    root_env_no_shadow R' ->
    root_env_store_roots_named R' s' /\
    root_set_store_roots_named roots s' /\
    root_env_store_keys_named R' s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots s s'
    Hsummary Hstore Hrn Hnamed Hkeys Hstore' Hrn'.
  pose proof (expr_root_shadow_store_safe_narrow_summary_typed
    env Omega n R Σ e T Σ' R' roots ret_roots Hsummary)
    as Htyped_shadow.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ e T Σ' R' roots Htyped_shadow)
    as Htyped_roots.
  assert (Hctx_roots : root_env_ctx_roots_named R Σ)
    by (eapply root_env_store_roots_named_to_ctx; eassumption).
  destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
    R Σ e T Σ' R' roots Htyped_roots Hrn Hctx_roots)
    as [Hctx_roots' Hctx_set'].
  assert (Hctx_keys : root_env_sctx_keys_named R Σ)
    by (eapply root_env_store_keys_named_to_ctx; eassumption).
  pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
    env Omega n) R Σ e T Σ' R' roots Htyped_shadow
    Hrn Hctx_keys) as Hctx_keys'.
  repeat split.
  - eapply root_env_ctx_roots_named_store_typed; eassumption.
  - eapply root_set_ctx_roots_named_store_typed; eassumption.
  - eapply root_env_ctx_keys_named_store_typed; eassumption.
Qed.

Lemma check_expr_root_shadow_store_safe_narrow_summary_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_narrow_summary_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_store_safe_narrow_summary_fuel] in Hcheck.
    rewrite Hinfer in Hcheck.
    destruct e; try discriminate.
    + simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
        try discriminate.
      destruct (non_function_value_ty_b t) eqn:Hnonfn;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2 Sigma2] R2] roots2] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[[Hfree_ret Hsctx_ok] Hroots2] Henv2]
        Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i t m Σ1) e2 T2 Sigma2 R2 roots2 Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_ok, Hroots2, Henv2 in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSSN_Let.
      all: try eassumption.
      all: try (apply roots_exclude_b_sound; assumption).
      all: try (apply root_env_excludes_b_sound; assumption).
      Unshelve.
      all: try eassumption.
      all: try (apply roots_exclude_b_sound; assumption).
      all: try (apply root_env_excludes_b_sound; assumption).
    + apply andb_true_iff in Hcheck as [Hready_args Hsupported].
      pose proof
        (check_supported_non_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hinfer_callee & Hcallee_shape).
      subst e.
      exists roots.
      eapply ERSSN_FunctionValueCall.
      * apply store_safe_function_value_call_args_b_sound. exact Hready_args.
      * exact Hinfer_callee.
      * exact Hcallee_shape.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hinfer.
Qed.

Lemma check_expr_root_shadow_store_safe_narrow_summary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_narrow_summary
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_narrow_summary,
    infer_core_env_roots_shadow_safe.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Omega n R
    (sctx_of_ctx Gamma) e) as [[[[T0 Sigma0] R0] roots0] | err]
    eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_narrow_summary_fuel_sound;
    eassumption.
Qed.

Lemma infer_core_env_roots_shadow_safe_evar_lookup_core_base :
  forall env Ω n R Γ x T_infer Γ_out R_out roots T_lookup st,
    infer_core_env_roots_shadow_safe env Ω n R Γ (EVar x) =
      infer_ok (T_infer, Γ_out, R_out, roots) ->
    sctx_lookup x (sctx_of_ctx Γ) = Some (T_lookup, st) ->
    ty_core T_infer = ty_core T_lookup.
Proof.
  intros env Ω n R Γ x T_infer Γ_out R_out roots T_lookup st
    Hinfer Hlookup.
  unfold infer_core_env_roots_shadow_safe in Hinfer.
  cbn in Hinfer.
  unfold consume_direct_place_value_roots, infer_place_roots in Hinfer.
  cbn in Hinfer.
  rewrite Hlookup in Hinfer.
  destruct (binding_available_b st []) eqn:Havailable; try discriminate.
  destruct (root_env_lookup x R) as [roots0 |] eqn:Hroot; try discriminate.
  destruct (usage_eqb (ty_usage T_lookup) UUnrestricted) eqn:Husage.
  - inversion Hinfer; subst. reflexivity.
  - destruct (sctx_consume_path (sctx_of_ctx Γ) x []) as [Σc | err]
      eqn:Hconsume; try discriminate.
    inversion Hinfer; subst. reflexivity.
Qed.

Lemma typed_env_roots_shadow_safe_evar_infer_core_base :
  forall env Ω n R Γ x T_typed Σ_out R_out roots_typed
      T_infer Γ_infer R_infer roots_infer,
    typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ) (EVar x)
      T_typed Σ_out R_out roots_typed ->
    infer_core_env_roots_shadow_safe env Ω n R Γ (EVar x) =
      infer_ok (T_infer, Γ_infer, R_infer, roots_infer) ->
    ty_core T_infer = ty_core T_typed.
Proof.
  intros env Ω n R Γ x T_typed Σ_out R_out roots_typed
    T_infer Γ_infer R_infer roots_infer Htyped Hinfer.
  dependent destruction Htyped.
  - match goal with
    | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace; subst
    end.
    eapply infer_core_env_roots_shadow_safe_evar_lookup_core_base; eassumption.
  - match goal with
    | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace; subst
    end.
    eapply infer_core_env_roots_shadow_safe_evar_lookup_core_base; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary :
  forall env Omega n R Σ x args T_callee Gamma_callee R_callee roots_callee T Σ' R' roots,
    store_safe_function_value_call_args env args ->
    infer_core_env_roots_shadow_safe env Omega n R (ctx_of_sctx Σ)
      (EVar x) = infer_ok (T_callee, Gamma_callee, R_callee, roots_callee) ->
    supported_non_type_generic_function_value_call_callee_shape T_callee ->
    typed_env_roots_shadow_safe env Omega n R Σ
      (ECallExpr (EVar x) args) T Σ' R' roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args T_callee Gamma_callee R_callee roots_callee T Σ' R' roots Hargs Hinfer_callee Hcallee_shape Htyped
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_callee Hunique.
  dependent destruction Heval_callee.
  match goal with
  | Hcallee_eval : eval env s (EVar x) s_fn (VClosure fname captured) |- _ =>
      rename Hcallee_eval into Heval_callee
  end.
  match goal with
  | Hlookup_fn : lookup_fn fname (env_fns env) = Some fdef |- _ =>
      rename Hlookup_fn into Hlookup
  end.
  match goal with
  | Hargs_eval : eval_args env s_fn args s_args vs |- _ =>
      rename Hargs_eval into Heval_args
  end.
  match goal with
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = (fcall, used') |- _ =>
      rename Halpha into Hrename
  end.
  match goal with
  | Hbody_eval : eval env (bind_params (fn_params fcall) vs (captured ++ s_args)) (fn_body fcall) s_body ret |- _ =>
      rename Hbody_eval into Heval_body
  end.
  pose proof (store_function_closure_targets_summary_eval_var
    env s s_fn x (VClosure fname captured) Hsummary Heval_callee) as Hsummary_fn.
  pose proof
    (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
      env args s_fn s_args vs Hargs Hsummary_fn Heval_args) as Hsummary_args.
  dependent destruction Htyped.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TFn param_tys ret))
      Σ1 R1 roots_callee0 Htyped) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TFn param_tys ret))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [_ [Hv_callee _]].
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TFn param_tys ret)) Hv_callee) as Hcaptured_nil.
    subst captured.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
    pose proof (eval_call_expr_tfn_components_final_store_eq
      env s s_fn s_args s_body (EVar x) args fname [] fdef fcall
      vs ret0 used' Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      param_tys ret (store_safe_function_value_call_args_preservation_ready env args Hargs)
      (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Htyped H0 Hunique Hcallee_summary) as Heq_final.
    rewrite Heq_final. exact Hsummary_args.
  - pose proof (typed_env_roots_shadow_safe_evar_infer_core_base
      env Omega n R (ctx_of_sctx Σ) x (MkTy u (TClosure env_lt param_tys ret))
      Σ1 R1 roots_callee0 T_callee Gamma_callee R_callee roots_callee
      Htyped Hinfer_callee) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape];
      rewrite Hcore in Hshape; simpl in Hshape; discriminate.
  - match goal with
    | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
        ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_infer_core_base
          env Omega n R (ctx_of_sctx Σ) x T_typed
          Σ_typed R_typed roots_typed
          T_callee Gamma_callee R_callee roots_callee
          Htyped_callee Hinfer_callee) as Hcore;
        destruct Hcallee_shape as
          [Tshape params_shape ret_shape Hshape
          | Tshape m_shape bounds_shape body_shape params_shape ret_shape
              Hshape Hbody_shape];
        rewrite Hcore in Hshape; simpl in Hshape;
        first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
    end.
  - match goal with
    | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
        ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_infer_core_base
          env Omega n R (ctx_of_sctx Σ) x T_typed
          Σ_typed R_typed roots_typed
          T_callee Gamma_callee R_callee roots_callee
          Htyped_callee Hinfer_callee) as Hcore;
        destruct Hcallee_shape as
          [Tshape params_shape ret_shape Hshape
          | Tshape m_shape bounds_shape body_shape params_shape ret_shape
              Hshape Hbody_shape];
        rewrite Hcore in Hshape; simpl in Hshape;
        first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
    end.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 Htyped) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
    destruct (proj1 eval_preserves_root_names_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Hnamed Htyped_callee_roots) as [Hnamed_fn _].
    pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x) Hstore Hroots Hshadow Hrn
      Hkeys Htyped_callee_roots) as Hkeys_fn.
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
    subst captured.
    simpl in Hrename, Heval_body.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
    destruct (value_has_type_empty_closure_tforall_tfn_components
      env s_fn fname fdef u m bounds body_ty param_tys ret σ
      Hv_callee Hlookup Hunique H0) as [Htype_params [Hcaps_fdef Hbridge]].
    pose proof (typed_args_roots_shadow_safe_roots
      env Omega n R1 Σ1 args
      (params_of_tys (map (open_bound_ty σ) param_tys))
      Σ' R' arg_roots H4) as Htyped_args.
    pose proof (preservation_ready_args_implies_provenance_ready_closure
      args (store_safe_function_value_call_args_preservation_ready env args Hargs)) as Hprov_args.
    assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
    { eapply direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset;
        eassumption. }
    pose proof (eval_evar_call_expr_lifetime_forall_tfn_components_final_store_eq
      env s s_fn s_args s_body x args fname [] fdef fcall vs ret0 used'
      Heval_callee Hlookup Heval_args Hrename Heval_body Omega n R Σ Σ1 R1 Σ' R'
      roots_callee0 arg_roots u m bounds body_ty param_tys ret σ (store_safe_function_value_call_args_preservation_ready env args Hargs)
      Hstore Hroots Hshadow Hrn Htyped H0 H4 Htype_params Hcaps_fdef
      Hbridge Hcallee_route) as Heq_final.
    rewrite Heq_final. exact Hsummary_args.
  - pose proof (typed_env_roots_shadow_safe_evar_infer_core_base
      env Omega n R (ctx_of_sctx Σ) x (MkTy u (TForall m bounds body_ty))
      Σ1 R1 roots_callee0 T_callee Gamma_callee R_callee roots_callee
      Htyped Hinfer_callee) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape].
    + rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + rewrite Hcore in Hshape; simpl in Hshape.
      inversion Hshape; subst.
      simpl in Hbody_shape. rewrite H0 in Hbody_shape. discriminate.
Qed.

Definition callee_body_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_captured_call_provenance_summary env fdef \/
  exists T_body Gamma_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma check_fn_root_shadow_captured_call_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_store_safe_summary in Hcheck.
  apply orb_true_iff in Hcheck as [Hold | Hnarrow].
  - left. apply check_fn_root_shadow_captured_call_provenance_summary_sound.
    exact Hold.
  - right.
    destruct (infer_core_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef))
      as [[[[T_body Gamma_body] R_body] roots_body] | err] eqn:Hcore;
      try discriminate.
    destruct (infer_env_roots_shadow_safe env fdef
      (initial_root_env_for_fn fdef))
      as [[[[T_env Gamma_env] R_env] roots_env] | err] eqn:Hinfer_env;
      try discriminate.
    repeat rewrite andb_true_iff in Hnarrow.
    destruct Hnarrow as [[[Hexpr Hcompat] Hroots] Henv].
    destruct (check_expr_root_shadow_store_safe_narrow_summary_sound
      env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef)
      T_body Gamma_body R_body roots_body Hcore Hexpr)
      as [ret_roots Hsummary].
    exists T_body, Gamma_body, R_body, roots_body, ret_roots.
    repeat split.
    + eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer_env.
    + exact Hsummary.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Definition env_fns_root_shadow_captured_call_store_safe_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.

Lemma check_env_root_shadow_captured_call_store_safe_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_store_safe_summary env = true ->
    env_fns_root_shadow_captured_call_store_safe_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_store_safe_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
  exact Hcheck.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_summary_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_store_safe_summary_fuel] in Hcheck.
    rewrite Hinfer in Hcheck.
    repeat (apply orb_true_iff in Hcheck as [Hcheck | Hcheck]).
    + destruct (check_expr_root_shadow_captured_call_provenance_summary_fuel_sound
        (S fuel') env Omega n R Σ e T Σ' R' roots Hinfer Hcheck)
        as [ret_roots Hexact].
      exists ret_roots. apply ERSS_Exact. exact Hexact.
    + destruct e; try discriminate.
      apply andb_true_iff in Hcheck as [Hready_args Hsupported].
      pose proof
        (check_supported_non_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hinfer_callee & Hcallee_shape).
      subst e.
      exists roots.
      eapply ERSS_FunctionValueCall.
      * apply preservation_ready_args_b_sound. exact Hready_args.
      * exact Hinfer_callee.
      * exact Hcallee_shape.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2 Sigma2] R2] roots2] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[[Hfree_ret Hsctx_ok] Hroots2] Henv2]
        Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i t m Σ1) e2 T2 Sigma2 R2 roots2 Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_ok, Hroots2, Henv2 in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSS_Let.
      * exact Hbound_summary.
      * exact Hcompat.
      * exact Hlookup_x.
      * apply roots_exclude_b_sound. exact Hroots1.
      * apply root_env_excludes_b_sound. exact Henv1.
      * exact Hbody_summary.
      * exact Hfree_ret.
      * exact Hsctx_ok.
      * apply roots_exclude_b_sound. exact Hroots2.
      * apply root_env_excludes_b_sound. exact Henv2.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err]
        eqn:Hcond; try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans) eqn:Hcond_core;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Helse_check].
      apply andb_true_iff in Hhead as [Hhead Hthen_check].
      apply andb_true_iff in Hhead as [Hcond_bool Hready_cond].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e2) as [[[[T2 Sigma2] R2] roots2] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e3) as [[[[T3 Sigma3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2 R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Sigma2) (ctx_of_sctx Sigma3))
        as [Sigma4 |] eqn:Hmerge; try discriminate.
      destruct (IH env Omega n R1 Σ1 e2 T2 Sigma2 R2 roots2 Hthen
        Hthen_check) as [ret_roots2 Hthen_summary].
      destruct (IH env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      exists (root_set_union ret_roots2 ret_roots3).
      eapply ERSS_If.
      * apply provenance_ready_expr_b_sound. exact Hready_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true. exact Hroot_eq.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_summary
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_summary,
    infer_core_env_roots_shadow_safe.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Omega n R
    (sctx_of_ctx Gamma) e) as [[[[T0 Sigma0] R0] roots0] | err]
    eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_summary_fuel_sound;
    eassumption.
Qed.

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
	  - induction l0 as [| a rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
	  - rewrite IH.
	    induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l1 as [| [fname field] rest IHfields]; simpl.
    + reflexivity.
    + rewrite IH, IHfields. reflexivity.
	  - induction l1 as [| payload rest IHargs]; simpl.
	    + reflexivity.
	    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| [[name binders] branch] rest IHbranches]; simpl.
    + reflexivity.
    + rewrite IH, IHbranches. reflexivity.
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
  destruct (infer_core_env (global_env_with_local_bounds env (fn_bounds f))
              (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
              (fn_body f))
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
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Htyped)
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
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
  - eapply initial_store_for_fn_store_typed. exact Hstore.
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
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
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
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique_body_env Hfns_ready_body_env
      (direct_call_callee_body_root_evidence_of_check body_env
        Hcallee_body_roots))
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
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
    direct_call_callee_body_root_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
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
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) R0
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R' roots
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Htyped
      Hunique_body_env Hfns_ready_body_env Hcallee_body_roots)
    as [_ [Hv _]].
  assert (Hv_env : value_has_type env s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
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
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
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
    direct_call_callee_body_root_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
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
    direct_call_callee_body_root_summary_bridge
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
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
  - apply env_fns_root_summary_evidence_of_check.
    apply env_fns_root_summary_check_ready_global_env_with_local_bounds.
    exact Hsummary.
  - exact Hbridge.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    direct_call_callee_body_root_shadow_summary_bridge
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
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
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
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
  pose (body_env :=
    global_env_with_local_bounds (alpha_normalize_global_env env)
      (fn_bounds f)).
  assert (Hstore_body_env :
      store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env.
    eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. exact Hunique. }
  assert (Hfns_ready_body_env : env_fns_preservation_ready body_env).
  { subst body_env. exact Hfns_ready. }
  assert (Hsummary_body :
      env_fns_root_shadow_summary_evidence body_env).
  { subst body_env.
    apply env_fns_root_shadow_summary_evidence_global_env_with_local_bounds.
    exact Hsummary. }
  destruct (eval_preserves_typing_direct_call_roots_ready
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hready Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
      (typed_env_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
        Htyped_shadow)
      Hunique_body_env Hfns_ready_body_env
      (direct_call_callee_body_root_evidence_of_shadow_summary_bridge
        body_env
        Hsummary_body
        (direct_call_callee_body_root_shadow_summary_bridge_of_unique
          body_env Hunique_body_env)))
    as [_ [Hv _]].
  assert (Hv_env :
      value_has_type (alpha_normalize_global_env env) s' v T_body).
  { subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
  eapply VHT_Compatible.
  - exact Hv_env.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.
