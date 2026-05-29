From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual.
From Facet.TypeSystem Require Export EnvRuntimeValidatorFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition value_function_closure_targets_summary
    (env : global_env) (v : value) : Prop :=
  match v with
  | VClosure fname [] =>
      exists fdef,
        lookup_fn fname (env_fns env) = Some fdef /\
        callee_body_root_shadow_provenance_summary env fdef
  | _ => True
  end.

Definition store_function_closure_targets_summary
    (env : global_env) (s : store) : Prop :=
  Forall (fun se => value_function_closure_targets_summary env (se_val se)) s.

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

Lemma value_function_closure_targets_summary_global_env_with_local_bounds :
  forall env bounds v,
    value_function_closure_targets_summary env v ->
    value_function_closure_targets_summary (global_env_with_local_bounds env bounds) v.
Proof.
  intros env bounds v Hsummary.
  destruct v; simpl in *; auto.
Qed.

Lemma store_function_closure_targets_summary_global_env_with_local_bounds :
  forall env bounds s,
    store_function_closure_targets_summary env s ->
    store_function_closure_targets_summary (global_env_with_local_bounds env bounds) s.
Proof.
  unfold store_function_closure_targets_summary.
  intros env bounds s Hsummary.
  induction Hsummary; constructor; auto.
Qed.

Lemma store_function_closure_targets_summary_lookup :
  forall env s x se,
    store_function_closure_targets_summary env s ->
    store_lookup x s = Some se ->
    value_function_closure_targets_summary env (se_val se).
Proof.
  unfold store_function_closure_targets_summary.
  intros env s x se Hsummary Hlookup.
  induction Hsummary as [| se0 rest Hhead Htail IH]; simpl in Hlookup.
  - discriminate.
  - destruct (ident_eqb x (se_name se0)) eqn:Heq.
    + inversion Hlookup; subst. exact Hhead.
    + apply IH. exact Hlookup.
Qed.

Fixpoint non_function_value_ty_b (T : Ty) : bool :=
  match T with
  | MkTy _ (TFn _ _) => false
  | MkTy _ (TClosure _ _ _) => false
  | MkTy _ (TForall _ _ body) => non_function_value_ty_b body
  | MkTy _ (TTypeForall _ _ body) => non_function_value_ty_b body
  | _ => true
  end.

Lemma non_function_value_ty_b_fn_value_ty :
  forall f,
    non_function_value_ty_b (fn_value_ty f) = false.
Proof.
  intros f.
  unfold non_function_value_ty_b, fn_value_ty, fn_signature_ty_with_usage.
  destruct (fn_type_params f); destruct (fn_lifetimes f); simpl; reflexivity.
Qed.

Lemma ty_compatible_non_function_value_ty_b :
  forall Ω T_actual T_expected,
    ty_compatible Ω T_actual T_expected ->
    non_function_value_ty_b T_expected = true ->
    non_function_value_ty_b T_actual = true.
Proof.
  intros Ω T_actual T_expected Hcompat.
  induction Hcompat; simpl; intros Hnonfn; try discriminate; auto.
  - subst. exact Hnonfn.
Qed.

Lemma ty_lifetime_equiv_non_function_value_ty_b :
  forall T_actual T_expected,
    ty_lifetime_equiv T_actual T_expected ->
    non_function_value_ty_b T_expected = true ->
    non_function_value_ty_b T_actual = true.
Proof.
  intros T_actual T_expected Hequiv.
  induction Hequiv; simpl; intros Hnonfn; try discriminate; auto.
Qed.

Lemma value_has_type_empty_closure_non_function_value_ty_b_false :
  forall env s fname T,
    value_has_type env s (VClosure fname []) T ->
    non_function_value_ty_b T = false.
Proof.
  intros env s fname T Htyped.
  remember (VClosure fname []) as v eqn:Hv.
  induction Htyped; try discriminate.
  - apply non_function_value_ty_b_fn_value_ty.
  - apply non_function_value_ty_b_fn_value_ty.
  - assert (Hactual : non_function_value_ty_b T_actual = false) by auto.
    destruct (non_function_value_ty_b T_expected) eqn:Hexpected; auto.
    pose proof (ty_compatible_non_function_value_ty_b
      Ω T_actual T_expected H Hexpected) as Hactual_true.
    rewrite Hactual in Hactual_true. discriminate.
  - assert (Hactual : non_function_value_ty_b T_actual = false) by auto.
    destruct (non_function_value_ty_b T_expected) eqn:Hexpected; auto.
    pose proof (ty_lifetime_equiv_non_function_value_ty_b
      T_actual T_expected H Hexpected) as Hactual_true.
    rewrite Hactual in Hactual_true. discriminate.
Qed.

Lemma value_has_type_non_function_value_summary :
  forall env s v T,
    value_has_type env s v T ->
    non_function_value_ty_b T = true ->
    value_function_closure_targets_summary env v.
Proof.
  intros env s v T Htyped Hnonfn.
  destruct v; simpl; auto.
  destruct l as [| se captured]; simpl; auto.
  pose proof (value_has_type_empty_closure_non_function_value_ty_b_false
    env s i T Htyped) as Hfalse.
  rewrite Hnonfn in Hfalse. discriminate.
Qed.

Lemma store_function_closure_targets_summary_add_value_summary :
  forall env s x T v,
    store_function_closure_targets_summary env s ->
    value_function_closure_targets_summary env v ->
    store_function_closure_targets_summary env (store_add x T v s).
Proof.
  unfold store_function_closure_targets_summary, store_add.
  intros env s x T v Hsummary Hvalue.
  constructor; auto.
Qed.

Lemma store_function_closure_targets_summary_add_non_function :
  forall env s x T v,
    store_function_closure_targets_summary env s ->
    value_has_type env s v T ->
    non_function_value_ty_b T = true ->
    store_function_closure_targets_summary env (store_add x T v s).
Proof.
  intros env s x T v Hsummary Htyped Hnonfn.
  apply store_function_closure_targets_summary_add_value_summary; auto.
  eapply value_has_type_non_function_value_summary; eassumption.
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
