From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeInitialFacts
  TypeSafetyStoreSafeFunctionValueCallFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma store_safe_function_value_call_arg_eval_preserves_store_function_closure_targets_summary :
  forall env arg s s' v,
    store_safe_function_value_call_arg env arg ->
    store_function_closure_targets_summary env s ->
    eval env s arg s' v ->
    store_function_closure_targets_summary env s'.
Proof.
  intros env arg s s' v Harg Hsummary Heval_callee.
  destruct Harg.
  - inversion Heval_callee; subst; auto.
  - inversion Heval_callee; subst; auto.
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

Lemma store_safe_function_value_call_arg_eval_value_summary :
  forall env arg s s' v,
    fn_env_unique_by_name env ->
    store_safe_function_value_call_arg env arg ->
    store_function_closure_targets_summary env s ->
    eval env s arg s' v ->
    value_function_closure_targets_summary env v.
Proof.
  intros env arg s s' v Hunique Harg Hsummary Heval_arg.
  destruct Harg as [| lit | x | fname fdef Hin Hname Hcallee].
  - inversion Heval_arg; subst; simpl; auto.
  - inversion Heval_arg; subst; simpl; auto.
  - inversion Heval_arg; subst;
      match goal with
      | Hlookup : store_lookup _ _ = Some _ |- _ =>
          eapply store_function_closure_targets_summary_lookup; eassumption
      end.
  - pose proof (lookup_fn_in_unique_by_name env fname fdef
        Hin Hname Hunique) as Hlookup.
    inversion Heval_arg; subst.
    simpl. exists fdef. split.
    + exact Hlookup.
    + exact Hcallee.
Qed.

Lemma store_safe_function_value_call_args_eval_values_summary :
  forall env args s s' vs,
    fn_env_unique_by_name env ->
    store_safe_function_value_call_args env args ->
    store_function_closure_targets_summary env s ->
    eval_args env s args s' vs ->
    Forall (value_function_closure_targets_summary env) vs.
Proof.
  intros env args s s' vs Hunique Hargs Hsummary Heval_args.
  revert s s' vs Hsummary Heval_args.
  induction Hargs as [| arg rest Harg Hrest IH]; intros s s' vs Hsummary Heval_args.
  - inversion Heval_args; subst. constructor.
  - inversion Heval_args; subst.
    constructor.
    + eapply store_safe_function_value_call_arg_eval_value_summary; eassumption.
    + eapply IH.
      * eapply store_safe_function_value_call_arg_eval_preserves_store_function_closure_targets_summary;
          eassumption.
      * eassumption.
Qed.

Lemma store_safe_function_value_call_args_bind_params_summary :
  forall env args ps s s_args vs,
    fn_env_unique_by_name env ->
    store_safe_function_value_call_args env args ->
    store_function_closure_targets_summary env s ->
    eval_args env s args s_args vs ->
    store_function_closure_targets_summary env
      (bind_params ps vs s_args).
Proof.
  intros env args ps s s_args vs Hunique Hargs Hsummary Heval_args.
  eapply store_function_closure_targets_summary_bind_params_values.
  - eapply store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary;
      eassumption.
  - eapply store_safe_function_value_call_args_eval_values_summary; eassumption.
Qed.

Lemma store_safe_function_value_call_args_eval_runtime_package_prefix_named :
  forall env Ω n R Σ args ps Σ_args R_args arg_roots s s_args vs,
    store_safe_function_value_call_args env args ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    store_typed_prefix env s_args Σ_args /\
    eval_args_values_have_types env Ω s_args vs ps /\
    store_ref_targets_preserved env s s_args /\
    store_roots_within R_args s_args /\
    Forall2 value_roots_within arg_roots vs /\
    store_no_shadow s_args /\
    root_env_no_shadow R_args /\
    root_env_store_roots_named R_args s_args /\
    root_env_store_keys_named R_args s_args /\
    store_function_closure_targets_summary env s_args.
Proof.
  intros env Ω n R Σ args ps Σ_args R_args arg_roots s s_args vs
    Hsafe_args Htyped_args Heval_args Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps Σ_args R_args
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
    as [Hstore_args [Hargs_values [Hpres_args [Hroots_args
      [Harg_roots_values [Hshadow_args Hrn_args]]]]]].
  assert (Hsummary_args : store_function_closure_targets_summary env s_args).
  { eapply store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary;
      eassumption. }
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args ps Σ_args R_args arg_roots s s_args vs
              Hsafe_args Htyped_args Heval_args Hnamed Hkeys)
    as [Hnamed_args [_ Hkeys_args]].
  repeat split; assumption.
Qed.

Lemma generic_direct_call_args_bind_params_runtime_package :
  forall env Ω n R Σ args type_args sigma fdef fcall used'
      s s_args vs Σ_args R_args arg_roots,
    store_safe_function_value_call_args env args ->
    eval_args env s args s_args vs ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params sigma (apply_type_params type_args (fn_params fdef)))
      Σ_args R_args arg_roots ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    fn_env_unique_by_name env ->
    store_function_closure_targets_summary env s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    let ps_call :=
      apply_lt_params sigma (apply_type_params type_args (fn_params fcall)) in
    store_typed_prefix env (bind_params ps_call vs s_args)
      (sctx_of_ctx (params_ctx ps_call)) /\
    store_roots_within (call_param_root_env ps_call arg_roots R_args)
      (bind_params ps_call vs s_args) /\
    store_no_shadow (bind_params ps_call vs s_args) /\
    root_env_no_shadow (call_param_root_env ps_call arg_roots R_args) /\
    root_env_covers_params ps_call
      (call_param_root_env ps_call arg_roots R_args) /\
    root_env_store_roots_named
      (call_param_root_env ps_call arg_roots R_args)
      (bind_params ps_call vs s_args) /\
    root_env_store_keys_named
      (call_param_root_env ps_call arg_roots R_args)
      (bind_params ps_call vs s_args) /\
    store_function_closure_targets_summary env
      (bind_params ps_call vs s_args) /\
    store_param_scope ps_call (bind_params ps_call vs s_args) s_args.
Proof.
  intros env Ω n R Σ args type_args sigma fdef fcall used' s s_args
    vs Σ_args R_args arg_roots Hsafe_args Heval_args Htyped_args Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hunique Hsummary_store Hrename ps_call.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params sigma
                (apply_type_params type_args (fn_params fdef)))
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Htyped_args)
    as [_ [Hargs_values_fdef [_ [_ [_ [_ Hrn_args]]]]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct (alpha_rename_fn_def_generic_call_bind_params_premises
              env Ω s_args vs sigma type_args fdef fcall used'
              Hargs_values_fdef Hshape Hrename)
    as [Hnodup [Hfresh Hargs_values_fcall]].
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params sigma
                (apply_type_params type_args (fn_params fdef)))
              Σ_args R_args arg_roots ps_call Heval_args Hprov_args
              Htyped_args Hroots Hshadow Hrn Hnodup Hfresh
              Hargs_values_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params sigma
                (apply_type_params type_args (fn_params fdef)))
              Σ_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
              Heval_args Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  repeat split.
  - eapply bind_params_store_typed_prefix; eassumption.
  - exact Hroots_bind.
  - exact Hshadow_bind.
  - exact Hrn_bind.
  - exact Hcover_bind.
  - eapply root_env_store_roots_named_call_param_bind_params;
      eassumption.
  - eapply root_env_store_keys_named_call_param_bind_params;
      eassumption.
  - eapply store_safe_function_value_call_args_bind_params_summary;
      eassumption.
  - eapply store_param_scope_bind_params. exact Hargs_values_fcall.
Qed.

Lemma generic_direct_call_args_bind_type_params_runtime_package_seed :
  forall env Ω n R Σ args type_args sigma fdef fcall used' (seed : list ident)
      s s_args vs Σ_args R_args arg_roots,
    store_safe_function_value_call_args env args ->
    eval_args env s args s_args vs ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params sigma (apply_type_params type_args (fn_params fdef)))
      Σ_args R_args arg_roots ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    fn_env_unique_by_name env ->
    store_function_closure_targets_summary env s ->
    (forall y, In y (store_names s_args) -> In y seed) ->
    alpha_rename_fn_def seed fdef = (fcall, used') ->
    let ps_runtime := apply_type_params type_args (fn_params fcall) in
    store_typed_prefix env (bind_params ps_runtime vs s_args)
      (sctx_of_ctx (params_ctx ps_runtime)) /\
    store_roots_within (call_param_root_env ps_runtime arg_roots R_args)
      (bind_params ps_runtime vs s_args) /\
    store_no_shadow (bind_params ps_runtime vs s_args) /\
    root_env_no_shadow (call_param_root_env ps_runtime arg_roots R_args) /\
    root_env_covers_params ps_runtime
      (call_param_root_env ps_runtime arg_roots R_args) /\
    root_env_store_roots_named
      (call_param_root_env ps_runtime arg_roots R_args)
      (bind_params ps_runtime vs s_args) /\
    root_env_store_keys_named
      (call_param_root_env ps_runtime arg_roots R_args)
      (bind_params ps_runtime vs s_args) /\
    store_function_closure_targets_summary env
      (bind_params ps_runtime vs s_args) /\
    store_param_scope ps_runtime (bind_params ps_runtime vs s_args) s_args.
Proof.
  intros env Ω n R Σ args type_args sigma fdef fcall used' seed s s_args
    vs Σ_args R_args arg_roots Hsafe_args Heval_args Htyped_args Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Hunique Hsummary_store Hseed_names
    Hrename ps_runtime.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params sigma
                (apply_type_params type_args (fn_params fdef)))
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Htyped_args)
    as [_ [Hargs_values_fdef_lt [_ [_ [_ [_ Hrn_args]]]]]].
  assert (Hargs_values_fdef_type :
    eval_args_values_have_types env Ω s_args vs
      (apply_type_params type_args (fn_params fdef))).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_values_fdef_lt. }
  pose proof (alpha_rename_fn_def_shape seed fdef fcall used' Hrename)
    as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hnodup : NoDup (ctx_names (params_ctx ps_runtime))).
  { subst ps_runtime.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_nodup. exact Hrename. }
  assert (Hfresh : params_fresh_in_store ps_runtime s_args).
  { subst ps_runtime.
    unfold params_fresh_in_store.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    intros y Hy Hstore_y.
    pose proof (alpha_rename_fn_def_params_fresh_used
      seed fdef fcall used' Hrename) as Hfresh_seed.
    pose proof (Hfresh_seed y Hy) as Hnot_seed.
    apply Hnot_seed. apply Hseed_names. exact Hstore_y. }
  assert (Hargs_values_fcall_type :
    eval_args_values_have_types env Ω s_args vs ps_runtime).
  { subst ps_runtime.
    eapply eval_args_values_have_types_params_alpha.
    - apply params_alpha_apply_type_compat. exact Hparams_alpha.
    - exact Hargs_values_fdef_type. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params sigma
                (apply_type_params type_args (fn_params fdef)))
              Σ_args R_args arg_roots ps_runtime Heval_args Hprov_args
              Htyped_args Hroots Hshadow Hrn Hnodup Hfresh
              Hargs_values_fcall_type)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params sigma
                (apply_type_params type_args (fn_params fdef)))
              Σ_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
              Heval_args Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  repeat split.
  - eapply bind_params_store_typed_prefix; eassumption.
  - exact Hroots_bind.
  - exact Hshadow_bind.
  - exact Hrn_bind.
  - exact Hcover_bind.
  - eapply root_env_store_roots_named_call_param_bind_params; eassumption.
  - eapply root_env_store_keys_named_call_param_bind_params; eassumption.
  - eapply store_safe_function_value_call_args_bind_params_summary; eassumption.
  - eapply store_param_scope_bind_params. exact Hargs_values_fcall_type.
Qed.


Lemma generic_direct_call_args_bind_type_params_runtime_package :
  forall env Ω n R Σ args type_args sigma fdef fcall used'
      s s_args vs Σ_args R_args arg_roots,
    store_safe_function_value_call_args env args ->
    eval_args env s args s_args vs ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params sigma (apply_type_params type_args (fn_params fdef)))
      Σ_args R_args arg_roots ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    fn_env_unique_by_name env ->
    store_function_closure_targets_summary env s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    let ps_runtime := apply_type_params type_args (fn_params fcall) in
    store_typed_prefix env (bind_params ps_runtime vs s_args)
      (sctx_of_ctx (params_ctx ps_runtime)) /\
    store_roots_within (call_param_root_env ps_runtime arg_roots R_args)
      (bind_params ps_runtime vs s_args) /\
    store_no_shadow (bind_params ps_runtime vs s_args) /\
    root_env_no_shadow (call_param_root_env ps_runtime arg_roots R_args) /\
    root_env_covers_params ps_runtime
      (call_param_root_env ps_runtime arg_roots R_args) /\
    root_env_store_roots_named
      (call_param_root_env ps_runtime arg_roots R_args)
      (bind_params ps_runtime vs s_args) /\
    root_env_store_keys_named
      (call_param_root_env ps_runtime arg_roots R_args)
      (bind_params ps_runtime vs s_args) /\
    store_function_closure_targets_summary env
      (bind_params ps_runtime vs s_args) /\
    store_param_scope ps_runtime (bind_params ps_runtime vs s_args) s_args.
Proof.
  intros.
  eapply generic_direct_call_args_bind_type_params_runtime_package_seed;
    try eassumption.
  intros y Hy. exact Hy.
Qed.

Lemma value_update_path_function_closure_targets_summary :
  forall env v path v_new v',
    value_function_closure_targets_summary env v ->
    value_function_closure_targets_summary env v_new ->
    value_update_path v path v_new = Some v' ->
    value_function_closure_targets_summary env v'.
Proof.
  intros env v path v_new v' Hvalue Hnew Hupdate.
  revert v v' Hvalue Hupdate.
  induction path as [| f rest IH]; intros v v' Hvalue Hupdate.
  - destruct v; simpl in Hupdate; inversion Hupdate; subst; exact Hnew.
  - simpl in Hupdate.
    destruct v; try discriminate.
    remember ((fix update (fields : list (string * value))
      : option (list (string * value)) :=
      match fields with
      | [] => None
      | (name, fv) :: tail =>
          if String.eqb f name
          then match value_update_path fv rest v_new with
               | Some fv' => Some ((name, fv') :: tail)
               | None => None
               end
          else match update tail with
               | Some tail' => Some ((name, fv) :: tail')
               | None => None
               end
      end) l) as fields_opt eqn:Hfields.
    destruct fields_opt as [fields' |]; simpl in Hupdate;
      rewrite <- Hfields in Hupdate; inversion Hupdate; subst; simpl; auto.
Qed.

Lemma eval_lit_value_function_closure_targets_summary :
  forall env s lit s' v,
    eval env s (ELit lit) s' v ->
    value_function_closure_targets_summary env v.
Proof.
  intros env s lit s' v Heval.
  inversion Heval; subst; simpl; auto.
Qed.

Lemma store_function_closure_targets_summary_store_update_val_value :
  forall env s x v s',
    store_function_closure_targets_summary env s ->
    value_function_closure_targets_summary env v ->
    store_update_val x v s = Some s' ->
    store_function_closure_targets_summary env s'.
Proof.
  unfold store_function_closure_targets_summary.
  intros env s x v s' Hsummary Hvalue Hupdate.
  revert x v s' Hvalue Hupdate.
  induction Hsummary as [| se rest Hhead Htail IH];
    intros x v s' Hvalue Hupdate; simpl in Hupdate.
  - discriminate.
  - destruct (ident_eqb x (se_name se)) eqn:Heq.
    + inversion Hupdate; subst. constructor; [exact Hvalue | exact Htail].
    + destruct (store_update_val x v rest) as [rest' |] eqn:Hrest;
        try discriminate.
      inversion Hupdate; subst. constructor; [exact Hhead |].
      eapply IH; eassumption.
Qed.

Lemma store_function_closure_targets_summary_store_update_path_value :
  forall env s x path v s',
    store_function_closure_targets_summary env s ->
    value_function_closure_targets_summary env v ->
    store_update_path x path v s = Some s' ->
    store_function_closure_targets_summary env s'.
Proof.
  unfold store_function_closure_targets_summary.
  intros env s x path v s' Hsummary Hvalue Hupdate.
  revert x path v s' Hvalue Hupdate.
  induction Hsummary as [| se rest Hhead Htail IH];
    intros x path v s' Hvalue Hupdate; simpl in Hupdate.
  - discriminate.
  - destruct (ident_eqb x (se_name se)) eqn:Heq.
    + destruct (value_update_path (se_val se) path v) as [v' |] eqn:Hval;
        try discriminate.
      inversion Hupdate; subst. constructor.
      * eapply (value_update_path_function_closure_targets_summary
            env (se_val se) path v v'); eassumption.
      * exact Htail.
    + destruct (store_update_path x path v rest) as [rest' |] eqn:Hrest;
        try discriminate.
      inversion Hupdate; subst. constructor; [exact Hhead |].
      eapply IH; eassumption.
Qed.

Lemma store_safe_function_value_call_args_b_sound :
  forall env args,
    store_safe_function_value_call_args_b env args = true ->
    store_safe_function_value_call_args env args.
Proof.
  intros env args.
  induction args as [| arg rest IH]; intros Hcheck.
  - constructor.
  - destruct arg; simpl in Hcheck; try discriminate.
    + constructor.
      * apply SSFVCArg_Unit.
      * apply IH. exact Hcheck.
    + constructor.
      * apply SSFVCArg_Lit.
      * apply IH. exact Hcheck.
    + constructor.
      * apply SSFVCArg_Var.
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

Lemma store_safe_function_value_call_arg_subst_type_params_expr :
  forall env type_args arg,
    store_safe_function_value_call_arg env arg ->
    store_safe_function_value_call_arg env
      (subst_type_params_expr type_args arg).
Proof.
  intros env type_args arg Harg.
  destruct Harg as [| lit | x | fname fdef Hin Hname Hsummary]; simpl.
  - constructor.
  - constructor.
  - constructor.
  - eapply SSFVCArg_Fn; eassumption.
Qed.

Lemma store_safe_function_value_call_args_subst_type_params_expr :
  forall env type_args args,
    store_safe_function_value_call_args env args ->
    store_safe_function_value_call_args env
      (map (subst_type_params_expr type_args) args).
Proof.
  intros env type_args args Hargs.
  induction Hargs as [| arg rest Harg Hrest IH]; simpl.
  - constructor.
  - constructor.
    + eapply store_safe_function_value_call_arg_subst_type_params_expr.
      exact Harg.
    + exact IH.
Qed.

Lemma store_safe_function_value_call_arg_subst_type_params_expr_inv :
  forall env type_args arg,
    store_safe_function_value_call_arg env
      (subst_type_params_expr type_args arg) ->
    store_safe_function_value_call_arg env arg.
Proof.
  intros env type_args arg Harg.
  destruct arg; simpl in Harg; inversion Harg; subst; try constructor.
  eapply SSFVCArg_Fn; eauto.
Qed.

Lemma store_safe_function_value_call_args_subst_type_params_expr_inv :
  forall env type_args args,
    store_safe_function_value_call_args env
      (map (subst_type_params_expr type_args) args) ->
    store_safe_function_value_call_args env args.
Proof.
  intros env type_args args.
  induction args as [| arg rest IH]; intros Hargs; simpl in Hargs.
  - constructor.
  - inversion Hargs; subst.
    constructor.
    + eapply store_safe_function_value_call_arg_subst_type_params_expr_inv.
      exact H1.
    + apply IH. exact H2.
Qed.

Lemma store_safe_function_value_call_arg_alpha_rename_expr :
  forall env rho used arg ar used',
    store_safe_function_value_call_arg env arg ->
    alpha_rename_expr rho used arg = (ar, used') ->
    store_safe_function_value_call_arg env ar.
Proof.
  intros env rho used arg ar used' Harg Hrename.
  destruct Harg as [| lit | x | fname fdef Hin Hname Hsummary];
    simpl in Hrename; inversion Hrename; subst.
  - constructor.
  - constructor.
  - constructor.
  - eapply SSFVCArg_Fn; eauto.
Qed.

Lemma store_safe_function_value_call_args_alpha_rename_exprs :
  forall env rho used args argsr used',
    store_safe_function_value_call_args env args ->
    alpha_rename_exprs rho used args = (argsr, used') ->
    store_safe_function_value_call_args env argsr.
Proof.
  intros env rho used args.
  revert used.
  induction args as [| arg rest IH];
    intros used argsr used' Hargs Hrename; simpl in Hrename.
  - inversion Hrename; subst. constructor.
  - inversion Hargs; subst.
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct (alpha_rename_exprs rho used1 rest) as [restr used2]
      eqn:Hrest.
    inversion Hrename; subst.
    constructor.
    + eapply store_safe_function_value_call_arg_alpha_rename_expr;
        eassumption.
    + eapply IH; eassumption.
Qed.

Lemma store_safe_function_value_call_args_alpha_rename_call_go :
  forall env rho used args argsr used',
    store_safe_function_value_call_args env args ->
    ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr rho used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used args) = (argsr, used') ->
    store_safe_function_value_call_args env argsr.
Proof.
  intros env rho used args.
  revert used.
  induction args as [| arg rest IH];
    intros used argsr used' Hargs Hrename; simpl in Hrename.
  - inversion Hrename; subst. constructor.
  - inversion Hargs; subst.
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg0 :: rest0 =>
            let (arg', used2) := alpha_rename_expr rho used0 arg0 in
            let (rest', used3) := go used2 rest0 in
            (arg' :: rest', used3)
        end) used1 rest) as [restr used2] eqn:Hrest.
    inversion Hrename; subst.
    constructor.
    + eapply store_safe_function_value_call_arg_alpha_rename_expr;
        eassumption.
    + eapply IH; eassumption.
Qed.
