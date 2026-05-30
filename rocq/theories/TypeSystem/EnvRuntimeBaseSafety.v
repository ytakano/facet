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

Lemma root_env_store_roots_named_store_names_eq :
  forall R s s',
    store_names s' = store_names s ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  unfold root_env_store_roots_named.
  intros R s s' Hnames Hnamed x roots z Hlookup Hin.
  rewrite Hnames. eapply Hnamed; eassumption.
Qed.

Lemma root_set_store_roots_named_store_names_eq :
  forall roots s s',
    store_names s' = store_names s ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  unfold root_set_store_roots_named.
  intros roots s s' Hnames Hnamed z Hin.
  rewrite Hnames. eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_store_names_eq :
  forall R s s',
    store_names s' = store_names s ->
    root_env_store_keys_named R s ->
    root_env_store_keys_named R s'.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros R s s' Hnames Hkeys x Hin.
  rewrite Hnames. eapply Hkeys; eassumption.
Qed.

Lemma store_names_remove_keeps_other :
  forall s x z,
    In z (store_names s) ->
    z <> x ->
    In z (store_names (store_remove x s)).
Proof.
  induction s as [| se rest IH]; intros x z Hin Hneq; simpl in *.
  - contradiction.
  - destruct (ident_eqb x (se_name se)) eqn:Hx.
    + apply ident_eqb_eq in Hx. subst x.
      destruct Hin as [Heq | Hin].
      * subst z. contradiction.
      * exact Hin.
    + destruct Hin as [Heq | Hin].
      * left. exact Heq.
      * right. apply IH; assumption.
Qed.

Lemma root_env_store_keys_named_remove_env_store_remove :
  forall R s x,
    root_env_no_shadow R ->
    root_env_store_keys_named R s ->
    root_env_store_keys_named (root_env_remove x R) (store_remove x s).
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros R s x Hrn Hkeys y Hin.
  apply store_names_remove_keeps_other.
  - apply Hkeys. eapply root_env_names_remove_subset; eassumption.
  - intros Heq. subst y.
    eapply root_env_lookup_none_not_in_names.
    + apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
    + exact Hin.
Qed.

Lemma typed_env_roots_shadow_safe_evar_store_named :
  forall env Ω n R Σ x T Σ' R' roots s,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s /\
    root_env_store_keys_named R' s.
Proof.
  intros env Ω n R Σ x T Σ' R' roots s Htyped Hnamed Hkeys.
  dependent destruction Htyped; repeat split; try assumption;
    unfold root_set_store_roots_named;
    intros z Hin_z; eapply Hnamed; eassumption.
Qed.

Lemma store_safe_function_value_call_args_typed_roots_static_named :
  forall env Omega n R Sigma args ps Sigma' R' arg_roots,
    typed_args_roots env Omega n R Sigma args ps Sigma' R' arg_roots ->
    store_safe_function_value_call_args env args ->
    forall s,
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      R' = R /\
      Forall (fun roots => root_set_store_roots_named roots s) arg_roots /\
      root_env_store_roots_named R' s /\
      root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma args ps Sigma' R' arg_roots Htyped.
  induction Htyped; intros Hsafe s Hnamed Hkeys.
  - dependent destruction Hsafe.
    repeat split; try reflexivity; try constructor; assumption.
  - dependent destruction Hsafe.
    match goal with
    | Harg : store_safe_function_value_call_arg _ _ |- _ =>
        destruct Harg as [x | fname fdef Hin Hname Hsummary]
    end.
    + dependent destruction H.
      * destruct (IHHtyped Hsafe s Hnamed Hkeys)
          as [HR [Hroots_rest [Hnamed' Hkeys']]].
        subst R2.
        repeat split; try assumption.
        constructor.
        -- unfold root_set_store_roots_named.
           intros z Hin_z. eapply Hnamed; eassumption.
        -- exact Hroots_rest.
      * destruct (IHHtyped Hsafe s Hnamed Hkeys)
          as [HR [Hroots_rest [Hnamed' Hkeys']]].
        subst R2.
        repeat split; try assumption.
        constructor.
        -- unfold root_set_store_roots_named.
           intros z Hin_z. eapply Hnamed; eassumption.
        -- exact Hroots_rest.
    + dependent destruction H.
      destruct (IHHtyped Hsafe s Hnamed Hkeys)
        as [HR [Hroots_rest [Hnamed' Hkeys']]].
      subst R2.
      repeat split; try assumption.
      constructor.
      * unfold root_set_store_roots_named. intros z Hin_z. contradiction.
      * exact Hroots_rest.
Qed.

Lemma store_safe_function_value_call_args_typed_roots_store_named :
  forall env Omega n R Sigma args ps Sigma' R' arg_roots s s' vs,
    store_safe_function_value_call_args env args ->
    typed_args_roots env Omega n R Sigma args ps Sigma' R' arg_roots ->
    eval_args env s args s' vs ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    root_env_store_roots_named R' s' /\
    Forall (fun roots => root_set_store_roots_named roots s') arg_roots /\
    root_env_store_keys_named R' s'.
Proof.
  intros env Omega n R Sigma args ps Sigma' R' arg_roots s s' vs
    Hsafe Htyped Heval Hnamed Hkeys.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe) as Hready.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                env s args s' vs Heval Hready) as Hnames.
  destruct (store_safe_function_value_call_args_typed_roots_static_named
              env Omega n R Sigma args ps Sigma' R' arg_roots Htyped
              Hsafe s Hnamed Hkeys)
    as [HR [Hroots [Hnamed' Hkeys']]].
  subst R'.
  repeat split.
  - eapply root_env_store_roots_named_store_names_eq; eassumption.
  - eapply Forall_impl; [| exact Hroots].
    intros roots Hroot.
    eapply root_set_store_roots_named_store_names_eq; eassumption.
  - eapply root_env_store_keys_named_store_names_eq; eassumption.
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

Lemma store_safe_function_value_call_arg_eval_value_summary :
  forall env arg s s' v,
    fn_env_unique_by_name env ->
    store_safe_function_value_call_arg env arg ->
    store_function_closure_targets_summary env s ->
    eval env s arg s' v ->
    value_function_closure_targets_summary env v.
Proof.
  intros env arg s s' v Hunique Harg Hsummary Heval_arg.
  destruct Harg as [x | fname fdef Hin Hname Hcallee].
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

Lemma store_safe_function_value_call_arg_alpha_rename_expr :
  forall env rho used arg ar used',
    store_safe_function_value_call_arg env arg ->
    alpha_rename_expr rho used arg = (ar, used') ->
    store_safe_function_value_call_arg env ar.
Proof.
  intros env rho used arg ar used' Harg Hrename.
  destruct Harg as [x | fname fdef Hin Hname Hsummary];
    simpl in Hrename; inversion Hrename; subst.
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

Inductive expr_root_shadow_store_safe_narrow_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSSN_FunctionValueCall : forall R Σ x args T_callee Σ_callee
      R_callee roots_callee T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
        T_callee Σ_callee R_callee roots_callee ->
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
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSSN_LetInfer : forall R R1 R2 Σ Σ1 Sigma2 m x T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      non_function_value_ty_b T1 = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      sctx_check_ok env x T1 Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots.

Lemma disjoint_names_evar_of_call_expr :
  forall x args ys,
    disjoint_names (free_vars_expr (ECallExpr (EVar x) args)) ys ->
    disjoint_names (free_vars_expr (EVar x)) ys.
Proof.
  intros x args ys Hdisj y Hy.
  simpl in Hy. destruct Hy as [Hy | Hy]; [subst y | contradiction].
  apply Hdisj. simpl. left. reflexivity.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_function_value_call_intro :
  forall env Omega n rho Rr Sigmar x args er used used' T Sigma' R' roots
      T_callee_r Sigma_callee_r R_callee_r roots_callee_r,
    store_safe_function_value_call_args env args ->
    alpha_rename_expr rho used (ECallExpr (EVar x) args) = (er, used') ->
    typed_env_roots_shadow_safe env Omega n Rr Sigmar
      (EVar (lookup_rename x rho)) T_callee_r Sigma_callee_r
      R_callee_r roots_callee_r ->
    supported_non_type_generic_function_value_call_callee_shape T_callee_r ->
    typed_env_roots_shadow_safe env Omega n Rr Sigmar er T Sigma' R' roots ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T Sigma' R' roots roots.
Proof.
  intros env Omega n rho Rr Sigmar x args er used used' T Sigma' R' roots
    T_callee_r Sigma_callee_r R_callee_r roots_callee_r Hargs Hrename
    Hcallee Hshape Hcall.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) as [argsr used_args] eqn:Hargsr.
  inversion Hrename; subst er used'.
  eapply ERSSN_FunctionValueCall.
  - eapply store_safe_function_value_call_args_alpha_rename_call_go;
      eassumption.
  - exact Hcallee.
  - exact Hshape.
  - exact Hcall.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_intro :
  forall env Omega n rho Rr Sigmar m x xr T_hidden e1 e2 er used used'
      e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
      T2 Sigma2r R2r roots2r ret_roots,
    alpha_rename_expr rho used (ELet m x T_hidden e1 e2) = (er, used') ->
    alpha_rename_expr rho used e1 = (e1r, used1) ->
    xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
    used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
    alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar e1r T1 Sigma1r R1r roots1r ret_roots1r ->
    ty_compatible_b Omega T1 T_hidden = true ->
    non_function_value_ty_b T_hidden = true ->
    root_env_lookup xr R1r = None ->
    roots_exclude xr roots1r ->
    root_env_excludes xr R1r ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n (root_env_add xr roots1r R1r)
      (sctx_add xr T_hidden m Sigma1r) e2r T2 Sigma2r R2r
      roots2r ret_roots ->
    sctx_check_ok env xr T_hidden Sigma2r = true ->
    roots_exclude xr roots2r ->
    root_env_excludes xr (root_env_remove xr R2r) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T2
      (sctx_remove xr Sigma2r) (root_env_remove xr R2r) roots2r
      ret_roots.
Proof.
  intros env Omega n rho Rr Sigmar m x xr T_hidden e1 e2 er used used'
    e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
    T2 Sigma2r R2r roots2r ret_roots Hrename He1 Hxr Hused2 He2
    Hsummary1 Hcompat Hnonfun Hlookup Hexcl_roots1 Hexcl_env1
    Hsummary2 Hcheck Hexcl_roots2 Hexcl_env2.
  subst xr used2.
  simpl in Hrename.
  rewrite He1 in Hrename.
  rewrite He2 in Hrename.
  inversion Hrename; subst er used'.
  eapply ERSSN_Let; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_infer_intro :
  forall env Omega n rho Rr Sigmar m x xr e1 e2 er used used'
      e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
      T2 Sigma2r R2r roots2r ret_roots,
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    alpha_rename_expr rho used e1 = (e1r, used1) ->
    xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
    used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
    alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar e1r T1 Sigma1r R1r roots1r ret_roots1r ->
    non_function_value_ty_b T1 = true ->
    root_env_lookup xr R1r = None ->
    roots_exclude xr roots1r ->
    root_env_excludes xr R1r ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n (root_env_add xr roots1r R1r)
      (sctx_add xr T1 m Sigma1r) e2r T2 Sigma2r R2r roots2r
      ret_roots ->
    sctx_check_ok env xr T1 Sigma2r = true ->
    roots_exclude xr roots2r ->
    root_env_excludes xr (root_env_remove xr R2r) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T2
      (sctx_remove xr Sigma2r) (root_env_remove xr R2r) roots2r
      ret_roots.
Proof.
  intros env Omega n rho Rr Sigmar m x xr e1 e2 er used used'
    e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
    T2 Sigma2r R2r roots2r ret_roots Hrename He1 Hxr Hused2 He2
    Hsummary1 Hnonfun Hlookup Hexcl_roots1 Hexcl_env1 Hsummary2
    Hcheck Hexcl_roots2 Hexcl_env2.
  subst xr used2.
  simpl in Hrename.
  rewrite He1 in Hrename.
  rewrite He2 in Hrename.
  inversion Hrename; subst er used'.
  eapply ERSSN_LetInfer; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_init_support :
  forall rho R Rr roots rootsr Sigma Sigmar xr,
    ctx_alpha rho Sigma Sigmar ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_env_sctx_keys_named R Sigma ->
    root_env_sctx_roots_named R Sigma ->
    root_set_sctx_roots_named roots Sigma ->
    ~ In xr (ctx_names Sigmar) ->
    root_env_lookup xr Rr = None /\
    roots_exclude xr rootsr /\
    root_env_excludes xr Rr.
Proof.
  intros rho R Rr roots rootsr Sigma Sigmar xr Hctx Hrn Hrn_r HR
    Hroots Hkeys Hroot_names Hroot_set_names Hfresh.
  exact (root_env_sctx_support_fresh_renamed_let_init rho R Rr roots rootsr
    Sigma Sigmar xr Hctx Hrn Hrn_r HR Hroots Hkeys Hroot_names
    Hroot_set_names Hfresh).
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision :
  forall rho Sigma Sigma2 Sigmar R x xr T m,
    ctx_alpha rho Sigma Sigmar ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma2 ->
    sctx_same_bindings (sctx_add x T m Sigma) Sigma2 ->
    ~ In xr (ctx_names Sigmar) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R).
Proof.
  intros rho Sigma Sigma2 Sigmar R x xr T m Hctx Hrn Hkeys Hsame
    Hfresh Hnocoll.
  eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings;
    eassumption.
Qed.

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
  - eapply TERS_LetInfer; eauto.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision_from_summary :
  forall env Omega n rho Sigma1 Sigma2 Sigma1r R1 R2 roots1 roots2
      x xr T m e2 T2 ret_roots,
    ctx_alpha rho Sigma1 Sigma1r ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n (root_env_add x roots1 R1) (sctx_add x T m Sigma1)
      e2 T2 Sigma2 R2 roots2 ret_roots ->
    root_env_no_shadow (root_env_add x roots1 R1) ->
    root_env_sctx_keys_named (root_env_add x roots1 R1)
      (sctx_add x T m Sigma1) ->
    ~ In xr (ctx_names Sigma1r) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R2).
Proof.
  intros env Omega n rho Sigma1 Sigma2 Sigma1r R1 R2 roots1 roots2
    x xr T m e2 T2 ret_roots Hctx Hsummary Hns_add Hkeys_add
    Hfresh Hnocoll.
  pose proof (expr_root_shadow_store_safe_narrow_summary_typed
    env Omega n (root_env_add x roots1 R1) (sctx_add x T m Sigma1)
    e2 T2 Sigma2 R2 roots2 ret_roots Hsummary) as Htyped.
  assert (HnsR2 : root_env_no_shadow R2).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped.
    - exact Hns_add. }
  assert (HkeysR2 : root_env_sctx_keys_named R2 Sigma2).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (Hsame : sctx_same_bindings (sctx_add x T m Sigma1) Sigma2).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped. }
  eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision;
    eassumption.
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

Lemma expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx :
  forall env Omega n R Σ e T Σ' R' roots ret_roots s',
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_sctx_keys_named R Σ ->
    store_typed_prefix env s' Σ' ->
    root_env_no_shadow R' ->
    root_env_store_roots_named R' s' /\
    root_set_store_roots_named roots s' /\
    root_env_store_keys_named R' s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots s'
    Hsummary Hrn Hctx_roots Hctx_keys Hstore' Hrn'.
  pose proof (expr_root_shadow_store_safe_narrow_summary_typed
    env Omega n R Σ e T Σ' R' roots ret_roots Hsummary)
    as Htyped_shadow.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ e T Σ' R' roots Htyped_shadow)
    as Htyped_roots.
  destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
    R Σ e T Σ' R' roots Htyped_roots Hrn Hctx_roots)
    as [Hctx_roots' Hctx_set'].
  pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
    env Omega n) R Σ e T Σ' R' roots Htyped_shadow
    Hrn Hctx_keys) as Hctx_keys'.
  repeat split.
  - eapply root_env_ctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_set_ctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_env_ctx_keys_named_store_typed_prefix; eassumption.
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


Lemma typed_env_roots_shadow_safe_evar_core_eq_base :
  forall env Ω n R Σ x T1 Σ1 R1 roots1 T2 Σ2 R2 roots2,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x)
      T1 Σ1 R1 roots1 ->
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x)
      T2 Σ2 R2 roots2 ->
    ty_core T1 = ty_core T2.
Proof.
  intros env Ω n R Σ x T1 Σ1 R1 roots1 T2 Σ2 R2 roots2
    Htyped1 Htyped2.
  dependent destruction Htyped1; dependent destruction Htyped2;
    match goal with
    | Hplace1 : typed_place_env_structural _ _ (PVar _) _,
      Hplace2 : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace1; subst; inversion Hplace2; subst;
        match goal with
        | Hlookup1 : sctx_lookup ?x ?Σ = Some (?T1, _),
          Hlookup2 : sctx_lookup ?x ?Σ = Some (?T2, _) |- _ =>
            rewrite Hlookup1 in Hlookup2; inversion Hlookup2; subst;
            reflexivity
        end
    end.
Qed.

Lemma typed_env_roots_shadow_safe_evar_rename_no_collision_on_output_base :
  forall env Ω n rho R Σ x T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R').
Proof.
  intros env Ω n rho R Σ x T Σ' R' roots Htyped Hnocoll.
  dependent destruction Htyped; exact Hnocoll.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_roots_ret_equiv :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    root_set_equiv roots ret_roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - apply root_set_equiv_refl.
  - exact IHHsummary2.
  - exact IHHsummary2.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_ret_roots_exclude :
  forall env Omega n R Σ e T Σ' R' roots ret_roots x,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    roots_exclude x roots ->
    roots_exclude x ret_roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots x Hsummary Hexcl.
  eapply roots_exclude_equiv.
  - eapply expr_root_shadow_store_safe_narrow_summary_roots_ret_equiv.
    exact Hsummary.
  - exact Hexcl.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_tail_frame :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall R_tail,
      root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (R ++ R_tail) Σ e T Σ' (R' ++ R_tail)
        roots ret_roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros R_tail Hfresh; simpl in Hfresh.
  - eapply ERSSN_FunctionValueCall.
    + exact H.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H0.
      * unfold root_env_tail_fresh_names. intros y Hy. contradiction.
    + exact H1.
    + eapply typed_env_roots_shadow_safe_tail_frame; eassumption.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ Hfresh) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ Hfresh) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply ERSSN_Let.
    + apply IHHsummary1. exact Hfresh1.
    + exact H.
    + exact H0.
    + rewrite root_env_lookup_app_right by exact H1.
      exact Htail_lookup.
    + exact H2.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply IHHsummary2. exact Hfresh2.
    + exact H4.
    + exact H5.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ Hfresh) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ Hfresh) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply ERSSN_LetInfer.
    + apply IHHsummary1. exact Hfresh1.
    + exact H.
    + rewrite root_env_lookup_app_right by exact H0.
      exact Htail_lookup.
    + exact H1.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply IHHsummary2. exact Hfresh2.
    + exact H3.
    + exact H4.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall rho Rr Σr er used used',
      ctx_alpha rho Σ Σr ->
      root_env_no_shadow R ->
      root_env_no_shadow Rr ->
      root_env_equiv Rr (root_env_rename rho R) ->
      root_env_sctx_keys_named R Σ ->
      root_env_sctx_roots_named R Σ ->
      rename_no_collision_on rho (root_env_names R) ->
      rename_no_collision_on rho (root_env_names R') ->
      (forall x, In x (ctx_names Σr) -> In x used) ->
      (forall x, In x (rename_range rho) -> In x used) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used e = (er, used') ->
      exists Σr' Rr' rootsr ret_rootsr,
        expr_root_shadow_store_safe_narrow_summary
          env Omega n Rr Σr er T Σr' Rr' rootsr ret_rootsr /\
        ctx_alpha rho Σ' Σr' /\
        root_env_no_shadow Rr' /\
        root_env_equiv Rr' (root_env_rename rho R') /\
        root_set_equiv rootsr (root_set_rename rho roots) /\
        root_set_equiv ret_rootsr (root_set_rename rho ret_roots).
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary as
    [ R Σ x args T_callee Σ_callee R_callee roots_callee T Σ' R' roots
      Hargs Hcallee Hshape Hcall
    | R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2 T2 roots1 roots2
      ret_roots1 ret_roots Hsummary1 IH1 Hcompat Hnonfun Hlookup
      Hexcl_roots1 Hexcl_env1 Hsummary2 IH2 Hcheck Hexcl_roots2
      Hexcl_env2
    | R R1 R2 Σ Σ1 Sigma2 m x T1 e1 e2 T2 roots1 roots2
      ret_roots1 ret_roots Hsummary1 IH1 Hnonfun Hlookup
      Hexcl_roots1 Hexcl_env1 Hsummary2 IH2 Hcheck Hexcl_roots2
      Hexcl_env2 ];
    intros rho Rr0 Σr0 er used used' Hctx HnsR HnsRr HRr Hkeys
      Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega n rho R Rr0 Σ Σr0 (ECallExpr (EVar x) args) er used
      used' T Σ' R' roots Hcall Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σcall_r & Rcall_r & roots_r & Hcall_r & Hctx_r &
        HnsR_r & HR_r & Hroots_r).
    assert (Hnocoll_callee :
      rename_no_collision_on rho (root_env_names R_callee)).
    { eapply typed_env_roots_shadow_safe_evar_rename_no_collision_on_output_base;
        eassumption. }
    destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega n rho R Rr0 Σ Σr0 (EVar x)
      (EVar (lookup_rename x rho)) used used T_callee Σ_callee
      R_callee roots_callee Hcallee Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR Hnocoll_callee Hctx_used Hrange_used
      (disjoint_names_evar_of_call_expr x args (rename_range rho) Hdisj)
      eq_refl)
      as (Σcallee_r & Rcallee_r & roots_callee_r & Hcallee_r & _).
    exists Σcall_r, Rcall_r, roots_r, roots_r.
    split.
    + eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_function_value_call_intro;
        eassumption.
    + split; [exact Hctx_r |].
      split; [exact HnsR_r |].
      split; [exact HR_r |].
      split; [exact Hroots_r | exact Hroots_r].
  - simpl in Hrename.
    destruct (disjoint_names_cons_l x
      (free_vars_expr e1 ++ free_vars_expr e2) (rename_range rho) Hdisj)
      as [Hsafe_x Hdisj_tail].
    destruct (disjoint_names_app_l (free_vars_expr e1)
      (free_vars_expr e2) (rename_range rho) Hdisj_tail)
      as [Hdisj1 Hdisj2].
    destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
    set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
    assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1))
      by reflexivity.
    set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
    assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1)
      by reflexivity.
    destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
      as [e2r used3] eqn:He2.
    assert (Htyped1 :
      typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1).
    assert (Htyped2 :
      typed_env_roots_shadow_safe env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary2).
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped1.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [Hroots_env1 _]; eauto. }
    assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [_ Hroots_set1]; eauto. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply typed_env_roots_let_body_no_collision_from_removed.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hlookup.
      - exact HnocollR'. }
    destruct (IH1 rho Rr0 Σr0 e1r used used1 Hctx HnsR HnsRr HRr
      Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used Hdisj1 He1)
      as (Σ1r & R1r & roots1r & ret_roots1r & Hsummary1r &
        Hctx1r & HnsR1r & HR1r & Hroots1r & _).
    assert (Htyped1r :
      typed_env_roots_shadow_safe env Omega n Rr0 Σr0 e1r T1 Σ1r R1r
        roots1r)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1r).
    assert (Hctx_used1 : forall y, In y (ctx_names Σ1r) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σ1r).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σ1r)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_init_support
      rho R1 R1r roots1 roots1r Σ1 Σ1r xr Hctx1r HnsR1 HnsR1r
      HR1r Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
      as [Hlookup_xr [Hexcl_roots1r Hexcl_env1r]].
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T_hidden m Σ1) (sctx_add xr T_hidden m Σ1r)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hns_add :
      root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hns_add_r :
      root_env_no_shadow (root_env_add xr roots1r R1r))
      by (apply root_env_no_shadow_add; assumption).
    assert (HRadd :
      root_env_equiv (root_env_add xr roots1r R1r)
        (root_env_rename ((x, xr) :: rho)
          (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
    assert (Hroots_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    assert (Hnocoll_add :
      rename_no_collision_on ((x, xr) :: rho)
        (root_env_names (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_no_collision_on;
        eassumption. }
    assert (HnocollR2_cons :
      rename_no_collision_on ((x, xr) :: rho) (root_env_names R2)).
    { eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision_from_summary;
        eassumption. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T_hidden m Σ1r)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (IH2 ((x, xr) :: rho) (root_env_add xr roots1r R1r)
      (sctx_add xr T_hidden m Σ1r) e2r used2 used3 Hctx_body
      Hns_add Hns_add_r HRadd Hkeys_add Hroots_add Hnocoll_add
      HnocollR2_cons Hctx_used2 Hrange_used2
      (alpha_rename_let_body_disjoint_forward rho used1 x xr e2 Hxr Hdisj2)
      He2)
      as (Σ2r & R2r & roots2r & ret_roots2r & Hsummary2r &
        Hctx2r & HnsR2r & HR2r_cons & Hroots2r_cons & Hret2r_cons).
    assert (HnsR2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hns_add. }
    assert (HkeysR2 : root_env_sctx_keys_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR2 : root_env_sctx_roots_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2)
        as [Hroots_env2 _]; eauto. }
    assert (Hroots2_named : root_set_sctx_roots_named roots2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2)
        as [_ Hroots_set2]; eauto. }
    assert (Hsame_body :
      sctx_same_bindings (sctx_add x T_hidden m Σ1) Sigma2).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
    assert (Hnocoll_x :
      rename_no_collision_for ((x, xr) :: rho) x (root_env_names R2)).
    { eapply root_env_sctx_keys_named_added_no_collision_for_head.
      - exact Hctx1r.
      - eapply root_env_sctx_keys_named_same_bindings.
        + apply sctx_same_bindings_sym. exact Hsame_body.
        + exact HkeysR2.
      - exact Hfresh_ctx. }
    assert (HRremove :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename rho (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_equiv;
        eassumption. }
    assert (Hroots2r :
      root_set_equiv roots2r (root_set_rename rho roots2)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hret_roots_excl : roots_exclude x ret_roots).
    { eapply expr_root_shadow_store_safe_narrow_summary_ret_roots_exclude;
        eassumption. }
    assert (Hret2r :
      root_set_equiv ret_roots2r (root_set_rename rho ret_roots)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hroots2r_excl : roots_exclude xr roots2r).
    { eapply roots_exclude_shadow_safe_rename_body.
      - exact Hctx1r.
      - eapply root_set_sctx_roots_named_strip_added_same_bindings.
        + exact Hexcl_roots2.
        + exact Hroots2_named.
        + exact Hsame_body.
      - exact Hfresh_ctx.
      - exact Hroots2r_cons.
      - exact Hexcl_roots2. }
    assert (Hremove_ext :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename ((x, xr) :: rho) (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
        eassumption. }
    assert (Henv2r_excl :
      root_env_excludes xr (root_env_remove xr R2r)).
    { eapply root_env_excludes_shadow_safe_rename_body.
      - exact Hctx1r.
      - apply root_env_no_shadow_remove. exact HnsR2.
      - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
          eassumption.
      - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
          eassumption.
      - exact Hfresh_ctx.
      - exact Hremove_ext.
      - exact Hexcl_env2. }
    change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
      in Hrename.
    change (xr :: x :: free_vars_expr e2 ++ used1) with used2
      in Hrename.
    rewrite He2 in Hrename.
    injection Hrename as <- <-.
    exists (sctx_remove xr Σ2r), (root_env_remove xr R2r), roots2r,
      ret_roots2r.
    split.
    + eapply ERSSN_Let.
      * exact Hsummary1r.
      * exact Hcompat.
      * exact Hnonfun.
      * exact Hlookup_xr.
      * exact Hexcl_roots1r.
      * exact Hexcl_env1r.
      * exact Hsummary2r.
      * assert (Hlookup_xr_rename :
          lookup_rename x ((x, xr) :: rho) = xr)
          by (simpl; rewrite ident_eqb_refl; reflexivity).
        rewrite <- Hlookup_xr_rename.
        eapply ctx_alpha_check_ok_forward.
        -- exact Hctx2r.
        -- eapply alpha_rename_let_bound_safe_forward; eassumption.
        -- exact Hcheck.
      * exact Hroots2r_excl.
      * exact Henv2r_excl.
    + split.
      * eapply ctx_alpha_remove_bound. exact Hctx2r.
      * split.
        -- apply root_env_no_shadow_remove. exact HnsR2r.
        -- split.
           ++ exact HRremove.
           ++ split; [exact Hroots2r | exact Hret2r].
  - simpl in Hrename.
    destruct (disjoint_names_cons_l x
      (free_vars_expr e1 ++ free_vars_expr e2) (rename_range rho) Hdisj)
      as [Hsafe_x Hdisj_tail].
    destruct (disjoint_names_app_l (free_vars_expr e1)
      (free_vars_expr e2) (rename_range rho) Hdisj_tail)
      as [Hdisj1 Hdisj2].
    destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
    set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
    assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1))
      by reflexivity.
    set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
    assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1)
      by reflexivity.
    destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
      as [e2r used3] eqn:He2.
    assert (Htyped1 :
      typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1).
    assert (Htyped2 :
      typed_env_roots_shadow_safe env Omega n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary2).
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped1.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [Hroots_env1 _]; eauto. }
    assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [_ Hroots_set1]; eauto. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply typed_env_roots_let_body_no_collision_from_removed.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hlookup.
      - exact HnocollR'. }
    destruct (IH1 rho Rr0 Σr0 e1r used used1 Hctx HnsR HnsRr HRr
      Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used Hdisj1 He1)
      as (Σ1r & R1r & roots1r & ret_roots1r & Hsummary1r &
        Hctx1r & HnsR1r & HR1r & Hroots1r & _).
    assert (Htyped1r :
      typed_env_roots_shadow_safe env Omega n Rr0 Σr0 e1r T1 Σ1r R1r
        roots1r)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1r).
    assert (Hctx_used1 : forall y, In y (ctx_names Σ1r) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σ1r).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σ1r)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_init_support
      rho R1 R1r roots1 roots1r Σ1 Σ1r xr Hctx1r HnsR1 HnsR1r
      HR1r Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
      as [Hlookup_xr [Hexcl_roots1r Hexcl_env1r]].
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hns_add :
      root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hns_add_r :
      root_env_no_shadow (root_env_add xr roots1r R1r))
      by (apply root_env_no_shadow_add; assumption).
    assert (HRadd :
      root_env_equiv (root_env_add xr roots1r R1r)
        (root_env_rename ((x, xr) :: rho)
          (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
    assert (Hroots_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    assert (Hnocoll_add :
      rename_no_collision_on ((x, xr) :: rho)
        (root_env_names (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_no_collision_on;
        eassumption. }
    assert (HnocollR2_cons :
      rename_no_collision_on ((x, xr) :: rho) (root_env_names R2)).
    { eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision_from_summary;
        eassumption. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σ1r)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (IH2 ((x, xr) :: rho) (root_env_add xr roots1r R1r)
      (sctx_add xr T1 m Σ1r) e2r used2 used3 Hctx_body
      Hns_add Hns_add_r HRadd Hkeys_add Hroots_add Hnocoll_add
      HnocollR2_cons Hctx_used2 Hrange_used2
      (alpha_rename_let_body_disjoint_forward rho used1 x xr e2 Hxr Hdisj2)
      He2)
      as (Σ2r & R2r & roots2r & ret_roots2r & Hsummary2r &
        Hctx2r & HnsR2r & HR2r_cons & Hroots2r_cons & Hret2r_cons).
    assert (HnsR2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hns_add. }
    assert (HkeysR2 : root_env_sctx_keys_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR2 : root_env_sctx_roots_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2)
        as [Hroots_env2 _]; eauto. }
    assert (Hroots2_named : root_set_sctx_roots_named roots2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2)
        as [_ Hroots_set2]; eauto. }
    assert (Hsame_body :
      sctx_same_bindings (sctx_add x T1 m Σ1) Sigma2).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
    assert (Hnocoll_x :
      rename_no_collision_for ((x, xr) :: rho) x (root_env_names R2)).
    { eapply root_env_sctx_keys_named_added_no_collision_for_head.
      - exact Hctx1r.
      - eapply root_env_sctx_keys_named_same_bindings.
        + apply sctx_same_bindings_sym. exact Hsame_body.
        + exact HkeysR2.
      - exact Hfresh_ctx. }
    assert (HRremove :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename rho (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_equiv;
        eassumption. }
    assert (Hroots2r :
      root_set_equiv roots2r (root_set_rename rho roots2)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hret_roots_excl : roots_exclude x ret_roots).
    { eapply expr_root_shadow_store_safe_narrow_summary_ret_roots_exclude;
        eassumption. }
    assert (Hret2r :
      root_set_equiv ret_roots2r (root_set_rename rho ret_roots)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hroots2r_excl : roots_exclude xr roots2r).
    { eapply roots_exclude_shadow_safe_rename_body.
      - exact Hctx1r.
      - eapply root_set_sctx_roots_named_strip_added_same_bindings.
        + exact Hexcl_roots2.
        + exact Hroots2_named.
        + exact Hsame_body.
      - exact Hfresh_ctx.
      - exact Hroots2r_cons.
      - exact Hexcl_roots2. }
    assert (Hremove_ext :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename ((x, xr) :: rho) (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
        eassumption. }
    assert (Henv2r_excl :
      root_env_excludes xr (root_env_remove xr R2r)).
    { eapply root_env_excludes_shadow_safe_rename_body.
      - exact Hctx1r.
      - apply root_env_no_shadow_remove. exact HnsR2.
      - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
          eassumption.
      - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
          eassumption.
      - exact Hfresh_ctx.
      - exact Hremove_ext.
      - exact Hexcl_env2. }
    change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
      in Hrename.
    change (xr :: x :: free_vars_expr e2 ++ used1) with used2
      in Hrename.
    rewrite He2 in Hrename.
    injection Hrename as <- <-.
    exists (sctx_remove xr Σ2r), (root_env_remove xr R2r), roots2r,
      ret_roots2r.
    split.
    + eapply ERSSN_LetInfer.
      * exact Hsummary1r.
      * exact Hnonfun.
      * exact Hlookup_xr.
      * exact Hexcl_roots1r.
      * exact Hexcl_env1r.
      * exact Hsummary2r.
      * assert (Hlookup_xr_rename :
          lookup_rename x ((x, xr) :: rho) = xr)
          by (simpl; rewrite ident_eqb_refl; reflexivity).
        rewrite <- Hlookup_xr_rename.
        eapply ctx_alpha_check_ok_forward.
        -- exact Hctx2r.
        -- eapply alpha_rename_let_bound_safe_forward; eassumption.
        -- exact Hcheck.
      * exact Hroots2r_excl.
      * exact Henv2r_excl.
    + split.
      * eapply ctx_alpha_remove_bound. exact Hctx2r.
      * split.
        -- apply root_env_no_shadow_remove. exact HnsR2r.
        -- split.
           ++ exact HRremove.
           ++ split; [exact Hroots2r | exact Hret2r].
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_instantiate_fresh :
  forall env Omega n rho R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0 ret_roots0,
        expr_root_shadow_store_safe_narrow_summary
          env Omega n R0 Σ e T Σ' R0' roots0 ret_roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Omega n rho R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros Hfresh R0 HnsR HnsR0 HR0.
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (ECallExpr (EVar x) args) T Σ' R' roots
      R0 H2 Hfresh HnsR HnsR0 HR0)
      as (Rcall0 & roots0 & Htyped_call0 & Hns_call0 & HR_call0 & Hroots0).
    destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EVar x) T_callee Σ_callee R_callee
      roots_callee R0 H0 (root_subst_images_exclude_names_nil rho) HnsR HnsR0 HR0)
      as (Rcallee0 & roots_callee0 & Htyped_callee0 & _ & _ & _).
    exists Rcall0, roots0, roots0. split.
    + eapply ERSSN_FunctionValueCall.
      * exact H.
      * exact Htyped_callee0.
      * exact H1.
      * exact Htyped_call0.
    + split; [exact Hns_call0 |].
      split; [exact HR_call0 |].
      exact Hroots0.
  - destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHHsummary1 Hfresh1 R0 HnsR HnsR0 HR0)
      as (R10 & roots10 & ret_roots10 & Hsummary10 & HnsR10 & HR10 & Hroots10).
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None)
      by (apply root_env_lookup_instantiate_none; exact H1).
    assert (Hlookup_R10_none : root_env_lookup x R10 = None)
      by (eapply root_env_equiv_lookup_none_r; eassumption).
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10))
      by (apply root_env_no_shadow_add; assumption).
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHHsummary2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 H1)
      Hns_add Heq_add)
      as (R20 & roots20 & ret_roots20 & Hsummary20 & HnsR20 & HR20 & Hroots20).
    exists (root_env_remove x R20), roots20, ret_roots20. split.
    + eapply ERSSN_Let.
      * exact Hsummary10.
      * exact H.
      * exact H0.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact Hsummary20.
      * exact H4.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + split.
      * apply root_env_no_shadow_remove. exact HnsR20.
      * split.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_remove.
              ** exact HnsR20.
              ** apply root_env_instantiate_no_shadow. exact Hns_R2.
              ** exact HR20.
           ++ apply root_env_equiv_sym.
              apply root_env_instantiate_remove_equiv.
              ** exact Hns_R2.
              ** exact Hns_R2.
              ** apply root_env_equiv_refl.
        -- exact Hroots20.
  - destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHHsummary1 Hfresh1 R0 HnsR HnsR0 HR0)
      as (R10 & roots10 & ret_roots10 & Hsummary10 & HnsR10 & HR10 & Hroots10).
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None)
      by (apply root_env_lookup_instantiate_none; exact H0).
    assert (Hlookup_R10_none : root_env_lookup x R10 = None)
      by (eapply root_env_equiv_lookup_none_r; eassumption).
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10))
      by (apply root_env_no_shadow_add; assumption).
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHHsummary2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 H0)
      Hns_add Heq_add)
      as (R20 & roots20 & ret_roots20 & Hsummary20 & HnsR20 & HR20 & Hroots20).
    exists (root_env_remove x R20), roots20, ret_roots20. split.
    + eapply ERSSN_LetInfer.
      * exact Hsummary10.
      * exact H.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact Hsummary20.
      * exact H3.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + split.
      * apply root_env_no_shadow_remove. exact HnsR20.
      * split.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_remove.
              ** exact HnsR20.
              ** apply root_env_instantiate_no_shadow. exact Hns_R2.
              ** exact HR20.
           ++ apply root_env_equiv_sym.
              apply root_env_instantiate_remove_equiv.
              ** exact Hns_R2.
              ** exact Hns_R2.
              ** apply root_env_equiv_refl.
        -- exact Hroots20.
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
      destruct Hcheck as [[[Hsctx_ok Hroots2] Henv2] Hbody_check].
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
    + simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (non_function_value_ty_b T1) eqn:Hnonfn;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i T1 m Σ1) e2)
        as [[[[T2 Sigma2] R2] roots2] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[Hsctx_ok Hroots2] Henv2] Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i T1 m Σ1) e2 T2 Sigma2 R2 roots2 Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_ok, Hroots2, Henv2 in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSSN_LetInfer.
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
      pose proof (infer_core_env_roots_shadow_safe_sound
        env Omega n R (ctx_of_sctx Σ) (EVar x) T_callee Gamma_callee
        R_callee roots_callee Hinfer_callee) as Htyped_callee.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (ECallExpr (EVar x) l) T Σ' R'
        roots Hinfer) as Htyped_call.
      exists roots.
      eapply ERSSN_FunctionValueCall.
      * apply store_safe_function_value_call_args_b_sound. exact Hready_args.
      * exact Htyped_callee.
      * exact Hcallee_shape.
      * exact Htyped_call.
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

Lemma expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary :
  forall env Omega n R Σ x args T_callee Σ_callee R_callee roots_callee T Σ' R' roots,
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      T_callee Σ_callee R_callee roots_callee ->
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
  intros env Omega n R Σ x args T_callee Σ_callee R_callee roots_callee T Σ' R' roots Hargs Htyped_callee_summary Hcallee_shape Htyped
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
  - pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
      env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
      (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee0
      Htyped_callee_summary Htyped) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape];
      rewrite Hcore in Hshape; simpl in Hshape; discriminate.
  - match goal with
    | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
        ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          T_typed Σ_typed R_typed roots_typed
          Htyped_callee_summary Htyped_callee) as Hcore;
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
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          T_typed Σ_typed R_typed roots_typed
          Htyped_callee_summary Htyped_callee) as Hcore;
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
  - pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
      env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
      (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
      Htyped_callee_summary Htyped) as Hcore.
    destruct Hcallee_shape as
      [Tshape params_shape ret_shape Hshape
      | Tshape m_shape bounds_shape body_shape params_shape ret_shape
          Hshape Hbody_shape].
    + rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + rewrite Hcore in Hshape; simpl in Hshape.
      inversion Hshape; subst.
      simpl in Hbody_shape. rewrite H0 in Hbody_shape. discriminate.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package :
  forall env Omega n R Σ x args u param_tys ret_ty Σ1 R1
      roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Σ1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys param_tys) Σ' R' arg_roots ->
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
      store_typed env s' Σ' /\
      value_has_type env s' ret ret_ty /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u param_tys ret_ty Σ1 R1
    roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TFn param_tys ret_ty))).
  { eapply SFV_TFn. reflexivity. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  pose proof
    (expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary
      env Omega n R Σ x args (MkTy u (TFn param_tys ret_ty)) Σ1 R1
      roots_callee_typed ret_ty Σ' R'
      (root_set_union roots_callee_typed (root_sets_union arg_roots))
      Hargs Htyped_callee Hcallee_shape Htyped_call
      s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call
      Hunique) as Hsummary'.
  inversion Heval_call; subst; clear Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ (EVar x) (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [_ [Hv_callee _]].
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  destruct (eval_call_expr_tfn_components_preserve_typing_with_callee_summary
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall
    vs ret used' Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped_callee Htyped_args Hunique)
    as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  { eapply eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary.
    - exact Hsummary.
    - exact Heval_callee.
    - exact Hlookup. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed
    env Omega n R Σ (ECallExpr (EVar x) args) ret_ty Σ' R'
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    s (store_remove_params (fn_captures fcall)
         (store_remove_params (fn_params fcall) s_body))
    Hnarrow Hstore Hrn Hnamed Hkeys Hstore' Hrn')
    as [Hnamed' [Hrootset_named Hkeys']].
  repeat split; eassumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package :
  forall env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
      Σ1 R1 roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty σ ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives σ bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
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
      store_typed env s' Σ' /\
      value_has_type env s' ret (open_bound_ty σ ret_ty) /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
    Σ1 R1 roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Hbody_shape
    Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call
    Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Forall_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Hbody_shape.
    - exact Hret_closed.
    - exact Hbounds_closed.
    - exact Hbounds.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TForall m bounds body_ty))).
  { eapply SFV_TForall_TFn.
    - reflexivity.
    - exact Hbody_shape. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  pose proof
    (expr_root_shadow_store_safe_narrow_function_call_preserves_store_function_closure_targets_summary
      env Omega n R Σ x args (MkTy u (TForall m bounds body_ty)) Σ1 R1
      roots_callee_typed (open_bound_ty σ ret_ty) Σ' R'
      (root_set_union roots_callee_typed (root_sets_union arg_roots))
      Hargs Htyped_callee Hcallee_shape Htyped_call
      s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call
      Hunique) as Hsummary'.
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (proj1 eval_preserves_root_names_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Hnamed Htyped_callee_roots) as [Hnamed_fn _].
  pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Hkeys Htyped_callee_roots) as Hkeys_fn.
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  destruct (value_has_type_empty_closure_tforall_tfn_components
    env s_fn fname fdef u m bounds body_ty param_tys ret_ty σ
    Hv_callee Hlookup Hunique Hbody_shape) as [Htype_params [Hcaps_fdef Hbridge]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Σ1 args
    (params_of_tys (map (open_bound_ty σ) param_tys))
    Σ' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset
      env Omega n R1 Σ1 Σ' R' arg_roots args fdef fcall
      (map (open_bound_ty σ) param_tys) (open_bound_ty σ ret_ty)
      s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  destruct (eval_evar_call_expr_lifetime_forall_tfn_components_preserve_typing_with_callee_summary_route
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty σ
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route)
    as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed
    env Omega n R Σ (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    s (store_remove_params (fn_captures fcall)
         (store_remove_params (fn_params fcall) s_body))
    Hnarrow Hstore Hrn Hnamed Hkeys Hstore' Hrn')
    as [Hnamed' [Hrootset_named Hkeys']].
  repeat split; eassumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_runtime_package :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
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
      store_typed env s' Σ' /\
      value_has_type env s' ret T /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Heval Hunique.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package;
        eassumption.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]].
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_roots_named_add_env_store_add; eassumption).
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H6.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hsummary_let :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ELet m x T_hidden e1 e2) T2 (sctx_remove x Sigma2)
        (root_env_remove x R2) roots2 ret_roots).
    { eapply ERSSN_Let; eassumption. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed
      env Omega n R Σ (ELet m x T_hidden e1 e2) T2
      (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
      s (store_remove x s2) Hsummary_let Hstore Hrn Hnamed Hkeys
      Hstore_final Hrn_final) as [Hnamed_final [Hrootset_final Hkeys_final]].
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hv2.
      * eapply value_roots_exclude_root; eassumption.
    + exact Hroots_removed.
    + exact Hvalue_roots.
    + exact Hrootset_final.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
Qed.

Definition callee_body_root_shadow_store_safe_narrow_summary
    (env : global_env) (fdef : fn_def) : Prop :=
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

Lemma store_safe_function_value_call_arg_global_env_with_local_bounds :
  forall env bounds arg,
    store_safe_function_value_call_arg env arg ->
    store_safe_function_value_call_arg
      (global_env_with_local_bounds env bounds) arg.
Proof.
  intros env bounds arg Harg.
  destruct Harg as [x | fname fdef Hin Hname Hsummary].
  - constructor.
  - eapply SSFVCArg_Fn.
    + exact Hin.
    + exact Hname.
    + apply callee_body_root_shadow_provenance_summary_global_env_with_local_bounds.
      exact Hsummary.
Qed.

Lemma store_safe_function_value_call_args_global_env_with_local_bounds :
  forall env bounds args,
    store_safe_function_value_call_args env args ->
    store_safe_function_value_call_args
      (global_env_with_local_bounds env bounds) args.
Proof.
  intros env bounds args Hargs.
  induction Hargs.
  - constructor.
  - constructor.
    + eapply store_safe_function_value_call_arg_global_env_with_local_bounds.
      exact H.
    + exact IHHargs.
Qed.

Lemma typed_place_env_structural_pvar_global_env_with_local_bounds :
  forall env bounds Sigma x T,
    typed_place_env_structural env Sigma (PVar x) T ->
    typed_place_env_structural
      (global_env_with_local_bounds env bounds) Sigma (PVar x) T.
Proof.
  intros env bounds Sigma x T Hplace.
  inversion Hplace; subst.
  eapply TPES_Var; eassumption.
Qed.

Lemma typed_env_roots_shadow_safe_evar_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma x T Sigma' R' roots,
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (EVar x) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma x T Sigma' R' roots Htyped.
  dependent destruction Htyped.
  - eapply TERS_Var_Copy.
    + match goal with
      | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
          eapply typed_place_env_structural_pvar_global_env_with_local_bounds;
          exact Hplace
      end.
    + assumption.
    + assumption.
  - eapply TERS_Var_Move.
    + match goal with
      | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
          eapply typed_place_env_structural_pvar_global_env_with_local_bounds;
          exact Hplace
      end.
    + assumption.
    + assumption.
    + assumption.
Qed.

Lemma typed_env_roots_shadow_safe_efn_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma fname T Sigma' R' roots,
    typed_env_roots_shadow_safe env Omega n R Sigma (EFn fname) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (EFn fname) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma fname T Sigma' R' roots Htyped.
  dependent destruction Htyped.
  change (env_fns (global_env_with_local_bounds env bounds)) with (env_fns env).
  eapply TERS_Fn.
  - match goal with
    | Hin : In _ (env_fns env) |- _ => exact Hin
    end.
  - reflexivity.
  - match goal with
    | Hcaps : fn_captures _ = [] |- _ => exact Hcaps
    end.
Qed.

Lemma typed_env_roots_shadow_safe_store_safe_arg_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma arg T Sigma' R' roots,
    store_safe_function_value_call_arg env arg ->
    typed_env_roots_shadow_safe env Omega n R Sigma arg T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      arg T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma arg T Sigma' R' roots Hsafe Htyped.
  inversion Hsafe; subst.
  - eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds.
    exact Htyped.
  - eapply typed_env_roots_shadow_safe_efn_global_env_with_local_bounds.
    exact Htyped.
Qed.

Lemma typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma args ps Sigma' R' roots,
    store_safe_function_value_call_args env args ->
    typed_args_roots_shadow_safe env Omega n R Sigma args ps Sigma' R' roots ->
    typed_args_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      args ps Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma args ps Sigma' R' roots Hsafe Htyped.
  revert bounds Hsafe.
  induction Htyped; intros bounds Hsafe.
  - constructor.
  - inversion Hsafe; subst.
    eapply TERSArgs_Cons.
    + eapply typed_env_roots_shadow_safe_store_safe_arg_global_env_with_local_bounds;
        eassumption.
    + exact H0.
    + apply IHHtyped. exact H4.
Qed.

Lemma typed_env_roots_shadow_safe_evar_ty_eq :
  forall env Omega n R Sigma x T1 Sigma1 R1 roots1 T2 Sigma2 R2 roots2,
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x) T1 Sigma1 R1 roots1 ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x) T2 Sigma2 R2 roots2 ->
    T1 = T2.
Proof.
  intros env Omega n R Sigma x T1 Sigma1 R1 roots1 T2 Sigma2 R2 roots2 H1 H2.
  inversion H1; subst; inversion H2; subst;
    match goal with
    | Hplace1 : typed_place_env_structural _ _ (PVar _) _,
      Hplace2 : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace1; subst; inversion Hplace2; subst;
        match goal with
        | Hlookup1 : sctx_lookup _ _ = Some (_, _),
          Hlookup2 : sctx_lookup _ _ = Some (_, _) |- _ =>
            rewrite Hlookup1 in Hlookup2; inversion Hlookup2; reflexivity
        end
    end.
Qed.

Lemma typed_env_roots_shadow_safe_evar_call_store_safe_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma x args T_callee Sigma_callee R_callee
      roots_callee T Sigma' R' roots,
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      T_callee Sigma_callee R_callee roots_callee ->
    supported_non_type_generic_function_value_call_callee_shape T_callee ->
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ECallExpr (EVar x) args) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (ECallExpr (EVar x) args) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma x args T_callee Sigma_callee R_callee
    roots_callee T Sigma' R' roots Hsafe Hcallee Hshape Hcall.
  dependent destruction Hcall.
  - eapply TERS_CallExpr_Fn.
    + exact H.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds;
        eassumption.
    + eapply typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds;
        eassumption.
  - assert (Heq :
        MkTy u (TClosure env_lt param_tys ret) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee. inversion Hshape; subst; simpl in *; discriminate.
  - assert (Heq :
        MkTy u (TTypeForall type_params bounds0 body_ty) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee. inversion Hshape; subst; simpl in *; discriminate.
  - assert (Heq :
        MkTy u
          (TForall m bounds0
            (MkTy u_body (TTypeForall type_params type_bounds body_ty))) =
        T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee.
    inversion Hshape as [T0 param_tys0 ret0 Hcore_shape
      | T0 m0 bounds_shape body_shape param_tys0 ret0 Hcore_shape Hbody_shape];
      subst.
    + simpl in Hcore_shape. discriminate.
    + simpl in Hcore_shape. inversion Hcore_shape; subst.
      simpl in Hbody_shape. discriminate.
  - eapply TERS_CallExpr_Forall_Fn.
    + exact H.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds;
        eassumption.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + eapply typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds;
        eassumption.
  - assert (Heq :
        MkTy u (TForall m bounds0 body_ty) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee.
    inversion Hshape as [T0 param_tys0 ret0 Hcore_shape
      | T0 m0 bounds_shape body_shape param_tys0 ret0 Hcore_shape Hbody_shape];
      subst.
    + simpl in Hcore_shape. discriminate.
    + simpl in Hcore_shape. inversion Hcore_shape; subst. congruence.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Sigma e T Sigma' R' roots ret_roots ->
    expr_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env bounds)
      Omega n R Sigma e T Sigma' R' roots ret_roots.
Proof.
  intros env bounds Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary.
  - eapply ERSSN_FunctionValueCall.
    + eapply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact H.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds.
      exact H0.
    + exact H1.
    + eapply typed_env_roots_shadow_safe_evar_call_store_safe_global_env_with_local_bounds;
        eassumption.
  - eapply ERSSN_Let.
    + exact IHHsummary1.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact IHHsummary2.
    + rewrite sctx_check_ok_global_env_with_local_bounds. exact H4.
    + exact H5.
    + exact H6.
  - eapply ERSSN_LetInfer.
    + exact IHHsummary1.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact IHHsummary2.
    + rewrite sctx_check_ok_global_env_with_local_bounds. exact H3.
    + exact H4.
    + exact H5.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    callee_body_root_shadow_store_safe_narrow_summary env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef Hsummary.
  unfold callee_body_root_shadow_store_safe_narrow_summary in *.
  destruct Hsummary as
    (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup & Hexpr & Hcompat & Hroots & Henv).
  exists T_body, Gamma_out, R_body, roots_body, ret_roots.
  repeat split; try assumption.
  apply expr_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds.
  exact Hexpr.
Qed.


Lemma eval_args_root_tail_fresh_names_for_fresh_call_prefix_ctx :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_sctx_keys_named R Σ ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_env_tail_fresh_names (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hctx_roots Hctx_keys Htyped_args Hrename x Hin.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Htyped_args)
    as [Hstore_args [_ [_ [_ [_ [_ Hrn_args]]]]]].
  destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Ω n))
              R Σ args ps_typed Σ_args R_args arg_roots Htyped_args Hrn
              Hctx_roots)
    as [Hctx_roots_args _].
  pose proof (proj1 (proj2 (typed_roots_ctx_keys_named_mutual env Ω n))
                R Σ args ps_typed Σ_args R_args arg_roots Htyped_args Hrn
                Hctx_keys) as Hctx_keys_args.
  assert (Harg_roots_named : root_env_store_roots_named R_args s_args).
  { eapply root_env_ctx_roots_named_store_typed_prefix; eassumption. }
  assert (Harg_keys_named : root_env_store_keys_named R_args s_args).
  { eapply root_env_ctx_keys_named_store_typed_prefix; eassumption. }
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names s_args) fdef fcall used' Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes.
    + eapply typed_args_roots_no_shadow; eassumption.
    + exact Hexcl.
Qed.


Lemma eval_args_root_tail_fresh_names_for_fresh_call_prefix_named :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    store_safe_function_value_call_args env args ->
    eval_args env s args s_args vs ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_env_tail_fresh_names (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Hsafe_args Heval_args Htyped_args Hrn Hnamed Hkeys
    Hrename x Hin.
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args ps_typed Σ_args R_args arg_roots
              s s_args vs Hsafe_args Htyped_args Heval_args Hnamed Hkeys)
    as [Hnamed_args [_ Hkeys_args]].
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names s_args) fdef fcall used' Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes.
    + eapply typed_args_roots_no_shadow; eassumption.
    + exact Hexcl.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_ctx :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_ctx_roots_named R Sigma ->
      root_env_sctx_keys_named R Sigma ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hctx_roots Hctx_keys
    Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Gamma_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (params_of_tys param_tys) Sigma_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
      as [Hstore_args _].
    destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Omega n))
              R Sigma args (params_of_tys param_tys) Sigma_args R_args
              arg_roots Htyped_args Hrn Hctx_roots)
      as [_ Harg_roots_ctx_named].
    eapply Forall_impl; [| exact Harg_roots_ctx_named].
    intros roots_i Hctx_named_i.
    eapply root_set_ctx_roots_named_store_typed_prefix.
    - exact Hstore_args.
    - exact Hctx_named_i. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call_prefix_ctx;
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - assert (Hstore_args : store_typed_prefix env s_args Sigma_args).
      { destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
                  env s args s_args vs Heval_args Omega n R Sigma
                  (params_of_tys param_tys) Sigma_args R_args arg_roots
                  Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
          as [Hstore_args _].
        exact Hstore_args. }
      assert (Hctx_roots_args : root_env_ctx_roots_named R_args Sigma_args).
      { destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Omega n))
                  R Sigma args (params_of_tys param_tys) Sigma_args R_args
                  arg_roots Htyped_args Hrn Hctx_roots)
          as [Hctx_roots_args _].
        exact Hctx_roots_args. }
      assert (Hnamed_args : root_env_store_roots_named R_args s_args).
      { eapply root_env_ctx_roots_named_store_typed_prefix; eassumption. }
      eapply root_env_store_roots_named_excludes_params; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite Hbounds;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.


Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Hsafe_args Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Gamma_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args (params_of_tys param_tys) Sigma_args
              R_args arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys) as [_ [Harg_roots_named _]].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call_prefix_named;
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - destruct (store_safe_function_value_call_args_typed_roots_store_named
                  env Omega n R Sigma args (params_of_tys param_tys) Sigma_args
                  R_args arg_roots s s_args vs Hsafe_args Htyped_args
                  Heval_args Hnamed Hkeys) as [Hnamed_args _].
      eapply root_env_store_roots_named_excludes_params; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite Hbounds;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.


Lemma direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_store_safe_narrow_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      exists T_body Sigma_out R_body roots_body ret_roots,
        expr_root_shadow_store_safe_narrow_summary env
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (sctx_of_ctx (params_ctx (fn_params fcall)))
          (fn_body fcall) T_body Sigma_out R_body roots_body
          ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
        roots_exclude_params (fn_params fcall) roots_body /\
        root_env_excludes_params (fn_params fcall) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename.
  unfold callee_body_root_shadow_store_safe_narrow_summary in Hsummary.
  destruct Hsummary as
    (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup_fdef & Hsummary_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Hsummary_body_params :
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots).
  { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
    exact Hsummary_body. }
  clear Hsummary_body. rename Hsummary_body_params into Hsummary_body.
  assert (Htyped_body :
    typed_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_body. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                env (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                env (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (initial_root_env_for_fn fdef)
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body
              roots_body ret_roots Hsummary_body rho
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) used_params used'
              Halpha_params Hrn_initial Hrn_initial_r Hinitial_equiv
              Hkeys_initial Hroots_initial Hnocoll_initial Hnocoll_body
              Hctx_used Hrange_used Hdisj Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r & ret_roots_r &
        Hsummary_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv & Hret_roots_equiv).
  assert (Htyped_renamed :
    typed_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin
        (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r).
  { eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_renamed. }
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (params_of_tys param_tys) Sigma_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (expr_root_shadow_store_safe_narrow_summary_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r
              roots_body_r ret_roots_r Hsummary_renamed Hsubst_fresh
              (call_param_root_env (fn_params fcall) arg_roots [])
              Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst & ret_roots_inst &
        Hsummary_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply
      (eval_args_root_tail_fresh_names_for_fresh_call_with_preservation_core
        eval_preserves_root_names_ready_mutual
        eval_preserves_root_keys_named_ready_mutual);
      eassumption. }
  assert (Hsummary_tail :
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst ret_roots_inst).
  { eapply expr_root_shadow_store_safe_narrow_summary_tail_frame;
      eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - eapply
        (eval_args_root_names_excludes_params_ready_with_preservation_core
          eval_preserves_root_names_ready_mutual);
        eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst, ret_roots_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; rewrite Houts; rewrite Hlts;
         exact Hsummary_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.


Lemma direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_store_safe_narrow_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      exists T_body Sigma_out R_body roots_body ret_roots,
        expr_root_shadow_store_safe_narrow_summary env
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (sctx_of_ctx (params_ctx (fn_params fcall)))
          (fn_body fcall) T_body Sigma_out R_body roots_body
          ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
        roots_exclude_params (fn_params fcall) roots_body /\
        root_env_excludes_params (fn_params fcall) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge Hsafe_args
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename.
  unfold callee_body_root_shadow_store_safe_narrow_summary in Hsummary.
  destruct Hsummary as
    (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup_fdef & Hsummary_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Hsummary_body_params :
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots).
  { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
    exact Hsummary_body. }
  clear Hsummary_body. rename Hsummary_body_params into Hsummary_body.
  assert (Htyped_body :
    typed_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_body. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                env (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                env (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (initial_root_env_for_fn fdef)
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body
              roots_body ret_roots Hsummary_body rho
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) used_params used'
              Halpha_params Hrn_initial Hrn_initial_r Hinitial_equiv
              Hkeys_initial Hroots_initial Hnocoll_initial Hnocoll_body
              Hctx_used Hrange_used Hdisj Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r & ret_roots_r &
        Hsummary_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv & Hret_roots_equiv).
  assert (Htyped_renamed :
    typed_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin
        (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r).
  { eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_renamed. }
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args (params_of_tys param_tys)
              Sigma_args R_args arg_roots s s_args vs
              Hsafe_args Htyped_args Heval_args Hnamed Hkeys)
      as [_ [Harg_roots_named _]].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (expr_root_shadow_store_safe_narrow_summary_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r
              roots_body_r ret_roots_r Hsummary_renamed Hsubst_fresh
              (call_param_root_env (fn_params fcall) arg_roots [])
              Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst & ret_roots_inst &
        Hsummary_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call_prefix_named;
      eassumption. }
  assert (Hsummary_tail :
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst ret_roots_inst).
  { eapply expr_root_shadow_store_safe_narrow_summary_tail_frame;
      eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args (params_of_tys param_tys)
              Sigma_args R_args arg_roots s s_args vs
              Hsafe_args Htyped_args Heval_args Hnamed Hkeys)
        as [Hnamed_args _].
      eapply root_env_store_roots_named_excludes_params; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst, ret_roots_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; rewrite Houts; rewrite Hlts;
         exact Hsummary_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.

Lemma direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_ctx :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_store_safe_narrow_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_ctx_roots_named R Sigma ->
      root_env_sctx_keys_named R Sigma ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      exists T_body Sigma_out R_body roots_body ret_roots,
        expr_root_shadow_store_safe_narrow_summary env
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (sctx_of_ctx (params_ctx (fn_params fcall)))
          (fn_body fcall) T_body Sigma_out R_body roots_body
          ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
        roots_exclude_params (fn_params fcall) roots_body /\
        root_env_excludes_params (fn_params fcall) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hctx_roots Hctx_keys
    Hrename.
  unfold callee_body_root_shadow_store_safe_narrow_summary in Hsummary.
  destruct Hsummary as
    (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup_fdef & Hsummary_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Hsummary_body_params :
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots).
  { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
    exact Hsummary_body. }
  clear Hsummary_body. rename Hsummary_body_params into Hsummary_body.
  assert (Htyped_body :
    typed_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_body. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                env (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                env (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (initial_root_env_for_fn fdef)
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body
              roots_body ret_roots Hsummary_body rho
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) used_params used'
              Halpha_params Hrn_initial Hrn_initial_r Hinitial_equiv
              Hkeys_initial Hroots_initial Hnocoll_initial Hnocoll_body
              Hctx_used Hrange_used Hdisj Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r & ret_roots_r &
        Hsummary_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv & Hret_roots_equiv).
  assert (Htyped_renamed :
    typed_env_roots_shadow_safe env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin
        (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r).
  { eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_renamed. }
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (params_of_tys param_tys) Sigma_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
      as [Hstore_args _].
    destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Omega n))
              R Sigma args (params_of_tys param_tys) Sigma_args R_args
              arg_roots Htyped_args Hrn Hctx_roots)
      as [_ Harg_roots_ctx_named].
    eapply Forall_impl; [| exact Harg_roots_ctx_named].
    intros roots_i Hctx_named_i.
    eapply root_set_ctx_roots_named_store_typed_prefix.
    - exact Hstore_args.
    - exact Hctx_named_i. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (expr_root_shadow_store_safe_narrow_summary_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r
              roots_body_r ret_roots_r Hsummary_renamed Hsubst_fresh
              (call_param_root_env (fn_params fcall) arg_roots [])
              Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst & ret_roots_inst &
        Hsummary_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call_prefix_ctx;
      eassumption. }
  assert (Hsummary_tail :
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst ret_roots_inst).
  { eapply expr_root_shadow_store_safe_narrow_summary_tail_frame;
      eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - assert (Hstore_args : store_typed_prefix env s_args Sigma_args).
      { destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
                  env s args s_args vs Heval_args Omega n R Sigma
                  (params_of_tys param_tys) Sigma_args R_args arg_roots
                  Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
          as [Hstore_args _].
        exact Hstore_args. }
      assert (Hctx_roots_args : root_env_ctx_roots_named R_args Sigma_args).
      { destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Omega n))
                  R Sigma args (params_of_tys param_tys) Sigma_args R_args
                  arg_roots Htyped_args Hrn Hctx_roots)
          as [Hctx_roots_args _].
        exact Hctx_roots_args. }
      assert (Hnamed_args : root_env_store_roots_named R_args s_args).
      { eapply root_env_ctx_roots_named_store_typed_prefix; eassumption. }
      eapply root_env_store_roots_named_excludes_params; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst, ret_roots_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; rewrite Houts; rewrite Hlts;
         exact Hsummary_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.


Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package_prefix_start :
  forall env Omega n R Σ x args u param_tys ret_ty Σ1 R1
      roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Σ1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys param_tys) Σ' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      root_env_ctx_roots_named R Σ ->
      root_env_sctx_keys_named R Σ ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret ret_ty /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u param_tys ret_ty Σ1 R1
    roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hctx_roots Hctx_keys
    Hsummary Heval_call Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TFn param_tys ret_ty))).
  { eapply SFV_TFn. reflexivity. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ (EVar x) (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
    R Σ (EVar x) (MkTy u (TFn param_tys ret_ty)) Σ1 R1 roots_callee_typed
    Htyped_callee_roots Hrn Hctx_roots) as [Hctx_roots_fn _].
  pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
    env Omega n) R Σ (EVar x) (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed Htyped_callee Hrn Hctx_keys) as Hctx_keys_fn.
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  pose proof (store_function_closure_targets_summary_eval_var
    env s s_fn x (VClosure fname []) Hsummary Heval_callee) as Hsummary_fn.
  pose proof (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
    env args s_fn s_args vs Hargs Hsummary_fn Heval_args) as Hsummary_args.
  destruct (value_has_type_empty_closure_plain_tfn_non_generic
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique)
    as [Htype_params Hlifetimes].
  destruct (value_has_type_empty_closure_tfn_components
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique
    Htype_params Hlifetimes) as [Hcaps_fdef Hbridge].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Σ1 args (params_of_tys param_tys)
    Σ' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_ctx
      env Omega n R1 Σ1 Σ' R' arg_roots args fdef fcall
      param_tys ret_ty s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hctx_roots_fn.
    - exact Hctx_keys_fn.
    - exact Hrename. }
  destruct (eval_call_expr_tfn_components_preserve_typing_with_callee_summary_route_prefix_start
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_callee
    Htyped_args Hunique Htype_params Hlifetimes Hcallee_route)
    as [Hstore' [Hv [_ [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  pose proof (eval_call_expr_tfn_components_final_store_eq_route_prefix_start
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_callee
    Htyped_args Hunique Htype_params Hlifetimes Hcallee_route) as Heq_final.
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
    env Omega n R Σ (ECallExpr (EVar x) args) ret_ty Σ' R'
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (store_remove_params (fn_captures fcall)
       (store_remove_params (fn_params fcall) s_body))
    Hnarrow Hrn Hctx_roots Hctx_keys Hstore' Hrn')
    as [Hnamed' [Hrootset_named Hkeys']].
  rewrite <- Heq_final in Hsummary_args.
  repeat split; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package_prefix_start :
  forall env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
      Σ1 R1 roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty σ ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives σ bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      root_env_ctx_roots_named R Σ ->
      root_env_sctx_keys_named R Σ ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret (open_bound_ty σ ret_ty) /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
    Σ1 R1 roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Hbody_shape
    Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hctx_roots Hctx_keys
    Hsummary Heval_call Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Forall_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Hbody_shape.
    - exact Hret_closed.
    - exact Hbounds_closed.
    - exact Hbounds.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TForall m bounds body_ty))).
  { eapply SFV_TForall_TFn.
    - reflexivity.
    - exact Hbody_shape. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
    R Σ (EVar x) (MkTy u (TForall m bounds body_ty)) Σ1 R1
    roots_callee_typed Htyped_callee_roots Hrn Hctx_roots)
    as [Hctx_roots_fn _].
  pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
    env Omega n) R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed Htyped_callee Hrn Hctx_keys) as Hctx_keys_fn.
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  pose proof (store_function_closure_targets_summary_eval_var
    env s s_fn x (VClosure fname []) Hsummary Heval_callee) as Hsummary_fn.
  pose proof (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
    env args s_fn s_args vs Hargs Hsummary_fn Heval_args) as Hsummary_args.
  destruct (value_has_type_empty_closure_tforall_tfn_components
    env s_fn fname fdef u m bounds body_ty param_tys ret_ty σ
    Hv_callee Hlookup Hunique Hbody_shape) as [Htype_params [Hcaps_fdef Hbridge]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Σ1 args
    (params_of_tys (map (open_bound_ty σ) param_tys))
    Σ' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_ctx
      env Omega n R1 Σ1 Σ' R' arg_roots args fdef fcall
      (map (open_bound_ty σ) param_tys) (open_bound_ty σ ret_ty)
      s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hctx_roots_fn.
    - exact Hctx_keys_fn.
    - exact Hrename. }
  destruct (eval_evar_call_expr_lifetime_forall_tfn_components_preserve_typing_with_callee_summary_route_prefix_start
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty σ
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route)
    as [Hstore' [Hv [_ [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  pose proof (eval_evar_call_expr_lifetime_forall_tfn_components_final_store_eq_prefix_start
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty σ
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route) as Heq_final.
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
    env Omega n R Σ (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (root_set_union roots_callee_typed (root_sets_union arg_roots))
    (store_remove_params (fn_captures fcall)
       (store_remove_params (fn_params fcall) s_body))
    Hnarrow Hrn Hctx_roots Hctx_keys Hstore' Hrn')
    as [Hnamed' [Hrootset_named Hkeys']].
  rewrite <- Heq_final in Hsummary_args.
  repeat split; eassumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package_prefix_named :
  forall env Omega n R Σ x args u param_tys ret_ty Σ1 R1
      roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Σ1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys param_tys) Σ' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret ret_ty /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u param_tys ret_ty Σ1 R1
    roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary Heval_call Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TFn param_tys ret_ty))).
  { eapply SFV_TFn. reflexivity. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) ret_ty Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ (EVar x) (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (typed_env_roots_shadow_safe_evar_store_named
    env Omega n R Σ x (MkTy u (TFn param_tys ret_ty))
    Σ1 R1 roots_callee_typed s Htyped_callee Hnamed Hkeys)
    as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    (PRE_Var x)) as Hcallee_names.
  assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
  { eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hcallee_roots_named_fn :
      root_set_store_roots_named roots_callee_typed s_fn).
  { eapply root_set_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
  { eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  pose proof (store_function_closure_targets_summary_eval_var
    env s s_fn x (VClosure fname []) Hsummary Heval_callee) as Hsummary_fn.
  pose proof (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
    env args s_fn s_args vs Hargs Hsummary_fn Heval_args) as Hsummary_args.
  destruct (value_has_type_empty_closure_plain_tfn_non_generic
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique)
    as [Htype_params Hlifetimes].
  destruct (value_has_type_empty_closure_tfn_components
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique
    Htype_params Hlifetimes) as [Hcaps_fdef Hbridge].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Σ1 args (params_of_tys param_tys)
    Σ' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
      env Omega n R1 Σ1 Σ' R' arg_roots args fdef fcall
      param_tys ret_ty s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Hargs.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  destruct (eval_call_expr_tfn_components_preserve_typing_with_callee_summary_route_prefix_start
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_callee
    Htyped_args Hunique Htype_params Hlifetimes Hcallee_route)
    as [Hstore' [Hv [Hpres' [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  pose proof (eval_call_expr_tfn_components_final_store_eq_route_prefix_start
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_callee
    Htyped_args Hunique Htype_params Hlifetimes Hcallee_route) as Heq_final.
  destruct (store_safe_function_value_call_args_typed_roots_store_named
    env Omega n R1 Σ1 args (params_of_tys param_tys) Σ' R' arg_roots
    s_fn s_args vs Hargs Htyped_args_roots Heval_args Hnamed_fn Hkeys_fn)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
    env s_fn args s_args vs Heval_args
    (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hargs_names.
  assert (Hcallee_roots_named_args :
      root_set_store_roots_named roots_callee_typed s_args).
  { eapply root_set_store_roots_named_store_names_eq; eassumption. }
  assert (Hrootset_named_args :
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s_args).
  { apply root_set_store_roots_named_union.
    - exact Hcallee_roots_named_args.
    - apply root_sets_store_roots_named_union. exact Harg_roots_named. }
  assert (Hnamed' :
      root_env_store_roots_named R'
        (store_remove_params (fn_captures fcall)
           (store_remove_params (fn_params fcall) s_body))).
  { rewrite Heq_final. exact Hnamed_args. }
  assert (Hrootset_named :
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (store_remove_params (fn_captures fcall)
           (store_remove_params (fn_params fcall) s_body))).
  { rewrite Heq_final. exact Hrootset_named_args. }
  assert (Hkeys' :
      root_env_store_keys_named R'
        (store_remove_params (fn_captures fcall)
           (store_remove_params (fn_params fcall) s_body))).
  { rewrite Heq_final. exact Hkeys_args. }
  rewrite <- Heq_final in Hsummary_args.
  repeat split; eassumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package_prefix_named :
  forall env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
      Σ1 R1 roots_callee_typed arg_roots Σ' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
      (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty σ ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives σ bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Σ1 args
      (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret (open_bound_ty σ ret_ty) /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) ret /\
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ x args u m bounds body_ty param_tys ret_ty σ
    Σ1 R1 roots_callee_typed arg_roots Σ' R' Hargs Htyped_callee Hbody_shape
    Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary Heval_call Hunique.
  assert (Htyped_call :
      typed_env_roots_shadow_safe env Omega n R Σ (ECallExpr (EVar x) args)
        (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply TERS_CallExpr_Forall_Fn.
    - intros fname caps Hcontra. discriminate Hcontra.
    - exact Htyped_callee.
    - exact Hbody_shape.
    - exact Hret_closed.
    - exact Hbounds_closed.
    - exact Hbounds.
    - exact Htyped_args. }
  assert (Hcallee_shape :
      supported_non_type_generic_function_value_call_callee_shape
        (MkTy u (TForall m bounds body_ty))).
  { eapply SFV_TForall_TFn.
    - reflexivity.
    - exact Hbody_shape. }
  assert (Hnarrow :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ECallExpr (EVar x) args) (open_bound_ty σ ret_ty) Σ' R'
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (root_set_union roots_callee_typed (root_sets_union arg_roots))).
  { eapply ERSSN_FunctionValueCall.
    - exact Hargs.
    - exact Htyped_callee.
    - exact Hcallee_shape.
    - exact Htyped_call. }
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ (EVar x) (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Σ (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (typed_env_roots_shadow_safe_evar_store_named
    env Omega n R Σ x (MkTy u (TForall m bounds body_ty))
    Σ1 R1 roots_callee_typed s Htyped_callee Hnamed Hkeys)
    as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    (PRE_Var x)) as Hcallee_names.
  assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
  { eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hcallee_roots_named_fn :
      root_set_store_roots_named roots_callee_typed s_fn).
  { eapply root_set_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
  { eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  pose proof (store_function_closure_targets_summary_eval_var
    env s s_fn x (VClosure fname []) Hsummary Heval_callee) as Hsummary_fn.
  pose proof (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
    env args s_fn s_args vs Hargs Hsummary_fn Heval_args) as Hsummary_args.
  destruct (value_has_type_empty_closure_tforall_tfn_components
    env s_fn fname fdef u m bounds body_ty param_tys ret_ty σ
    Hv_callee Hlookup Hunique Hbody_shape) as [Htype_params [Hcaps_fdef Hbridge]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Σ1 args
    (params_of_tys (map (open_bound_ty σ) param_tys))
    Σ' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
      env Omega n R1 Σ1 Σ' R' arg_roots args fdef fcall
      (map (open_bound_ty σ) param_tys) (open_bound_ty σ ret_ty)
      s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Hargs.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  destruct (eval_evar_call_expr_lifetime_forall_tfn_components_preserve_typing_with_callee_summary_route_prefix_start
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty σ
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route)
    as [Hstore' [Hv [Hpres' [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  pose proof (eval_evar_call_expr_lifetime_forall_tfn_components_final_store_eq_prefix_start
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Σ Σ1 R1 Σ' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty σ
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route) as Heq_final.
  destruct (store_safe_function_value_call_args_typed_roots_store_named
    env Omega n R1 Σ1 args (params_of_tys (map (open_bound_ty σ) param_tys))
    Σ' R' arg_roots s_fn s_args vs Hargs Htyped_args_roots Heval_args
    Hnamed_fn Hkeys_fn) as [Hnamed_args [Harg_roots_named Hkeys_args]].
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
    env s_fn args s_args vs Heval_args
    (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hargs_names.
  assert (Hcallee_roots_named_args :
      root_set_store_roots_named roots_callee_typed s_args).
  { eapply root_set_store_roots_named_store_names_eq; eassumption. }
  assert (Hrootset_named_args :
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots)) s_args).
  { apply root_set_store_roots_named_union.
    - exact Hcallee_roots_named_args.
    - apply root_sets_store_roots_named_union. exact Harg_roots_named. }
  assert (Hnamed' :
      root_env_store_roots_named R'
        (store_remove_params (fn_captures fcall)
           (store_remove_params (fn_params fcall) s_body))).
  { rewrite Heq_final. exact Hnamed_args. }
  assert (Hrootset_named :
      root_set_store_roots_named
        (root_set_union roots_callee_typed (root_sets_union arg_roots))
        (store_remove_params (fn_captures fcall)
           (store_remove_params (fn_params fcall) s_body))).
  { rewrite Heq_final. exact Hrootset_named_args. }
  assert (Hkeys' :
      root_env_store_keys_named R'
        (store_remove_params (fn_captures fcall)
           (store_remove_params (fn_params fcall) s_body))).
  { rewrite Heq_final. exact Hkeys_args. }
  rewrite <- Heq_final in Hsummary_args.
  repeat split; eassumption.
Qed.



Lemma expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_ctx :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      root_env_ctx_roots_named R Σ ->
      root_env_sctx_keys_named R Σ ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret T /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hctx_roots Hctx_keys Hsummary_store Heval Hunique.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package_prefix_start;
        eassumption.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package_prefix_start;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hctx_roots Hctx_keys Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]].
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_roots_named_add_env_store_add; eassumption).
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    pose proof (expr_root_shadow_store_safe_narrow_summary_typed
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1)
      as Htyped_shadow1.
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ e1 T1 Σ1 R1 roots1 Htyped_shadow1)
      as Htyped_roots1.
    destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
      R Σ e1 T1 Σ1 R1 roots1 Htyped_roots1 Hrn Hctx_roots)
      as [Hctx_roots1 Hrootset1_ctx].
    pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
      env Omega n) R Σ e1 T1 Σ1 R1 roots1 Htyped_shadow1
      Hrn Hctx_keys) as Hctx_keys1.
    assert (Hadd_ctx_roots :
      root_env_ctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1))
      by (apply root_env_ctx_roots_named_add_binding; assumption).
    assert (Hadd_ctx_keys :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1))
      by (apply root_env_sctx_keys_named_add_binding; assumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hadd_ctx_roots Hadd_ctx_keys Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H6.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed_prefix env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_prefix_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hsummary_let :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ELet m x T_hidden e1 e2) T2 (sctx_remove x Sigma2)
        (root_env_remove x R2) roots2 ret_roots).
    { eapply ERSSN_Let; eassumption. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
      env Omega n R Σ (ELet m x T_hidden e1 e2) T2
      (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
      (store_remove x s2) Hsummary_let Hrn Hctx_roots Hctx_keys
      Hstore_final Hrn_final) as [Hnamed_final [Hrootset_final Hkeys_final]].
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hv2.
      * eapply value_roots_exclude_root; eassumption.
    + exact Hroots_removed.
    + exact Hvalue_roots.
    + exact Hrootset_final.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
Qed.



Lemma expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Heval Hunique.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package_prefix_named;
        eassumption.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hpres1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]]].
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_roots_named_add_env_store_add; eassumption).
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hpres2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H6.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed_prefix env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_prefix_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hsummary_let :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ELet m x T_hidden e1 e2) T2 (sctx_remove x Sigma2)
        (root_env_remove x R2) roots2 ret_roots).
    { eapply ERSSN_Let; eassumption. }
    assert (Hremain_names :
      forall z,
        In z (store_names s2) ->
        z <> x ->
        In z (store_names (store_remove x s2)))
      by (intros z Hin Hneq; apply store_names_remove_keeps_other; assumption).
    assert (Hnamed_removed :
      root_env_store_roots_named (root_env_remove x R2) s2).
    { eapply root_env_store_roots_named_remove_env; eassumption. }
    assert (Hnamed_final :
      root_env_store_roots_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_roots_named_store_remove_excluding.
      - intros y roots Hlookup.
        apply H6 with (y := y) (roots := roots); [exact Hlookup|].
        intros Heq. subst y.
        rewrite root_env_lookup_remove_eq_no_shadow in Hlookup by exact Hrn2.
        discriminate.
      - exact Hnamed_removed.
      - exact Hremain_names. }
    assert (Hrootset_final :
      root_set_store_roots_named roots2 (store_remove x s2)).
    { eapply root_set_store_roots_named_store_remove_excluding.
      - exact H5.
      - exact Hroots2_named.
      - exact Hremain_names. }
    assert (Hkeys_final :
      root_env_store_keys_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_keys_named_remove_env_store_remove; eassumption. }
    assert (Hpres_add_body :
      store_ref_targets_preserved env s1 s2).
    { eapply store_ref_targets_preserved_trans; eassumption. }
    assert (Hpres_removed_from_s1 :
      store_ref_targets_preserved env s1 (store_remove x s2)).
    { eapply store_ref_targets_preserved_remove_after_absent_root;
        eassumption. }
    assert (Hpres_final :
      store_ref_targets_preserved env s (store_remove x s2)).
    { eapply store_ref_targets_preserved_trans; eassumption. }
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hv2.
      * eapply value_roots_exclude_root; eassumption.
    + exact Hpres_final.
    + exact Hroots_removed.
    + exact Hvalue_roots.
    + exact Hrootset_final.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_final_store_eq_prefix_named :
  forall env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
      roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys param_tys) Sigma' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      exists s_fn s_args vs fname,
        eval env s (EVar x) s_fn (VClosure fname []) /\
        eval_args env s_fn args s_args vs /\
        s' = s_args.
Proof.
  intros env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary Heval_call Hunique.
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Sigma (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (typed_env_roots_shadow_safe_evar_store_named
    env Omega n R Sigma x (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed s Htyped_callee Hnamed Hkeys)
    as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    (PRE_Var x)) as Hcallee_names.
  assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
  { eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
  { eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TFn param_tys ret_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  destruct (value_has_type_empty_closure_plain_tfn_non_generic
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique)
    as [Htype_params Hlifetimes].
  destruct (value_has_type_empty_closure_tfn_components
    env s_fn fname fdef u param_tys ret_ty Hv_callee Hlookup Hunique
    Htype_params Hlifetimes) as [Hcaps_fdef Hbridge].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
      env Omega n R1 Sigma1 Sigma' R' arg_roots args fdef fcall
      param_tys ret_ty s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Hargs.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  pose proof (eval_call_expr_tfn_components_final_store_eq_route_prefix_start
    env s s_fn s_args s_body (EVar x) args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' roots_callee_typed arg_roots u
    param_tys ret_ty
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_callee
    Htyped_args Hunique Htype_params Hlifetimes Hcallee_route) as Heq_final.
  exists s_fn, s_args, vs, fname.
  repeat split; assumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_final_store_eq_prefix_named :
  forall env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
      Sigma1 R1 roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty sigma ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives sigma bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots ->
    forall s s' ret,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      exists s_fn s_args vs fname,
        eval env s (EVar x) s_fn (VClosure fname []) /\
        eval_args env s_fn args s_args vs /\
        s' = s_args.
Proof.
  intros env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Hbody_shape
    Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hsummary Heval_call Hunique.
  dependent destruction Heval_call.
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
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    Omega n R Sigma (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed (ProvReady_Var x) Hstore Hroots Hshadow Hrn
    Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
  destruct (typed_env_roots_shadow_safe_evar_store_named
    env Omega n R Sigma x (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed s Htyped_callee Hnamed Hkeys)
    as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s_fn (VClosure fname captured) Heval_callee
    (PRE_Var x)) as Hcallee_names.
  assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
  { eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
  { eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (value_has_type_closure_captured_nil env s_fn fname captured
    (MkTy u (TForall m bounds body_ty)) Hv_callee) as Hcaptured_nil.
  subst captured.
  simpl in Hrename, Heval_body.
  pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
    env s s_fn x fname fdef Hsummary Heval_callee Hlookup) as Hcallee_summary.
  destruct (value_has_type_empty_closure_tforall_tfn_components
    env s_fn fname fdef u m bounds body_ty param_tys ret_ty sigma
    Hv_callee Hlookup Hunique Hbody_shape) as [Htype_params [Hcaps_fdef Hbridge]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  assert (Hcallee_route :
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R')
        (root_sets_union arg_roots)).
  { eapply (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
      env Omega n R1 Sigma1 Sigma' R' arg_roots args fdef fcall
      (map (open_bound_ty sigma) param_tys) (open_bound_ty sigma ret_ty)
      s_fn s_args vs used').
    - exact Hcallee_summary.
    - exact Hcaps_fdef.
    - exact Hbridge.
    - exact Hargs.
    - exact Htyped_args_roots.
    - exact Heval_args.
    - exact Hprov_args.
    - exact Hstore_fn.
    - exact Hroots_fn.
    - exact Hshadow_fn.
    - exact Hrn_fn.
    - exact Hnamed_fn.
    - exact Hkeys_fn.
    - exact Hrename. }
  pose proof (eval_evar_call_expr_lifetime_forall_tfn_components_final_store_eq_prefix_start
    env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
    Heval_callee Hlookup Heval_args Hrename Heval_body
    Omega n R Sigma Sigma1 R1 Sigma' R' roots_callee_typed arg_roots u
    m bounds body_ty param_tys ret_ty sigma
    (store_safe_function_value_call_args_preservation_ready env args Hargs)
    Hstore Hroots Hshadow Hrn Htyped_callee Hbody_shape Htyped_args
    Htype_params Hcaps_fdef Hbridge Hcallee_route) as Heq_final.
  exists s_fn, s_args, vs, fname.
  repeat split; assumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_frame_scope_prefix_named :
  forall env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
      roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys param_tys) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_frame_scope ps Sigma s frame ->
      store_frame_static_fresh Sigma frame ->
      frame_scope_roots_ready_result ps R' Sigma' s' frame.
Proof.
  intros env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope Hfresh.
  destruct (expr_root_shadow_store_safe_narrow_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1 roots_callee_typed
    arg_roots Sigma' R' Hargs Htyped_callee Htyped_args s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TFn param_tys ret_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hroots Hshadow Hrn
    Hscope Hfresh) as
    [Hcover_fn [Hroots_fn [Hshadow_fn [Hrn_fn [Hscope_fn Hfresh_fn]]]]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  pose proof (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys param_tys) Sigma' R' arg_roots ps frame
    Hprov_args Htyped_args_roots Hcover_fn Hroots_fn Hshadow_fn Hrn_fn
    Hscope_fn Hfresh_fn) as Hframe_args.
  rewrite Heq_final. exact Hframe_args.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_frame_scope_prefix_named :
  forall env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
      Sigma1 R1 roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty sigma ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives sigma bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_frame_scope ps Sigma s frame ->
      store_frame_static_fresh Sigma frame ->
      frame_scope_roots_ready_result ps R' Sigma' s' frame.
Proof.
  intros env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope Hfresh.
  destruct (expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TForall m bounds body_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hroots Hshadow Hrn
    Hscope Hfresh) as
    [Hcover_fn [Hroots_fn [Hshadow_fn [Hrn_fn [Hscope_fn Hfresh_fn]]]]].
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  pose proof (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots
    ps frame Hprov_args Htyped_args_roots Hcover_fn Hroots_fn Hshadow_fn
    Hrn_fn Hscope_fn Hfresh_fn) as Hframe_args.
  rewrite Heq_final. exact Hframe_args.
Qed.


Lemma store_safe_function_value_call_args_roots_shadow_safe_preserves_param_cover :
  forall env Omega n R Sigma args params Sigma' R' roots ps,
    store_safe_function_value_call_args env args ->
    typed_args_roots_shadow_safe env Omega n R Sigma args params
      Sigma' R' roots ->
    root_env_covers_params ps R ->
    root_env_covers_params ps R'.
Proof.
  intros env Omega n R Sigma args params Sigma' R' roots ps Hsafe.
  revert R Sigma params Sigma' R' roots ps.
  induction Hsafe as [| arg rest Harg Hsafe IH];
    intros R Sigma params Sigma' R' roots ps Htyped Hcover.
  - dependent destruction Htyped. exact Hcover.
  - dependent destruction Htyped.
    assert (Hcover1 : root_env_covers_params ps R1).
    { destruct Harg; dependent destruction H; exact Hcover. }
    eapply IH; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_param_scope_prefix_named :
  forall env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
      roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TFn param_tys ret_ty)) Sigma1 R1 roots_callee_typed ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys param_tys) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope.
  destruct (expr_root_shadow_store_safe_narrow_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u param_tys ret_ty Sigma1 R1
    roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee Htyped_args
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TFn param_tys ret_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TFn param_tys ret_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hscope)
    as [frame_fn Hscope_fn].
  assert (Hcover_fn : root_env_covers_params ps R1).
  { dependent destruction Htyped_callee.
    all: exact Hcover. }
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args (params_of_tys param_tys)
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_param_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys param_tys) Sigma' R' arg_roots ps frame_fn
    Hprov_args Htyped_args_roots Hcover_fn Hscope_fn) as [frame_args Hscope_args].
  rewrite Heq_final. exists frame_args. exact Hscope_args.
Qed.

Lemma expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_param_scope_prefix_named :
  forall env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
      Sigma1 R1 roots_callee_typed arg_roots Sigma' R',
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee_typed ->
    ty_core body_ty = TFn param_tys ret_ty ->
    contains_lbound_ty (open_bound_ty sigma ret_ty) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Omega a b) (open_bound_outlives sigma bounds) ->
    typed_args_roots_shadow_safe env Omega n R1 Sigma1 args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ECallExpr (EVar x) args) s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args
    s s' ret ps frame Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary
    Heval_call Hunique Hcover Hscope.
  destruct (expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_final_store_eq_prefix_named
    env Omega n R Sigma x args u m bounds body_ty param_tys ret_ty sigma
    Sigma1 R1 roots_callee_typed arg_roots Sigma' R' Hargs Htyped_callee
    Hbody_shape Hret_closed Hbounds_closed Hbounds Htyped_args s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary Heval_call Hunique)
    as [s_fn [s_args [vs [fname [Heval_callee [Heval_args Heq_final]]]]]].
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Sigma (EVar x) (MkTy u (TForall m bounds body_ty))
    Sigma1 R1 roots_callee_typed Htyped_callee) as Htyped_callee_roots.
  destruct (proj1 eval_preserves_param_scope_roots_ready_mutual
    env s (EVar x) s_fn (VClosure fname []) Heval_callee
    Omega n R Sigma (MkTy u (TForall m bounds body_ty)) Sigma1 R1
    roots_callee_typed ps frame
    (ProvReady_Var x) Htyped_callee_roots Hcover Hscope)
    as [frame_fn Hscope_fn].
  assert (Hcover_fn : root_env_covers_params ps R1).
  { dependent destruction Htyped_callee.
    all: exact Hcover. }
  pose proof (typed_args_roots_shadow_safe_roots
    env Omega n R1 Sigma1 args
    (params_of_tys (map (open_bound_ty sigma) param_tys))
    Sigma' R' arg_roots Htyped_args) as Htyped_args_roots.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args (store_safe_function_value_call_args_preservation_ready env args Hargs))
    as Hprov_args.
  destruct (proj1 (proj2 eval_preserves_param_scope_roots_ready_mutual)
    env s_fn args s_args vs Heval_args Omega n R1 Sigma1
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R' arg_roots
    ps frame_fn Hprov_args Htyped_args_roots Hcover_fn Hscope_fn)
    as [frame_args Hscope_args].
  rewrite Heq_final. exists frame_args. exact Hscope_args.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T
      Sigma' R' roots ret_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      root_env_covers_params ps R ->
      store_frame_scope ps Sigma s frame ->
      store_frame_static_fresh Sigma frame ->
      frame_scope_roots_ready_result ps R' Sigma' s' frame.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret ps frame Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hcover Hscope Hfresh.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_frame_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_frame_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1
      s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
      Heval1 Hunique)
      as [Hstore1 [Hv1 [Hpres1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]]].
    destruct (IHHsummary1 s s1 v1 ps frame Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Hsummary_store Heval1 Hunique Hcover Hscope Hfresh)
      as [Hcover1 [Hroots1_frame [Hshadow1_frame
        [Hrn1_frame [Hscope1 Hfresh1]]]]].
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H1) as Hnotin.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hnot_frame : ~ In x (store_names frame))
      by (eapply store_frame_scope_lookup_absent_in_frame; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply store_add_roots_within.
      - exact Hroots1_runtime.
      - exact H1.
      - exact Hv1_roots. }
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_roots_named_add_env_store_add.
      - exact Hnamed1.
      - exact Hroots1_named. }
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_keys_named_add_env_store_add.
      - exact Hkeys1. }
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function.
      - exact Hsummary1_store.
      - exact Hv1_hidden.
      - exact H0. }
    assert (Hcover_add :
      root_env_covers_params ps (root_env_add x roots1 R1))
      by (apply root_env_covers_params_add; exact Hcover1).
    assert (Hscope_add :
      store_frame_scope ps (sctx_add x T_hidden m Σ1)
        (store_add x T_hidden v1 s1) frame).
    { eapply store_frame_scope_add_weaken.
      - exact Hnotin.
      - simpl. left. reflexivity.
      - intros y Hy. simpl. right. exact Hy.
      - exact Hscope1. }
    assert (Hfresh_add :
      store_frame_static_fresh (sctx_add x T_hidden m Σ1) frame).
    { eapply store_frame_static_fresh_add.
      - exact Hfresh1.
      - exact Hnot_frame. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2 ps frame
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique Hcover_add Hscope_add Hfresh_add)
      as [Hcover2 [Hroots2 [Hshadow2 [Hrn2 [Hscope2 Hfresh2]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2)).
    { eapply store_remove_roots_within.
      - exact Hroots2.
      - exact Hremove_names. }
    assert (Hin_x_Sigma2 : In x (ctx_names Sigma2)).
    { pose proof (expr_root_shadow_store_safe_narrow_summary_typed
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2
        ret_roots Hsummary2) as Htyped_body.
      pose proof (typed_env_structural_same_bindings env Omega n
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2
        (typed_env_roots_structural env Omega n
          (root_env_add x roots1 R1) (sctx_add x T_hidden m Σ1)
          e2 T2 Sigma2 R2 roots2
          (typed_env_roots_shadow_safe_roots env Omega n
            (root_env_add x roots1 R1) (sctx_add x T_hidden m Σ1)
            e2 T2 Sigma2 R2 roots2 Htyped_body))) as Hsame_body.
      pose proof (sctx_same_bindings_names_alpha
        (sctx_add x T_hidden m Σ1) Sigma2 Hsame_body) as Hnames.
      rewrite Hnames. simpl. left. reflexivity. }
    repeat split.
    + eapply root_env_covers_params_remove_non_param.
      * exact Hcover2.
      * exact Hnotin.
    + exact Hroots_removed.
    + apply store_no_shadow_remove. exact Hshadow2.
    + apply root_env_no_shadow_remove. exact Hrn2.
    + eapply store_frame_scope_remove_non_param_sctx_remove.
      * exact Hin_x_Sigma2.
      * exact Hshadow2.
      * exact Hfresh2.
      * exact Hscope2.
      * exact Hnotin.
    + apply store_frame_static_fresh_remove. exact Hfresh2.
  - dependent destruction Heval.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_preserves_param_cover :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T
      Sigma' R' roots ret_roots ->
    forall ps,
      root_env_covers_params ps R ->
      root_env_covers_params ps R'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary; intros ps Hcover.
  - dependent destruction H2;
      match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          _ _ ?R_args _,
        Htyped_args : typed_args_roots_shadow_safe _ _ _ ?R_args _ args
          _ _ ?R_final _ |- root_env_covers_params _ ?R_final =>
          assert (Hcover_args : root_env_covers_params ps R_args)
            by (dependent destruction Htyped_callee; exact Hcover);
          eapply store_safe_function_value_call_args_roots_shadow_safe_preserves_param_cover;
            [exact H | exact Htyped_args | exact Hcover_args]
      end.
  - pose proof (IHHsummary1 ps Hcover) as Hcover1.
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H1) as Hnotin.
    pose proof (root_env_covers_params_add
      ps R1 x roots1 Hcover1) as Hcover_add.
    pose proof (IHHsummary2 ps Hcover_add) as Hcover2.
    eapply root_env_covers_params_remove_non_param; eassumption.
  - pose proof (IHHsummary1 ps Hcover) as Hcover1.
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H0) as Hnotin.
    pose proof (root_env_covers_params_add
      ps R1 x roots1 Hcover1) as Hcover_add.
    pose proof (IHHsummary2 ps Hcover_add) as Hcover2.
    eapply root_env_covers_params_remove_non_param; eassumption.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary env Omega n R Sigma e T Sigma' R' roots ret_roots ->
    forall s s' ret ps frame,
      store_typed_prefix env s Sigma -> store_roots_within R s -> store_no_shadow s -> root_env_no_shadow R ->
      root_env_store_roots_named R s -> root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s -> eval env s e s' ret -> fn_env_unique_by_name env ->
      root_env_covers_params ps R -> store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret ps frame Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval Hunique Hcover Hscope.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_param_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TClosure env_lt param_tys ret)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Sigma_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Sigma_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_param_scope_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1
      s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
      Heval1 Hunique)
      as [Hstore1 [Hv1 [Hpres1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]]].
    pose proof (expr_root_shadow_store_safe_narrow_summary_preserves_param_cover
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1
      ps Hcover) as Hcover1.
    destruct (IHHsummary1 s s1 v1 ps frame Hstore Hroots Hshadow Hrn
      Hnamed Hkeys Hsummary_store Heval1 Hunique Hcover Hscope)
      as [frame1 Hscope1].
    pose proof (root_env_covers_params_lookup_none_not_in
      ps R1 x Hcover1 H1) as Hnotin.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply store_add_roots_within.
      - exact Hroots1_runtime.
      - exact H1.
      - exact Hv1_roots. }
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_roots_named_add_env_store_add.
      - exact Hnamed1.
      - exact Hroots1_named. }
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_keys_named_add_env_store_add.
      - exact Hkeys1. }
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function.
      - exact Hsummary1_store.
      - exact Hv1_hidden.
      - exact H0. }
    assert (Hcover_add :
      root_env_covers_params ps (root_env_add x roots1 R1))
      by (apply root_env_covers_params_add; exact Hcover1).
    assert (Hscope_add :
      store_param_scope ps (store_add x T_hidden v1 s1) frame1).
    { eapply store_param_scope_add.
      - exact Hnotin.
      - exact Hscope1. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2 ps frame1
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique Hcover_add Hscope_add) as [frame2 Hscope2].
    eapply store_param_scope_remove_non_param; eassumption.
  - dependent destruction Heval.
Qed.


Lemma eval_direct_call_store_safe_narrow_summary_value_prefix_named :
  forall env Omega n R Sigma fname args sigma Sigma_args R_args arg_roots
      s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary env fdef ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECall fname args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    fn_type_params fdef = 0 ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret (apply_lt_ty sigma (fn_ret fdef)).
Proof.
  intros env Omega n R Sigma fname args sigma Sigma_args R_args arg_roots
    s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef Hcaps_fdef
    Htype_params Htyped_args Houtlives.
  dependent destruction Heval_call.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  | Hlookup_fn : lookup_fn ?fname_call ?fns = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  end.
  match goal with
  | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
      rename H into Heval_args;
      rename s_args0 into s_args;
      rename vs0 into vs
  end.
  match goal with
  | H : alpha_rename_fn_def (store_names s_args) fdef =
        (?fcall0, ?used0) |- _ =>
      rename H into Hrename;
      rename fcall0 into fcall;
      rename used0 into used'
  end.
  match goal with
  | H : eval _ (bind_params (fn_params fcall) vs s_args)
        (fn_body fcall) ?s_body0 ret |- _ =>
      rename H into Heval_body;
      rename s_body0 into s_body
  end.
  pose proof (typed_args_roots_params_of_tys_map_param_ty
    env Omega n R Sigma args (apply_lt_params sigma (fn_params fdef))
    Sigma_args R_args arg_roots Htyped_args) as Htyped_args_param_tys.
  pose proof (runtime_tfn_signature_bridge_apply_lt_params
    sigma (fn_params fdef) (fn_ret fdef)) as Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
    env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args Hready_args) as Hprov_args.
  destruct (direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    (map param_ty (apply_lt_params sigma (fn_params fdef)))
    (apply_lt_ty sigma (fn_ret fdef)) s s_args vs used'
    Hsummary Hcaps_fdef Hbridge Hsafe_args Htyped_args_param_tys Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
    as [Hstore_args [Hargs_values_sigma [Hpres_args
        [Hroots_args [_ [Hshadow_args Hrn_args]]]]]].
  assert (Hargs_values_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_values_sigma. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hargs_values_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Omega n R Sigma
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots (fn_params fcall) Heval_args Hprov_args Htyped_args
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_values_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args
              (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
              arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hsummary_bind :
    store_function_closure_targets_summary env
      (bind_params (fn_params fcall) vs s_args)).
  { eapply store_safe_function_value_call_args_bind_params_summary;
      eassumption. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Hsummary_body_env :
    expr_root_shadow_store_safe_narrow_summary body_env
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots).
  { subst body_env.
    eapply expr_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds.
    exact Hsummary_body. }
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hsummary_bind_body_env :
    store_function_closure_targets_summary body_env
      (bind_params (fn_params fcall) vs s_args)).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    exact Hsummary_bind. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R_args)
    (sctx_of_ctx (params_ctx (fn_params fcall)))
    (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots
    Hsummary_body_env
    (bind_params (fn_params fcall) vs s_args) s_body ret
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
      [Hrootset_body [Hshadow_body [Hrn_body [Hnamed_body
        [Hkeys_body Hsummary_body_store]]]]]]]]]].
  assert (Hframe_start :
    store_param_scope (fn_params fcall)
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_param_scope_bind_params. exact Hargs_values_fcall. }
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env (fn_params fcall) arg_roots R_args)
    (sctx_of_ctx (params_ctx (fn_params fcall)))
    (fn_body fcall) T_body Sigma_out R_body roots_body ret_roots
    Hsummary_body_env
    (bind_params (fn_params fcall) vs s_args) s_body ret
    (fn_params fcall) s_args Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Hsummary_bind_body_env
    Heval_body_body_env Hunique_body_env Hcover_bind Hframe_start)
    as [frame_final Hscope_body].
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret_alpha. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              (fn_params fcall) s_body frame_final R_body roots_body ret
              Hscope_body Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty sigma (fn_ret fdef))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  exact Hv_final.
Qed.

Definition callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_store_safe_narrow_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_captured_call_provenance_summary env fdef \/
  callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    env fdef \/
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
  apply orb_true_iff in Hcheck as [Hhead | Hnarrow].
  - apply orb_true_iff in Hhead as [Hold | Hdirect].
    + left. apply check_fn_root_shadow_captured_call_provenance_summary_sound.
      exact Hold.
    + right. left.
      destruct (direct_call_target_expr (fn_body fdef))
        as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
      apply andb_true_iff in Hdirect as [Hready_args Hdirect].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee))
        as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
        eqn:Hcallee_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fcallee
        (initial_root_env_for_fn fcallee))
        as [[[[T_callee_env Gamma_callee_env] R_callee_env]
              roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hdirect.
      destruct Hdirect as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      destruct (check_expr_root_shadow_store_safe_narrow_summary_sound
        env (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee) T_callee Gamma_callee R_callee roots_callee
        Hcallee_core Hcallee_expr) as [ret_roots_callee Hcallee_summary].
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split.
      { unfold direct_call_target_expr in Htarget.
        destruct (fn_body fdef); try discriminate.
        - inversion Htarget. reflexivity.
        - destruct e; try discriminate.
          inversion Htarget. reflexivity. }
      split; [apply store_safe_function_value_call_args_b_sound; exact Hready_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split.
      { exists T_callee, Gamma_callee, R_callee, roots_callee,
          ret_roots_callee.
        repeat split.
        - eapply infer_env_roots_shadow_safe_params_nodup.
          exact Hcallee_env.
        - exact Hcallee_summary.
        - exact Hcallee_compat.
        - apply fn_params_roots_exclude_b_sound. exact Hcallee_roots.
        - apply fn_params_root_env_excludes_b_sound. exact Hcallee_env_excl. }
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
  - right. right.
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
