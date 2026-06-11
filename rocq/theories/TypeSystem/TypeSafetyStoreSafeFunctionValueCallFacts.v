From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyReadiness TypeSafetyDirectCallEvidenceFacts.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Inductive store_safe_function_value_call_arg
    (env : global_env) : expr -> Prop :=
  | SSFVCArg_Unit :
      store_safe_function_value_call_arg env EUnit
  | SSFVCArg_Lit : forall lit,
      store_safe_function_value_call_arg env (ELit lit)
  | SSFVCArg_Var : forall x,
      store_safe_function_value_call_arg env (EVar x)
  | SSFVCArg_Fn : forall fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_provenance_summary env fdef ->
      store_safe_function_value_call_arg env (EFn fname)
  | SSFVCArg_EmptyStruct : forall name lts tys sdef,
      lookup_struct name env = Some sdef ->
      struct_bounds sdef = [] ->
      store_safe_function_value_call_arg env (EStruct name lts tys []).

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
  destruct Harg; try constructor.
  constructor.
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

Lemma typed_fields_roots_empty_literal_ctx_names :
  forall env Omega n lts args R Sigma defs Sigma' R' roots,
    typed_fields_roots env Omega n lts args R Sigma [] defs Sigma' R' roots ->
    ctx_names Sigma' = ctx_names Sigma.
Proof.
  intros env Omega n lts args R Sigma defs Sigma' R' roots Hfields.
  dependent destruction Hfields.
  reflexivity.
Qed.

Lemma typed_env_roots_shadow_safe_call_generic_typed_args_roots :
  forall env Ω n R Σ fname type_args args T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ
      (ECallGeneric fname type_args args) T Σ' R' roots ->
    exists fdef σ arg_roots,
      In fdef (env_fns env) /\
      fn_name fdef = fname /\
      fn_captures fdef = [] /\
      Datatypes.length type_args = fn_type_params fdef /\
      check_struct_bounds env (fn_bounds fdef) type_args = None /\
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ
          (apply_type_params type_args (fn_params fdef))) Σ' R' arg_roots /\
      Forall (fun '(a, b) => outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) /\
      T = apply_lt_ty σ
        (subst_type_params_ty type_args (fn_ret fdef)) /\
      roots = root_sets_union arg_roots.
Proof.
  intros env Ω n R Σ fname type_args args T Σ' R' roots Htyped.
  pose proof (typed_env_roots_shadow_safe_roots
    env Ω n R Σ (ECallGeneric fname type_args args)
    T Σ' R' roots Htyped) as Htyped_roots.
  dependent destruction Htyped_roots.
  eexists. eexists. eexists.
  repeat split; eauto.
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
        destruct Harg as [| lit | x | fname fdef Hin Hname Hsummary | name lts tys sdef Hlookup Hbounds]
    end.
    + dependent destruction H.
      destruct (IHHtyped Hsafe s Hnamed Hkeys)
        as [HR [Hroots_rest [Hnamed' Hkeys']]].
      subst R2.
      repeat split; try assumption.
      constructor.
      * unfold root_set_store_roots_named. intros z Hin_z. contradiction.
      * exact Hroots_rest.
    + dependent destruction H.
      * destruct (IHHtyped Hsafe s Hnamed Hkeys)
        as [HR [Hroots_rest [Hnamed' Hkeys']]].
        subst R2.
        repeat split; try assumption.
        constructor.
        -- unfold root_set_store_roots_named. intros z Hin_z. contradiction.
        -- exact Hroots_rest.
      * destruct (IHHtyped Hsafe s Hnamed Hkeys)
          as [HR [Hroots_rest [Hnamed' Hkeys']]].
        subst R2.
        repeat split; try assumption.
        constructor.
        -- unfold root_set_store_roots_named. intros z Hin_z. contradiction.
        -- exact Hroots_rest.
      * destruct (IHHtyped Hsafe s Hnamed Hkeys)
          as [HR [Hroots_rest [Hnamed' Hkeys']]].
        subst R2.
        repeat split; try assumption.
        constructor.
        -- unfold root_set_store_roots_named. intros z Hin_z. contradiction.
        -- exact Hroots_rest.
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
    + dependent destruction H.
      match goal with
      | Hfields : typed_fields_roots _ _ _ _ _ _ _ [] _ _ _ _ |- _ =>
          dependent destruction Hfields
      end.
      destruct (IHHtyped Hsafe s Hnamed Hkeys)
          as [HR [Hroots_rest [Hnamed' Hkeys']]].
        subst R2.
        repeat split; try assumption.
        constructor.
        -- unfold root_set_store_roots_named. intros z Hin_z. contradiction.
        -- exact Hroots_rest.

Qed.


Lemma store_safe_function_value_call_arg_typed_roots_ctx_names :
  forall env Omega n R Sigma arg T Sigma' R' roots,
    store_safe_function_value_call_arg env arg ->
    typed_env_roots env Omega n R Sigma arg T Sigma' R' roots ->
    ctx_names Sigma' = ctx_names Sigma /\
    forall x, In x (free_vars_expr arg) -> In x (ctx_names Sigma).
Proof.
  intros env Omega n R Sigma arg T Sigma' R' roots Hsafe Htyped.
  destruct Hsafe as [| lit | y | fname fdef Hin Hname Hsummary | name lts tys sdef Hlookup Hbounds];
    dependent destruction Htyped; simpl;
    try solve [split; [reflexivity | intros x Hin; contradiction]];
    try solve [split; [reflexivity | intros x Hin; inversion Hin]].
  all: try match goal with
  | Hconsume : sctx_consume_path ?Sigma0 ?y0 [] = infer_ok ?Sigma1,
    Hplace : typed_place_env_structural _ ?Sigma0 (PVar ?y0) _
    |- ctx_names ?Sigma1 = ctx_names ?Sigma0 /\ _ =>
      split;
      [ pose proof (sctx_consume_path_same_bindings _ _ _ _ Hconsume) as Hsame;
        exact (sctx_same_bindings_names_alpha _ _ Hsame)
      | intros x Hin; inversion Hin as [Heq | Hnil]; [subst x | contradiction];
        inversion Hplace; subst; eapply sctx_lookup_in_ctx_names; eassumption ]
  | Hplace : typed_place_env_structural _ ?Sigma0 (PVar ?y0) _
    |- ctx_names ?Sigma0 = ctx_names ?Sigma0 /\ _ =>
      split;
      [ reflexivity
      | intros x Hin; inversion Hin as [Heq | Hnil]; [subst x | contradiction];
        inversion Hplace; subst; eapply sctx_lookup_in_ctx_names; eassumption ]
  end.
  all: try match goal with
  | Hfields : typed_fields_roots _ _ _ _ _ _ _ [] _ _ _ _ |- _ =>
      split;
      [ eapply typed_fields_roots_empty_literal_ctx_names; exact Hfields
      | intros x Hfalse; contradiction ]
  end.
  all: split; [reflexivity | intros x Hfalse; contradiction].
Qed.

Lemma store_safe_function_value_call_args_typed_roots_free_vars_ctx_names :
  forall env Omega n R Sigma args ps Sigma' R' arg_roots,
    store_safe_function_value_call_args env args ->
    typed_args_roots env Omega n R Sigma args ps Sigma' R' arg_roots ->
    forall x, In x (args_free_vars_ts args) -> In x (ctx_names Sigma).
Proof.
  intros env Omega n R Sigma args ps Sigma' R' arg_roots Hsafe Htyped.
  revert Hsafe.
  induction Htyped as
    [R0 Sigma0
    | R0 R1 R2 Sigma0 Sigma1 Sigma2 arg rest p ps0 T_arg roots
        roots_rest Htyped_arg Hcompat Htyped_rest IH];
    intros Hsafe x Hin; dependent destruction Hsafe; simpl in Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (store_safe_function_value_call_arg_typed_roots_ctx_names
        env Omega n R0 Sigma0 arg T_arg Sigma1 R1 roots H Htyped_arg)
        as [_ Hfree].
      exact (Hfree x Hin).
    + destruct (store_safe_function_value_call_arg_typed_roots_ctx_names
        env Omega n R0 Sigma0 arg T_arg Sigma1 R1 roots H Htyped_arg)
        as [Hnames _].
      rewrite <- Hnames.
      eapply IH; eassumption.
Qed.


Lemma store_safe_function_value_call_arg_typed_roots_remove_unused_key :
  forall env Omega n R Sigma arg T Sigma' R' roots x,
    store_safe_function_value_call_arg env arg ->
    typed_env_roots env Omega n R Sigma arg T Sigma' R' roots ->
    ~ In x (free_vars_expr arg) ->
    typed_env_roots env Omega n (root_env_remove x R) Sigma arg T
      Sigma' (root_env_remove x R') roots.
Proof.
  intros env Omega n R Sigma arg T Sigma' R' roots x Hsafe Htyped Hfree.
  destruct Hsafe as [| lit | y | fname fdef Hin Hname Hsummary | name lts tys sdef Hlookup Hbounds];
    dependent destruction Htyped; simpl in Hfree;
    try solve [constructor; eauto].
  - assert (Hyx : y <> x).
    { intros Heq. subst y. apply Hfree. simpl. left. reflexivity. }
    eapply TER_Var_Copy; eauto.
    rewrite root_env_lookup_remove_neq by (intro Heq; apply Hyx; symmetry; exact Heq). exact H1.
  - assert (Hyx : y <> x).
    { intros Heq. subst y. apply Hfree. simpl. left. reflexivity. }
    eapply TER_Var_Move; eauto.
    rewrite root_env_lookup_remove_neq by (intro Heq; apply Hyx; symmetry; exact Heq). exact H2.
  - match goal with
    | Hfields : typed_fields_roots _ _ _ _ _ _ _ [] _ _ _ _ |- _ =>
        dependent destruction Hfields
    end.
    eapply TER_Struct; eauto.
    rewrite <- x. constructor.
Qed.

Lemma store_safe_function_value_call_args_typed_roots_remove_unused_key :
  forall env Omega n R Sigma args ps Sigma' R' arg_roots x,
    store_safe_function_value_call_args env args ->
    typed_args_roots env Omega n R Sigma args ps Sigma' R' arg_roots ->
    ~ In x (args_free_vars_ts args) ->
    typed_args_roots env Omega n (root_env_remove x R) Sigma args ps
      Sigma' (root_env_remove x R') arg_roots.
Proof.
  intros env Omega n R Sigma args ps Sigma' R' arg_roots x Hsafe Htyped.
  revert Hsafe x.
  induction Htyped as
    [R0 Sigma0
    | R0 R1 R2 Sigma0 Sigma1 Sigma2 arg rest p ps0 T_arg roots
        roots_rest Htyped_arg Hcompat Htyped_rest IH];
    intros Hsafe x Hfree; dependent destruction Hsafe.
  - constructor.
  - destruct (args_free_vars_ts_cons_notin x arg rest Hfree)
      as [Hfree_arg Hfree_rest].
    econstructor.
    + eapply store_safe_function_value_call_arg_typed_roots_remove_unused_key;
        eassumption.
    + exact Hcompat.
    + eapply IH; eassumption.
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

