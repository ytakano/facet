From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyHiddenFrameStrip.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition params_fresh_in_store (ps : list param) (s : store) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    ~ In x (store_names s).

Lemma ctx_names_params_ctx_apply_lt_params :
  forall σ ps,
    ctx_names (params_ctx (apply_lt_params σ ps)) =
    ctx_names (params_ctx ps).
Proof.
  intros σ ps.
  induction ps as [| p ps IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma apply_lt_params_length :
  forall σ ps,
    List.length (apply_lt_params σ ps) = List.length ps.
Proof.
  intros σ ps.
  unfold apply_lt_params.
  rewrite length_map. reflexivity.
Qed.

Lemma params_fresh_in_store_apply_lt_params :
  forall σ ps s,
    params_fresh_in_store ps s ->
    params_fresh_in_store (apply_lt_params σ ps) s.
Proof.
  unfold params_fresh_in_store.
  intros σ ps s Hfresh x Hin.
  rewrite ctx_names_params_ctx_apply_lt_params in Hin.
  exact (Hfresh x Hin).
Qed.

Lemma params_ctx_names_nodup_apply_lt_params :
  forall σ ps,
    NoDup (ctx_names (params_ctx ps)) ->
    NoDup (ctx_names (params_ctx (apply_lt_params σ ps))).
Proof.
  intros σ ps Hnodup.
  rewrite ctx_names_params_ctx_apply_lt_params.
  exact Hnodup.
Qed.

Lemma alpha_rename_fn_def_params_fresh_in_store :
  forall s f fr used',
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    params_fresh_in_store (fn_params fr) s.
Proof.
  unfold params_fresh_in_store.
  intros s f fr used' Hrename x Hin.
  eapply alpha_rename_fn_def_params_fresh_used.
  - exact Hrename.
  - exact Hin.
Qed.

Lemma alpha_rename_fn_def_params_nodup_ctx_names :
  forall s f fr used',
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params fr))).
Proof.
  intros s f fr used' Hrename.
  eapply alpha_rename_fn_def_params_nodup.
  exact Hrename.
Qed.

Lemma params_fresh_in_store_tail :
  forall p ps s,
    params_fresh_in_store (p :: ps) s ->
    params_fresh_in_store ps s.
Proof.
  unfold params_fresh_in_store.
  intros p ps s Hfresh x Hin.
  apply Hfresh. simpl. right. exact Hin.
Qed.

Lemma params_fresh_in_store_head :
  forall p ps s,
    params_fresh_in_store (p :: ps) s ->
    ~ In (param_name p) (store_names s).
Proof.
  unfold params_fresh_in_store.
  intros p ps s Hfresh.
  apply Hfresh. simpl. left. reflexivity.
Qed.

Lemma params_ctx_names_nodup_tail :
  forall p ps,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    NoDup (ctx_names (params_ctx ps)).
Proof.
  intros p ps Hnodup.
  simpl in Hnodup. inversion Hnodup; subst. assumption.
Qed.

Lemma params_ctx_names_nodup_head_not_tail :
  forall p ps,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    ~ In (param_name p) (ctx_names (params_ctx ps)).
Proof.
  intros p ps Hnodup.
  simpl in Hnodup. inversion Hnodup; subst. assumption.
Qed.

Lemma store_typed_names :
  forall env s Σ,
    store_typed env s Σ ->
    store_names s = ctx_names Σ.
Proof.
  intros env s Σ Htyped.
  induction Htyped as [| se ce s_tail Σ_tail Hentry _ IH].
  - reflexivity.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname _].
    simpl. rewrite Hname, IH. reflexivity.
Qed.

Lemma store_lookup_not_in_names :
  forall x s,
    ~ In x (store_names s) ->
    store_lookup x s = None.
Proof.
  intros x s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - apply IH.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_lookup_none_not_in_names :
  forall x s,
    store_lookup x s = None ->
    ~ In x (store_names s).
Proof.
  intros x s Hlookup.
  induction s as [| se rest IH]; simpl in *.
  - intros Hin. exact Hin.
  - destruct (ident_eqb x (se_name se)) eqn:Heq; try discriminate.
    intros [Hin | Hin].
    + subst x. rewrite ident_eqb_refl in Heq. discriminate.
    + apply (IH Hlookup Hin).
Qed.

Lemma check_make_closure_captures_exact_sctx_params_fresh_in_store :
  forall env Ω s Σ captures caps captured_tys,
    store_typed env s Σ ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    params_fresh_in_store caps s.
Proof.
  intros env Ω s Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys
    Hstore Hcheck;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - unfold params_fresh_in_store. intros y Hin. contradiction.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    unfold params_fresh_in_store.
    intros y Hin.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + subst y.
      intros Hin_store.
      apply (sctx_lookup_none_not_in_names (param_name cap) Σ Hcap_lookup).
      rewrite (store_typed_names env s Σ Hstore) in Hin_store.
      exact Hin_store.
    + eapply IH.
      * exact Hstore.
      * exact Hrest.
      * exact Hin.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_base_params_fresh_in_store :
  forall env Ω s Σ captures caps captured_tys,
    store_typed env s Σ ->
    check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps = infer_ok captured_tys ->
    params_fresh_in_store caps s.
Proof.
  intros env Ω s Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys
    Hstore Hcheck;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - unfold params_fresh_in_store. intros y Hin. contradiction.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest | err] eqn:Hrest;
      try discriminate.
    injection Hcheck as <-.
    unfold params_fresh_in_store.
    intros y Hin.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + subst y.
      intros Hin_store.
      apply (sctx_lookup_none_not_in_names (param_name cap) Σ Hcap_lookup).
      rewrite (store_typed_names env s Σ Hstore) in Hin_store.
      exact Hin_store.
    + eapply IH.
      * exact Hstore.
      * exact Hrest.
      * exact Hin.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_params_fresh_in_store :
  forall env Ω s Σ captures caps env_lt captured_tys,
    store_typed env s Σ ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    params_fresh_in_store caps s.
Proof.
  intros env Ω s Σ captures caps env_lt captured_tys Hstore Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  eapply check_make_closure_captures_exact_sctx_with_env_base_params_fresh_in_store;
    eassumption.
Qed.

Inductive eval_args_values_have_types
    (env : global_env) (Ω : outlives_ctx) (s : store)
    : list value -> list param -> Prop :=
  | AHT_Nil :
      eval_args_values_have_types env Ω s [] []
  | AHT_Cons : forall v vs p ps T_actual,
      value_has_type env s v T_actual ->
      ty_compatible Ω T_actual (param_ty p) ->
      eval_args_values_have_types env Ω s vs ps ->
      eval_args_values_have_types env Ω s (v :: vs) (p :: ps).

Lemma eval_args_values_have_types_length :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    List.length vs = List.length ps.
Proof.
  intros env Ω s vs ps Hargs.
  induction Hargs; simpl; congruence.
Qed.

Lemma eval_args_values_have_types_store_preserved :
  forall env Ω s s' vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_ref_targets_preserved env s s' ->
    eval_args_values_have_types env Ω s' vs ps.
Proof.
  intros env Ω s s' vs ps Hargs Hpres.
  induction Hargs as [| v vs p ps T_actual Hvalue Hcompat _ IH].
  - constructor.
  - eapply AHT_Cons with (T_actual := T_actual).
    + eapply value_has_type_store_preserved; eassumption.
    + exact Hcompat.
    + exact IH.
Qed.

Lemma eval_args_values_have_types_apply_lt_params_inv :
  forall env Ω s vs σ ps,
    eval_args_values_have_types env Ω s vs (apply_lt_params σ ps) ->
    eval_args_values_have_types env Ω s vs ps.
Proof.
  intros env Ω s vs σ ps.
  revert vs.
  induction ps as [| p ps IH]; intros vs Hargs; simpl in Hargs.
  - inversion Hargs; subst. constructor.
  - inversion Hargs as [| v vs' p_subst ps_subst T_actual Hvalue Hcompat Htail];
      subst; clear Hargs.
    simpl in Hcompat.
    eapply AHT_Cons with (T_actual := param_ty p).
    + eapply VHT_LifetimeEquiv.
      * eapply value_has_type_compatible.
        -- exact Hvalue.
        -- exact Hcompat.
      * apply ty_lifetime_equiv_sym.
        apply ty_lifetime_equiv_apply_lt_ty.
    + apply ty_compatible_refl.
    + apply IH. exact Htail.
Qed.

Lemma eval_args_values_have_types_params_alpha :
  forall env Ω s vs ps psr,
    params_alpha ps psr ->
    eval_args_values_have_types env Ω s vs ps ->
    eval_args_values_have_types env Ω s vs psr.
Proof.
  intros env Ω s vs ps psr Halpha Hargs.
  revert vs Hargs.
  induction Halpha as [| p pr ps psr Hshape Halpha IH];
    intros vs Hargs.
  - inversion Hargs; subst. constructor.
  - inversion Hargs as [| v vs_tail p0 ps0 T_actual Hv Hcompat Htail];
      subst; clear Hargs.
    destruct Hshape as [_ Hty].
    eapply AHT_Cons with (T_actual := T_actual).
    + exact Hv.
    + rewrite <- Hty. exact Hcompat.
    + apply IH. exact Htail.
Qed.

Lemma alpha_rename_fn_def_call_bind_params_premises :
  forall env Ω s vs σ f fr used',
    eval_args_values_have_types env Ω s vs
      (apply_lt_params σ (fn_params f)) ->
    same_fn_shape f fr ->
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    NoDup (ctx_names (params_ctx (apply_lt_params σ (fn_params fr)))) /\
    params_fresh_in_store (apply_lt_params σ (fn_params fr)) s /\
    eval_args_values_have_types env Ω s vs
      (apply_lt_params σ (fn_params fr)).
Proof.
  intros env Ω s vs σ f fr used' Hargs Hshape Hrename.
  destruct Hshape as [_ [_ Hparams_alpha]].
  repeat split.
  - apply params_ctx_names_nodup_apply_lt_params.
    eapply alpha_rename_fn_def_params_nodup_ctx_names.
    exact Hrename.
  - apply params_fresh_in_store_apply_lt_params.
    eapply alpha_rename_fn_def_params_fresh_in_store.
    exact Hrename.
  - eapply eval_args_values_have_types_params_alpha.
    + apply params_alpha_apply_lt_compat.
      exact Hparams_alpha.
    + exact Hargs.
Qed.

Lemma alpha_rename_fn_def_generic_call_bind_params_premises :
  forall env Ω s vs σ type_args f fr used',
    eval_args_values_have_types env Ω s vs
      (apply_lt_params σ (apply_type_params type_args (fn_params f))) ->
    same_fn_shape f fr ->
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    NoDup
      (ctx_names
        (params_ctx
          (apply_lt_params σ (apply_type_params type_args (fn_params fr))))) /\
    params_fresh_in_store
      (apply_lt_params σ (apply_type_params type_args (fn_params fr))) s /\
    eval_args_values_have_types env Ω s vs
      (apply_lt_params σ (apply_type_params type_args (fn_params fr))).
Proof.
  intros env Ω s vs σ type_args f fr used' Hargs Hshape Hrename.
  destruct Hshape as [_ [_ Hparams_alpha]].
  repeat split.
  - rewrite params_ctx_apply_lt_params.
    rewrite ctx_names_apply_lt_ctx.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_nodup_ctx_names.
    exact Hrename.
  - apply params_fresh_in_store_apply_lt_params.
    unfold params_fresh_in_store.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_fresh_in_store.
    exact Hrename.
  - eapply eval_args_values_have_types_params_alpha.
    + apply params_alpha_apply_lt_compat.
      apply params_alpha_apply_type_compat.
      exact Hparams_alpha.
    + exact Hargs.
Qed.
