From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyFrameScopeReady.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_frame_scope_remove_non_param_after_same_bindings :
  forall ps Σ_body Σ_after s frame x,
    In x (ctx_names Σ_body) ->
    store_frame_static_fresh Σ_body frame ->
    store_frame_scope ps Σ_body s frame ->
    store_no_shadow s ->
    ~ In x (ctx_names (params_ctx ps)) ->
    sctx_same_bindings Σ_after (sctx_remove x Σ_body) ->
    store_frame_scope ps Σ_after (store_remove x s) frame.
Proof.
  intros ps Σ_body Σ_after s frame x Hin Hfresh Hscope Hshadow Hnotin Hsame.
  eapply store_frame_scope_same_names.
  - symmetry. apply sctx_same_bindings_names_alpha. exact Hsame.
  - eapply store_frame_scope_remove_non_param_sctx_remove; eassumption.
Qed.

Lemma sctx_same_bindings_params_ctx_names :
  forall ps Σ,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    ctx_names Σ = ctx_names (params_ctx ps).
Proof.
  intros ps Σ Hsame.
  pose proof (sctx_same_bindings_names_alpha
                (sctx_of_ctx (params_ctx ps)) Σ Hsame) as Hnames.
  unfold sctx_of_ctx in Hnames. exact Hnames.
Qed.

Lemma store_frame_scope_no_local_under_params :
  forall ps Σ se s_param frame,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    ~ In (se_name se) (ctx_names (params_ctx ps)) ->
    In (se_name se) (ctx_names Σ) ->
    store_frame_scope ps Σ (se :: s_param) frame ->
    False.
Proof.
  intros ps Σ se s_param frame Hsame Hnotin HinΣ _.
  apply Hnotin.
  rewrite <- (sctx_same_bindings_params_ctx_names ps Σ Hsame).
  exact HinΣ.
Qed.

Lemma store_remove_params_cleanup_excludes :
  forall ps s_body frame R roots v,
    store_param_scope ps s_body frame ->
    store_roots_within R s_body ->
    value_roots_within roots v ->
    store_no_shadow s_body ->
    NoDup (ctx_names (params_ctx ps)) ->
    roots_exclude_params ps roots ->
    root_env_excludes_params ps R ->
    exists locals,
      store_remove_params ps s_body = locals ++ frame /\
      value_refs_exclude_params ps v /\
      store_refs_exclude_params ps (store_remove_params ps s_body).
Proof.
  intros ps s_body frame R roots v Hscope Hstore Hvalue Hshadow Hnodup
    Hexclude_roots Hexclude_env.
  destruct (store_remove_params_store_param_scope ps s_body frame Hscope)
    as [locals Hremoved].
  exists locals.
  repeat split.
  - exact Hremoved.
  - eapply value_roots_exclude_params; eassumption.
  - eapply store_roots_exclude_params.
    + apply store_remove_params_roots_within_same_env. exact Hstore.
    + exact Hexclude_env.
    + intros x Hin se Hse.
      eapply store_remove_params_no_param_names; eassumption.
Qed.

Lemma value_has_type_store_remove_params_excluding :
  forall ps env s v T,
    value_has_type env s v T ->
    value_refs_exclude_params ps v ->
    value_has_type env (store_remove_params ps s) v T.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros env s v T Hvalue Hexclude.
  - exact Hvalue.
  - simpl.
    apply IH.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hvalue.
      * apply Hexclude. simpl. left. reflexivity.
    + intros x Hin.
      apply Hexclude. simpl. right. exact Hin.
Qed.

Lemma store_ref_targets_preserved_remove_params_after_absent :
  forall ps env s s',
    store_ref_targets_preserved env s s' ->
    params_fresh_in_store ps s ->
    store_ref_targets_preserved env s (store_remove_params ps s').
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros env s s' Hpres Hfresh.
  - exact Hpres.
  - simpl.
    apply IH.
    + eapply store_ref_targets_preserved_remove_after_absent_root.
      * exact Hpres.
      * apply store_lookup_not_in_names.
        eapply params_fresh_in_store_head. exact Hfresh.
    + eapply params_fresh_in_store_tail. exact Hfresh.
Qed.

Lemma store_names_store_param_scope :
  forall ps s_param s,
    store_param_scope ps s_param s ->
    exists local_names,
      store_names s_param =
        local_names ++ ctx_names (params_ctx ps) ++ store_names s.
Proof.
  intros ps s_param s Hscope.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s _ _ IH].
  - exists [].
    rewrite (store_names_store_param_prefix ps s_param s Hprefix).
    reflexivity.
  - destruct IH as [local_names IH].
    exists (se_name se :: local_names).
    simpl. rewrite IH. reflexivity.
Qed.

Lemma store_remove_params_store_param_prefix :
  forall ps s_param s,
    store_param_prefix ps s_param s ->
    store_remove_params ps s_param = s.
Proof.
  intros ps s_param s Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH].
  - reflexivity.
  - simpl. rewrite ident_eqb_refl. exact IH.
Qed.

Lemma captured_params_store_typed_remove_app :
  forall env captured caps frame,
    captured_params_store_typed env captured caps ->
    store_remove_params caps (captured ++ frame) = frame.
Proof.
  intros env captured caps frame Htyped.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured caps Htyped) as Hprefix.
  pose proof (store_param_prefix_append_frame
                caps captured frame [] Hprefix) as Hprefix_frame.
  simpl in Hprefix_frame.
  eapply store_remove_params_store_param_prefix.
  exact Hprefix_frame.
Qed.

Lemma captured_params_store_typed_remove_hidden_app :
  forall env captured caps x T v frame,
    captured_params_store_typed env captured caps ->
    store_remove x
      (store_remove_params caps (captured ++ store_add x T v frame)) =
      frame.
Proof.
  intros env captured caps x T v frame Htyped.
  rewrite captured_params_store_typed_remove_app with (env := env)
    by exact Htyped.
  apply store_remove_store_add_same.
Qed.

Lemma store_remove_params_store_frame_scope_exact :
  forall ps Σ s_param frame,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    store_param_scope ps s_param frame ->
    store_frame_scope ps Σ s_param frame ->
    store_remove_params ps s_param = frame.
Proof.
  intros ps Σ s_param frame Hsame Hparam_scope Hframe_scope.
  induction Hframe_scope as
    [s_param frame Hprefix
    | se s_param frame Hnotin HinΣ Hframe_scope_tail IH].
  - eapply store_remove_params_store_param_prefix. exact Hprefix.
  - exfalso.
    apply Hnotin.
    rewrite <- (sctx_same_bindings_params_ctx_names ps Σ Hsame).
    exact HinΣ.
Qed.

Lemma store_typed_remove_params_store_param_prefix :
  forall env ps s_param s Σ,
    store_typed env s Σ ->
    store_param_prefix ps s_param s ->
    store_typed env (store_remove_params ps s_param) Σ.
Proof.
  intros env ps s_param s Σ Htyped Hprefix.
  rewrite (store_remove_params_store_param_prefix ps s_param s Hprefix).
  exact Htyped.
Qed.
