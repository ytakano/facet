From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyProvenanceReady.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition root_env_covers_sctx (Σ : sctx) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names Σ) ->
    exists roots, root_env_lookup x R = Some roots.

Definition root_env_covers_params (ps : list param) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    exists roots, root_env_lookup x R = Some roots.

Lemma root_env_covers_sctx_equiv :
  forall Σ R R',
    root_env_equiv R R' ->
    root_env_covers_sctx Σ R ->
    root_env_covers_sctx Σ R'.
Proof.
  unfold root_env_covers_sctx.
  intros Σ R R' Heq Hcovers x Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
    as [roots' [Hlookup' _]].
  exists roots'. exact Hlookup'.
Qed.

Lemma root_env_covers_params_equiv :
  forall ps R R',
    root_env_equiv R R' ->
    root_env_covers_params ps R ->
    root_env_covers_params ps R'.
Proof.
  unfold root_env_covers_params.
  intros ps R R' Heq Hcovers x Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
    as [roots' [Hlookup' _]].
  exists roots'. exact Hlookup'.
Qed.

Lemma root_env_covers_params_app_inv_l :
  forall ps caps R,
    root_env_covers_params (ps ++ caps) R ->
    root_env_covers_params ps R.
Proof.
  unfold root_env_covers_params.
  intros ps caps R Hcovers x Hin.
  apply Hcovers.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. left. exact Hin.
Qed.

Lemma root_env_covers_params_app_inv_r :
  forall ps caps R,
    root_env_covers_params (ps ++ caps) R ->
    root_env_covers_params caps R.
Proof.
  unfold root_env_covers_params.
  intros ps caps R Hcovers x Hin.
  apply Hcovers.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_covers_params_app :
  forall ps caps R,
    root_env_covers_params ps R ->
    root_env_covers_params caps R ->
    root_env_covers_params (ps ++ caps) R.
Proof.
  unfold root_env_covers_params.
  intros ps caps R Hcovers_ps Hcovers_caps x Hin.
  rewrite params_ctx_app, ctx_names_app in Hin.
  apply in_app_or in Hin as [Hin | Hin].
  - apply Hcovers_ps. exact Hin.
  - apply Hcovers_caps. exact Hin.
Qed.

Lemma captured_params_store_typed_empty_root_env_covers :
  forall env captured caps,
    captured_params_store_typed env captured caps ->
    root_env_covers_params caps (empty_root_env_for_store captured).
Proof.
  intros env captured caps Htyped.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured caps Htyped) as Hprefix.
  unfold root_env_covers_params.
  intros x Hin.
  exists [].
  apply root_env_lookup_empty_root_env_for_store.
  rewrite (store_names_store_param_prefix caps captured [] Hprefix).
  rewrite app_nil_r. exact Hin.
Qed.

Lemma empty_root_env_for_captured_params_equiv :
  forall env captured caps,
    captured_params_store_typed env captured caps ->
    root_env_equiv (empty_root_env_for_store captured)
      (root_env_add_params_roots caps (repeat [] (List.length caps)) []).
Proof.
  intros env captured caps Htyped.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured caps Htyped) as Hprefix.
  rewrite (empty_root_env_for_store_param_prefix caps captured [] Hprefix).
  simpl. apply root_env_equiv_refl.
Qed.

Lemma captured_params_store_typed_empty_root_env_app_covers :
  forall env captured caps R_tail,
    captured_params_store_typed env captured caps ->
    root_env_covers_params caps
      (empty_root_env_for_store captured ++ R_tail).
Proof.
  intros env captured caps R_tail Htyped.
  unfold root_env_covers_params.
  intros x Hin.
  destruct (captured_params_store_typed_empty_root_env_covers
              env captured caps Htyped x Hin) as [roots Hlookup].
  exists roots. eapply root_env_lookup_app_left. exact Hlookup.
Qed.

Definition roots_exclude_params (ps : list param) (roots : root_set) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    roots_exclude x roots.

Definition root_env_excludes_params (ps : list param) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    root_env_excludes x R.

Lemma roots_exclude_params_app_inv_l :
  forall ps caps roots,
    roots_exclude_params (ps ++ caps) roots ->
    roots_exclude_params ps roots.
Proof.
  unfold roots_exclude_params.
  intros ps caps roots Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. left. exact Hin.
Qed.

Lemma roots_exclude_params_app_inv_r :
  forall ps caps roots,
    roots_exclude_params (ps ++ caps) roots ->
    roots_exclude_params caps roots.
Proof.
  unfold roots_exclude_params.
  intros ps caps roots Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_excludes_params_app_inv_l :
  forall ps caps R,
    root_env_excludes_params (ps ++ caps) R ->
    root_env_excludes_params ps R.
Proof.
  unfold root_env_excludes_params.
  intros ps caps R Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. left. exact Hin.
Qed.

Lemma root_env_excludes_params_app_inv_r :
  forall ps caps R,
    root_env_excludes_params (ps ++ caps) R ->
    root_env_excludes_params caps R.
Proof.
  unfold root_env_excludes_params.
  intros ps caps R Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. right. exact Hin.
Qed.

Lemma empty_root_env_for_store_params_fresh_lookup_none :
  forall ps s x,
    params_fresh_in_store ps s ->
    In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (empty_root_env_for_store s) = None.
Proof.
  intros ps s x Hfresh Hin.
  apply root_env_lookup_empty_root_env_for_store_none.
  exact (Hfresh x Hin).
Qed.

Lemma root_env_excludes_params_empty_root_env_for_store :
  forall ps s,
    root_env_excludes_params ps (empty_root_env_for_store s).
Proof.
  unfold root_env_excludes_params, root_env_excludes, roots_exclude.
  intros ps s x _ y roots Hlookup _ Hin.
  assert (Hy_names : In y (store_names s)).
  { rewrite <- root_env_names_empty_root_env_for_store.
    eapply root_env_lookup_some_in_names. exact Hlookup. }
  rewrite root_env_lookup_empty_root_env_for_store in Hlookup
    by exact Hy_names.
  inversion Hlookup; subst roots.
  contradiction.
Qed.

Lemma root_set_no_store_of_sctx_named_excludes_params :
  forall ps Σ roots,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    root_set_sctx_roots_named roots Σ ->
    roots_exclude_params ps roots ->
    root_set_no_store roots.
Proof.
  unfold root_set_no_store, roots_exclude_params, roots_exclude.
  intros ps Σ roots Hsame Hnamed Hexclude z Hin.
  assert (Hz_ctx : In z (ctx_names Σ)).
  { apply Hnamed. exact Hin. }
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha (params_ctx ps) Σ Hsame).
    reflexivity. }
  rewrite Hnames in Hz_ctx.
  eapply Hexclude; eassumption.
Qed.

Lemma roots_exclude_params_rename :
  forall rho ps psr roots rootsr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    (forall x y,
      In x (ctx_names (params_ctx ps)) ->
      In (RStore y) roots ->
      y <> x ->
      lookup_rename y rho <> lookup_rename x rho) ->
    roots_exclude_params ps roots ->
    roots_exclude_params psr rootsr.
Proof.
  unfold roots_exclude_params.
  intros rho ps psr roots rootsr Halpha Hnodup Heq Hnocoll Hexcl xr Hinr.
  destruct (ctx_alpha_renamed_name_preimage rho
              (sctx_of_ctx (params_ctx ps))
              (sctx_of_ctx (params_ctx psr)) xr Halpha Hnodup Hinr)
    as [x [Hinx Hlookup]].
  subst xr.
  eapply roots_exclude_equiv.
  - apply root_set_equiv_sym. exact Heq.
  - apply roots_exclude_rename.
    + intros y Hy Hyx. eapply Hnocoll; eassumption.
    + apply Hexcl. exact Hinx.
Qed.

Lemma root_env_excludes_params_rename :
  forall rho ps psr R Rr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    root_env_equiv Rr (root_env_rename rho R) ->
    (forall x y,
      In x (ctx_names (params_ctx ps)) ->
      In y (root_env_names R) ->
      y <> x ->
      lookup_rename y rho <> lookup_rename x rho) ->
    (forall x y roots z,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup y R = Some roots ->
      y <> x ->
      In (RStore z) roots ->
      z <> x ->
      lookup_rename z rho <> lookup_rename x rho) ->
    root_env_excludes_params ps R ->
    root_env_excludes_params psr Rr.
Proof.
  unfold root_env_excludes_params.
  intros rho ps psr R Rr Halpha Hnodup Hrn Heq Hkey_nocoll Hroot_nocoll
    Hexcl xr Hinr.
  destruct (ctx_alpha_renamed_name_preimage rho
              (sctx_of_ctx (params_ctx ps))
              (sctx_of_ctx (params_ctx psr)) xr Halpha Hnodup Hinr)
    as [x [Hinx Hlookup]].
  subst xr.
  eapply root_env_excludes_equiv.
  - apply root_env_equiv_sym. exact Heq.
  - eapply root_env_excludes_rename.
    + exact Hrn.
    + intros y Hy Hyx. eapply Hkey_nocoll; eassumption.
    + intros y roots z Hlookup_y Hyx Hin_z Hzx.
      eapply Hroot_nocoll; eassumption.
    + apply Hexcl. exact Hinx.
Qed.

Lemma roots_exclude_params_instantiate :
  forall ps rho roots,
    roots_exclude_params ps roots ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_subst_images_exclude x rho) ->
    roots_exclude_params ps (root_set_instantiate rho roots).
Proof.
  unfold roots_exclude_params.
  intros ps rho roots Hexcl Himages x Hin.
  apply root_set_instantiate_excludes_images.
  - apply Hexcl. exact Hin.
  - apply Himages. exact Hin.
Qed.

Lemma root_env_excludes_params_instantiate :
  forall ps rho R,
    root_env_excludes_params ps R ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_subst_images_exclude x rho) ->
    root_env_excludes_params ps (root_env_instantiate rho R).
Proof.
  unfold root_env_excludes_params.
  intros ps rho R Hexcl Himages x Hin.
  apply root_env_instantiate_excludes_images.
  - apply Hexcl. exact Hin.
  - apply Himages. exact Hin.
Qed.

Lemma root_env_excludes_params_app :
  forall ps R1 R2,
    root_env_excludes_params ps R1 ->
    root_env_excludes_params ps R2 ->
    root_env_excludes_params ps (R1 ++ R2).
Proof.
  unfold root_env_excludes_params.
  intros ps R1 R2 Hexcl1 Hexcl2 x Hin.
  apply root_env_excludes_app.
  - apply Hexcl1. exact Hin.
  - apply Hexcl2. exact Hin.
Qed.

Lemma roots_exclude_params_equiv :
  forall ps roots roots',
    root_set_equiv roots roots' ->
    roots_exclude_params ps roots ->
    roots_exclude_params ps roots'.
Proof.
  unfold roots_exclude_params.
  intros ps roots roots' Heq Hexcl x Hin.
  exact (roots_exclude_equiv x roots roots' Heq (Hexcl x Hin)).
Qed.

Lemma root_env_excludes_params_equiv :
  forall ps R R',
    root_env_equiv R R' ->
    root_env_excludes_params ps R ->
    root_env_excludes_params ps R'.
Proof.
  unfold root_env_excludes_params.
  intros ps R R' Heq Hexcl x Hin.
  exact (root_env_excludes_equiv x R R' Heq (Hexcl x Hin)).
Qed.

Lemma roots_exclude_params_rename_from_typed_support :
  forall rho ps psr Σ Σr roots rootsr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    ctx_alpha rho Σ Σr ->
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_set_sctx_roots_named roots Σ ->
    roots_exclude_params ps roots ->
    roots_exclude_params psr rootsr.
Proof.
  intros rho ps psr Σ Σr roots rootsr Halpha_params Halpha_out
    Hsame Hnodup Heq Hroots_named Hexcl.
  eapply roots_exclude_params_rename; try eassumption.
  intros x y Hx Hy Hyx.
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha
      (params_ctx ps) Σ Hsame). reflexivity. }
  assert (Hnodup_out : NoDup (ctx_names Σ)).
  { rewrite Hnames. exact Hnodup. }
  assert (Hnodup_ren : NoDup (ctx_names Σr)).
  { eapply ctx_alpha_nodup_names; eassumption. }
  eapply ctx_alpha_no_collision_on with (Σ := Σ) (Σr := Σr).
  - exact Halpha_out.
  - exact Hnodup_out.
  - exact Hnodup_ren.
  - rewrite Hnames. exact Hx.
  - apply Hroots_named. exact Hy.
  - exact Hyx.
Qed.

Lemma root_env_excludes_params_rename_from_typed_support :
  forall rho ps psr Σ Σr R Rr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    ctx_alpha rho Σ Σr ->
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    root_env_excludes_params ps R ->
    root_env_excludes_params psr Rr.
Proof.
  intros rho ps psr Σ Σr R Rr Halpha_params Halpha_out Hsame Hnodup
    Hrn Heq Hkeys Hroots Hexcl.
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha
      (params_ctx ps) Σ Hsame). reflexivity. }
  assert (Hnodup_out : NoDup (ctx_names Σ)).
  { rewrite Hnames. exact Hnodup. }
  assert (Hnodup_ren : NoDup (ctx_names Σr)).
  { eapply ctx_alpha_nodup_names; eassumption. }
  assert (Hnocoll : rename_no_collision_on rho (ctx_names Σ)).
  { eapply ctx_alpha_no_collision_on; eassumption. }
  eapply root_env_excludes_params_rename; try eassumption.
  - intros x y Hx Hy Hyx.
    eapply Hnocoll.
    + rewrite Hnames. exact Hx.
    + apply Hkeys. exact Hy.
    + exact Hyx.
  - intros x y roots z Hx Hlookup Hyx Hz Hzx.
    eapply Hnocoll.
    + rewrite Hnames. exact Hx.
    + eapply Hroots; eassumption.
    + exact Hzx.
Qed.

Lemma rename_no_collision_on_root_env_names_from_typed_support :
  forall rho ps psr Σ R,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_sctx_keys_named R Σ ->
    rename_no_collision_on rho (root_env_names R).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho ps psr Σ R Halpha Hsame Hnodup Hkeys x Hx y Hy Hyx.
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha
      (params_ctx ps) Σ Hsame). reflexivity. }
  assert (Hnodup_ren :
    NoDup (ctx_names (sctx_of_ctx (params_ctx psr)))).
  { eapply ctx_alpha_nodup_names.
    - exact Halpha.
    - unfold sctx_of_ctx. exact Hnodup. }
  eapply ctx_alpha_no_collision_on.
  - exact Halpha.
  - unfold sctx_of_ctx. exact Hnodup.
  - exact Hnodup_ren.
  - unfold sctx_of_ctx. rewrite <- Hnames. apply Hkeys. exact Hx.
  - unfold sctx_of_ctx. rewrite <- Hnames. apply Hkeys. exact Hy.
  - exact Hyx.
Qed.

Lemma root_env_store_roots_named_excludes_params :
  forall ps R s,
    root_env_store_roots_named R s ->
    params_fresh_in_store ps s ->
    root_env_excludes_params ps R.
Proof.
  unfold root_env_store_roots_named, params_fresh_in_store,
    root_env_excludes_params, root_env_excludes, roots_exclude.
  intros ps R s Hnamed Hfresh x Hparam y roots Hlookup Hyx Hin.
  apply (Hfresh x Hparam).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_roots_named_excludes_name :
  forall R s x,
    root_env_store_roots_named R s ->
    ~ In x (store_names s) ->
    root_env_excludes x R.
Proof.
  unfold root_env_store_roots_named, root_env_excludes, roots_exclude.
  intros R s x Hnamed Hfresh y roots Hlookup Hyx Hin.
  apply Hfresh.
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_lookup_excludes_name :
  forall R s x,
    root_env_store_keys_named R s ->
    ~ In x (store_names s) ->
    root_env_lookup x R = None.
Proof.
  intros R s x Hnamed Hfresh.
  destruct (root_env_lookup x R) as [roots |] eqn:Hlookup;
    try reflexivity.
  exfalso. apply Hfresh.
  eapply root_env_keys_named_lookup; eassumption.
Qed.

Lemma root_set_store_roots_named_excludes_params :
  forall ps roots s,
    root_set_store_roots_named roots s ->
    params_fresh_in_store ps s ->
    roots_exclude_params ps roots.
Proof.
  unfold root_set_store_roots_named, params_fresh_in_store,
    roots_exclude_params, roots_exclude.
  intros ps roots s Hnamed Hfresh x Hparam Hin.
  apply (Hfresh x Hparam).
  apply Hnamed. exact Hin.
Qed.

Lemma root_set_store_roots_named_excludes_name :
  forall roots s x,
    root_set_store_roots_named roots s ->
    ~ In x (store_names s) ->
    roots_exclude x roots.
Proof.
  unfold root_set_store_roots_named, roots_exclude.
  intros roots s x Hnamed Hfresh Hin.
  apply Hfresh.
  apply Hnamed. exact Hin.
Qed.

Lemma root_subst_of_params_images_exclude_names_from_store_roots :
  forall ps arg_roots names s,
    Forall (fun roots => root_set_store_roots_named roots s) arg_roots ->
    Forall (fun x => ~ In x (store_names s)) names ->
    root_subst_images_exclude_names names
      (root_subst_of_params ps arg_roots).
Proof.
  intros ps arg_roots names s Hnamed Hfresh.
  induction Hfresh as [| x names Hx Hfresh IH].
  - constructor.
  - constructor.
    + apply root_subst_of_params_images_exclude.
      eapply Forall_impl; [| exact Hnamed].
      intros roots Hroot.
      apply (root_set_store_roots_named_excludes_name roots s x).
      * exact Hroot.
      * exact Hx.
    + exact IH.
Qed.

Lemma alpha_rename_fn_def_body_root_subst_images_exclude_names_from_store_roots :
  forall f fr used' arg_roots s,
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    Forall (fun roots => root_set_store_roots_named roots s) arg_roots ->
    root_subst_images_exclude_names
      (expr_local_store_names (fn_body fr))
      (root_subst_of_params (fn_params fr) arg_roots).
Proof.
  intros f fr used' arg_roots s Hrename Hnamed.
  eapply root_subst_of_params_images_exclude_names_from_store_roots.
  - exact Hnamed.
  - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
    exact Hrename.
Qed.

Lemma root_sets_store_roots_named_excludes_params :
  forall ps roots_list s,
    Forall (fun roots => root_set_store_roots_named roots s) roots_list ->
    params_fresh_in_store ps s ->
    Forall (roots_exclude_params ps) roots_list.
Proof.
  intros ps roots_list s Hnamed Hfresh.
  induction Hnamed as [| roots roots_list Hroot Hnamed IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_excludes_params; eassumption.
    + exact IH.
Qed.

Definition value_refs_exclude_params (ps : list param) (v : value) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    value_refs_exclude_root x v.

Definition store_refs_exclude_params (ps : list param) (s : store) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    store_refs_exclude_root x s.

Definition roots_exclude_params_b (ps : list param) (roots : root_set) : bool :=
  forallb (fun x => roots_exclude_b x roots) (ctx_names (params_ctx ps)).

Definition root_env_excludes_params_b (ps : list param) (R : root_env) : bool :=
  forallb (fun x => root_env_excludes_b x R) (ctx_names (params_ctx ps)).

Lemma roots_exclude_b_sound_ts :
  forall x roots,
    roots_exclude_b x roots = true ->
    roots_exclude x roots.
Proof.
  unfold roots_exclude_b, roots_exclude.
  intros x roots Hexclude Hin.
  apply negb_true_iff in Hexclude.
  assert (existsb (root_atom_eqb (RStore x)) roots = true) as Hexists.
  { apply existsb_exists.
    exists (RStore x). split.
    - exact Hin.
    - apply root_atom_eqb_refl. }
  rewrite Hexists in Hexclude. discriminate.
Qed.

Lemma root_env_excludes_b_sound_ts :
  forall x R,
    root_env_excludes_b x R = true ->
    root_env_excludes x R.
Proof.
  unfold root_env_excludes.
  intros x R.
  induction R as [| [y roots_y] rest IH]; intros Hexclude z roots
    Hlookup Hneq; simpl in *; try discriminate.
  apply andb_true_iff in Hexclude as [Hhead Hrest].
  destruct (ident_eqb z y) eqn:Hz.
  - inversion Hlookup; subst roots_y; clear Hlookup.
    destruct (ident_eqb x y) eqn:Hxy.
    + apply ident_eqb_eq in Hxy. subst y.
      apply ident_eqb_eq in Hz. subst z.
      contradiction Hneq. reflexivity.
    + eapply roots_exclude_b_sound_ts. exact Hhead.
  - eapply IH; eassumption.
Qed.

Lemma roots_exclude_params_b_sound :
  forall ps roots,
    roots_exclude_params_b ps roots = true ->
    roots_exclude_params ps roots.
Proof.
  assert (Hnames :
    forall names roots,
      forallb (fun x => roots_exclude_b x roots) names = true ->
      forall x, In x names -> roots_exclude x roots).
  { induction names as [| y ys IH]; intros roots Hparams x Hin;
      simpl in *; try contradiction.
    apply andb_true_iff in Hparams as [Hhead Htail].
    destruct Hin as [Hin | Hin].
    - subst x. eapply roots_exclude_b_sound_ts. exact Hhead.
    - eapply IH; eassumption. }
  unfold roots_exclude_params_b, roots_exclude_params.
  intros ps roots Hparams x Hin.
  eapply Hnames; eassumption.
Qed.

Lemma root_env_excludes_params_b_sound :
  forall ps R,
    root_env_excludes_params_b ps R = true ->
    root_env_excludes_params ps R.
Proof.
  assert (Hnames :
    forall names R,
      forallb (fun x => root_env_excludes_b x R) names = true ->
      forall x, In x names -> root_env_excludes x R).
  { induction names as [| y ys IH]; intros R Hparams x Hin;
      simpl in *; try contradiction.
    apply andb_true_iff in Hparams as [Hhead Htail].
    destruct Hin as [Hin | Hin].
    - subst x. eapply root_env_excludes_b_sound_ts. exact Hhead.
    - eapply IH; eassumption. }
  unfold root_env_excludes_params_b, root_env_excludes_params.
  intros ps R Hparams x Hin.
  eapply Hnames; eassumption.
Qed.

Lemma root_env_covers_sctx_update :
  forall Σ R x roots,
    root_env_covers_sctx Σ R ->
    root_env_covers_sctx Σ (root_env_update x roots R).
Proof.
  intros Σ R x roots Hcovers y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots.
    eapply root_env_lookup_update_eq. exact Hlookup.
  - exists roots_old.
    rewrite root_env_lookup_update_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_sctx_add :
  forall Σ R x roots,
    root_env_covers_sctx Σ R ->
    root_env_covers_sctx Σ (root_env_add x roots R).
Proof.
  intros Σ R x roots Hcovers y Hy.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots. apply root_env_lookup_add_eq.
  - destruct (Hcovers y Hy) as [roots_old Hlookup].
    exists roots_old.
    rewrite root_env_lookup_add_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_sctx_remove_non_name :
  forall Σ R x,
    root_env_covers_sctx Σ R ->
    ~ In x (ctx_names Σ) ->
    root_env_covers_sctx Σ (root_env_remove x R).
Proof.
  intros Σ R x Hcovers Hnotin y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  exists roots_old.
  rewrite root_env_lookup_remove_neq.
  - exact Hlookup.
  - intros Heq. subst y. contradiction.
Qed.

Lemma root_env_covers_sctx_lookup_none_not_in :
  forall Σ R x,
    root_env_covers_sctx Σ R ->
    root_env_lookup x R = None ->
    ~ In x (ctx_names Σ).
Proof.
  intros Σ R x Hcovers Hlookup_none Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  rewrite Hlookup_none in Hlookup. discriminate.
Qed.

Lemma root_env_covers_params_sctx_of_params :
  forall ps R,
    root_env_covers_params ps R ->
    root_env_covers_sctx (sctx_of_ctx (params_ctx ps)) R.
Proof.
  unfold root_env_covers_params, root_env_covers_sctx, sctx_of_ctx.
  intros ps R Hcovers x Hin.
  apply Hcovers. exact Hin.
Qed.

Lemma root_env_covers_params_update :
  forall ps R x roots,
    root_env_covers_params ps R ->
    root_env_covers_params ps (root_env_update x roots R).
Proof.
  intros ps R x roots Hcovers y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots.
    eapply root_env_lookup_update_eq. exact Hlookup.
  - exists roots_old.
    rewrite root_env_lookup_update_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_params_add :
  forall ps R x roots,
    root_env_covers_params ps R ->
    root_env_covers_params ps (root_env_add x roots R).
Proof.
  intros ps R x roots Hcovers y Hy.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots. apply root_env_lookup_add_eq.
  - destruct (Hcovers y Hy) as [roots_old Hlookup].
    exists roots_old.
    rewrite root_env_lookup_add_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_params_remove_non_param :
  forall ps R x,
    root_env_covers_params ps R ->
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_covers_params ps (root_env_remove x R).
Proof.
  intros ps R x Hcovers Hnotin y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  exists roots_old.
  rewrite root_env_lookup_remove_neq.
  - exact Hlookup.
  - intros Heq. subst y. contradiction.
Qed.

Lemma root_env_covers_params_lookup_none_not_in :
  forall ps R x,
    root_env_covers_params ps R ->
    root_env_lookup x R = None ->
    ~ In x (ctx_names (params_ctx ps)).
Proof.
  intros ps R x Hcovers Hlookup_none Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  rewrite Hlookup_none in Hlookup. discriminate.
Qed.

Lemma root_env_covers_params_add_params_roots :
  forall ps roots_list R,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length roots_list = List.length ps ->
    root_env_covers_params ps (root_env_add_params_roots ps roots_list R).
Proof.
  intros ps roots_list R Hnodup Hlen x Hin.
  eapply root_env_add_params_roots_covers_lookup; eassumption.
Qed.

Lemma call_param_root_env_covers_params :
  forall ps roots_list R_tail,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length roots_list = List.length ps ->
    root_env_covers_params ps (call_param_root_env ps roots_list R_tail).
Proof.
  intros ps roots_list R_tail Hnodup Hlen.
  unfold call_param_root_env.
  apply root_env_covers_params_add_params_roots.
  - exact Hnodup.
  - exact Hlen.
Qed.

Lemma captured_call_runtime_root_env_covers_params_captures :
  forall env captured caps ps arg_roots R_tail,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length arg_roots = List.length ps ->
    captured_params_store_typed env captured caps ->
    root_env_covers_params (ps ++ caps)
      (call_param_root_env ps arg_roots
        (empty_root_env_for_store captured ++ R_tail)).
Proof.
  intros env captured caps ps arg_roots R_tail Hnodup Hlen Hcaptured.
  apply root_env_covers_params_app.
  - apply call_param_root_env_covers_params; assumption.
  - unfold root_env_covers_params.
    intros x Hin_caps.
    assert (Hident_dec : forall a b : ident, {a = b} + {a <> b}).
    { decide equality; [apply Nat.eq_dec | apply string_dec]. }
    destruct (in_dec Hident_dec x (ctx_names (params_ctx ps)))
      as [Hin_ps | Hnotin_ps].
    + apply call_param_root_env_covers_params; assumption.
    + destruct (captured_params_store_typed_empty_root_env_app_covers
                  env captured caps R_tail Hcaptured x Hin_caps)
        as [roots Hlookup_tail].
      exists roots.
      unfold call_param_root_env.
      rewrite root_env_add_params_roots_lookup_not_in by exact Hnotin_ps.
      rewrite root_env_lookup_remove_params_not_in by exact Hnotin_ps.
      exact Hlookup_tail.
Qed.

Lemma root_env_excludes_remove_no_shadow :
  forall x y R,
    root_env_no_shadow R ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_remove y R).
Proof.
  unfold root_env_excludes.
  intros x y R Hrn Hexcl z roots Hlookup Hneq.
  destruct (ident_eqb z y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst z.
    rewrite root_env_lookup_remove_eq_no_shadow in Hlookup; try discriminate.
    exact Hrn.
  - eapply Hexcl.
    + rewrite (root_env_lookup_remove_neq y z R) in Hlookup.
      * exact Hlookup.
      * intros Hz. subst z. rewrite ident_eqb_refl in Heq. discriminate.
    + exact Hneq.
Qed.

Lemma root_env_remove_params_preserves_excludes :
  forall ps x R,
    root_env_no_shadow R ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_remove_params ps R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros x R Hrn Hexcl; simpl.
  - exact Hexcl.
  - apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + apply root_env_excludes_remove_no_shadow; assumption.
Qed.

Lemma root_env_remove_params_preserves_excludes_params :
  forall remove_ps protected_ps R,
    root_env_no_shadow R ->
    root_env_excludes_params protected_ps R ->
    root_env_excludes_params protected_ps
      (root_env_remove_params remove_ps R).
Proof.
  intros remove_ps.
  induction remove_ps as [| p remove_ps IH];
    intros protected_ps R Hrn Hexcl; simpl.
  - exact Hexcl.
  - apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + unfold root_env_excludes_params in *.
      intros x Hin.
      apply root_env_excludes_remove_no_shadow.
      * exact Hrn.
      * apply Hexcl. exact Hin.
Qed.

Lemma root_env_remove_params_excludes_params :
  forall ps R_tail,
    root_env_no_shadow R_tail ->
    root_env_excludes_params ps R_tail ->
    root_env_excludes_params ps (root_env_remove_params ps R_tail).
Proof.
  intros ps R_tail Hrn Hexcl.
  eapply root_env_remove_params_preserves_excludes_params; eassumption.
Qed.

Lemma captured_call_runtime_args_tail_excludes_binding_params :
  forall ps caps R_args s_args,
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    params_fresh_in_store (ps ++ caps) s_args ->
    root_env_excludes_params (ps ++ caps)
      (root_env_remove_params ps R_args).
Proof.
  intros ps caps R_args s_args Hrn Hnamed Hfresh.
  eapply root_env_remove_params_preserves_excludes_params.
  - exact Hrn.
  - eapply root_env_store_roots_named_excludes_params; eassumption.
Qed.

Lemma captured_call_runtime_args_tail_fresh_names_for_fresh_call :
  forall env captured s_args R_args fdef fcall used',
    captured_call_frame_ready env captured
      (empty_root_env_for_store captured) s_args R_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env captured s_args R_args fdef fcall used'
    Hframe Hrename x Hin.
  unfold captured_call_frame_ready in Hframe.
  destruct Hframe as [_ [_ [_ [Hrn_tail [Hnamed_tail Hkeys_tail]]]]].
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_tail.
    eapply NoDup_app_right_ts. exact Hrn_tail. }
  assert (Hnamed_args :
    root_env_store_roots_named R_args (captured ++ s_args)).
  { unfold root_env_store_roots_named in *.
    intros y roots z Hlookup_args Hin_root.
    eapply Hnamed_tail.
    - assert (Hlookup_cap :
        root_env_lookup y (empty_root_env_for_store captured) = None).
      { eapply root_env_no_shadow_app_lookup_right_none; eassumption. }
      rewrite (root_env_lookup_app_right y
        (empty_root_env_for_store captured) R_args Hlookup_cap).
      exact Hlookup_args.
    - exact Hin_root. }
  assert (Hkeys_args :
    root_env_store_keys_named R_args (captured ++ s_args)).
  { unfold root_env_store_keys_named, root_env_keys_named in *.
    intros y Hin_names.
    apply Hkeys_tail.
    rewrite root_env_names_app.
    apply in_or_app. right. exact Hin_names. }
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names (captured ++ s_args))).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes; assumption.
Qed.

Lemma captured_call_runtime_root_env_binding_split_equiv :
  forall env captured ps caps arg_roots,
    captured_params_store_typed env captured caps ->
    params_fresh_in_store ps captured ->
    List.length arg_roots = List.length ps ->
    root_env_equiv
      (call_param_root_env ps arg_roots
        (empty_root_env_for_store captured))
      (call_param_root_env (ps ++ caps)
        (arg_roots ++ repeat [] (List.length caps)) []).
Proof.
  intros env captured ps caps arg_roots Hcaptured Hfresh Hlen.
  rewrite (call_param_root_env_app_roots ps caps arg_roots
             (repeat [] (List.length caps)) [] Hlen).
  unfold call_param_root_env at 1.
  rewrite (root_env_remove_params_lookup_none_self
             ps (empty_root_env_for_store captured)).
  - eapply root_env_add_params_roots_preserves_equiv.
    rewrite root_env_remove_params_empty.
    eapply empty_root_env_for_captured_params_equiv. exact Hcaptured.
  - intros x Hin.
    eapply empty_root_env_for_store_params_fresh_lookup_none; eassumption.
Qed.

Lemma captured_call_binding_runtime_root_env_equiv :
  forall env captured fdef fcall used used' arg_roots,
    alpha_rename_fn_def used fdef = (fcall, used') ->
    NoDup (ctx_names (params_ctx
      (fn_params fdef ++ fn_captures fdef))) ->
    List.length arg_roots = List.length (fn_params fdef) ->
    captured_params_store_typed env captured (fn_captures fcall) ->
    params_fresh_in_store (fn_params fcall) captured ->
    root_env_equiv
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured))
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall))).
Proof.
  intros env captured fdef fcall used used' arg_roots Hrename Hnodup
    Hlen_args Hcaptured Hfresh.
  pose proof (alpha_rename_fn_def_binding_params_alpha_ts
                used fdef fcall used' Hrename) as Halpha_binding.
  pose proof (alpha_rename_fn_def_shape used fdef fcall used' Hrename)
    as [_ [_ Halpha_params]].
  assert (Hlen_args_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Halpha_params).
    exact Hlen_args. }
  assert (Hcaps_eq :
    fn_captures fcall = fn_captures fdef).
  { rewrite <- (alpha_rename_fn_def_captures
                  used fdef fcall used' Hrename).
    reflexivity. }
  assert (Hlen_binding :
    List.length
      (arg_roots ++ repeat [] (List.length (fn_captures fdef))) =
    List.length (fn_params fdef ++ fn_captures fdef)).
  { rewrite length_app, repeat_length, length_app.
    rewrite Hlen_args. reflexivity. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall)))
      (call_param_root_env (fn_params fcall ++ fn_captures fcall)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))) [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  eapply (root_env_equiv_trans
    (call_param_root_env (fn_params fcall) arg_roots
      (empty_root_env_for_store captured))
    (call_param_root_env (fn_params fcall ++ fn_captures fcall)
      (arg_roots ++ repeat [] (List.length (fn_captures fdef))) [])
    (root_env_instantiate
      (root_subst_of_params
        (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
      (initial_root_env_for_params_origin
        (fn_params fdef ++ fn_captures fdef)
        (fn_params fcall ++ fn_captures fcall)))).
  - rewrite <- Hcaps_eq.
    eapply captured_call_runtime_root_env_binding_split_equiv;
      eassumption.
  - apply root_env_equiv_sym. exact Hinitial_inst_equiv.
Qed.

Lemma root_env_excludes_add :
  forall x y roots R,
    roots_exclude x roots ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_add y roots R).
Proof.
  unfold root_env_excludes.
  intros x y roots R Hroots Hexcl z roots_z Hlookup Hneq.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb z y) eqn:Heq.
  - inversion Hlookup; subst roots_z. exact Hroots.
  - eapply Hexcl.
    + exact Hlookup.
    + exact Hneq.
Qed.

Lemma root_env_add_params_roots_preserves_excludes_params :
  forall add_ps roots_list protected_ps R_tail,
    Forall (roots_exclude_params protected_ps) roots_list ->
    root_env_excludes_params protected_ps R_tail ->
    root_env_excludes_params protected_ps
      (root_env_add_params_roots add_ps roots_list R_tail).
Proof.
  intros add_ps.
  induction add_ps as [| p add_ps IH];
    intros roots_list protected_ps R_tail Hroots Hexcl;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - exact Hexcl.
  - exact Hexcl.
  - exact Hexcl.
  - inversion Hroots as [| ? ? Hroot Hroots_tail]; subst.
    unfold root_env_excludes_params in *.
    intros x Hin.
    apply root_env_excludes_add.
    + apply Hroot. exact Hin.
    + exact (IH roots_list protected_ps R_tail Hroots_tail Hexcl x Hin).
Qed.

Lemma root_env_add_params_roots_excludes_params :
  forall ps roots_list R_tail,
    Forall (roots_exclude_params ps) roots_list ->
    root_env_excludes_params ps R_tail ->
    root_env_excludes_params ps
      (root_env_add_params_roots ps roots_list R_tail).
Proof.
  intros ps roots_list R_tail Hroots Hexcl.
  eapply root_env_add_params_roots_preserves_excludes_params; eassumption.
Qed.

Lemma call_param_root_env_excludes_params :
  forall ps roots_list R_tail,
    root_env_no_shadow R_tail ->
    Forall (roots_exclude_params ps) roots_list ->
    root_env_excludes_params ps R_tail ->
    root_env_excludes_params ps
      (call_param_root_env ps roots_list R_tail).
Proof.
  intros ps roots_list R_tail Hrn Hroots Hexcl.
  unfold call_param_root_env.
  apply root_env_add_params_roots_excludes_params.
  - exact Hroots.
  - apply root_env_remove_params_excludes_params; assumption.
Qed.

