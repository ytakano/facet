From Facet.TypeSystem Require Import TypeSafetyRootsReadyStore.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyRootSets.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyStoreOps.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyCtx.
From Facet.TypeSystem Require Import AssocEnvStructural.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma roots_exclude_root_sets_union_inv :
  forall x roots_list,
    roots_exclude x (root_sets_union roots_list) ->
    Forall (roots_exclude x) roots_list.
Proof.
  intros x roots_list Hexclude.
  induction roots_list as [|roots rest IH]; simpl in *.
  - constructor.
  - constructor.
    + unfold roots_exclude in *. intros Hin.
      apply Hexclude. apply root_set_union_in_l. exact Hin.
    + apply IH. unfold roots_exclude in *. intros Hin.
      apply Hexclude. apply root_set_union_in_r. exact Hin.
Qed.

Lemma match_binder_params_opt_infer_ok :
  forall binders tys ps,
    match_binder_params binders tys = infer_ok ps ->
    match_binder_params_opt binders tys = Some ps.
Proof.
  induction binders as [| x xs IH]; intros tys ps Hmatch;
    destruct tys as [| T Ts]; simpl in Hmatch; try discriminate.
  - inversion Hmatch. reflexivity.
  - destruct (match_binder_params xs Ts) as [ps_tail | err] eqn:Htail;
      try discriminate.
    inversion Hmatch; subst ps.
    simpl. rewrite (IH Ts ps_tail Htail). reflexivity.
Qed.

Lemma match_payload_params_opt_infer_ok :
  forall binders lts args v ps,
    match_payload_params binders lts args v = infer_ok ps ->
    match_payload_params_opt binders lts args v = Some ps.
Proof.
  intros binders lts args v ps Hmatch.
  unfold match_payload_params, match_payload_params_opt,
    instantiate_enum_variant_field_tys in *.
  eapply match_binder_params_opt_infer_ok. exact Hmatch.
Qed.

Lemma match_binder_params_opt_names :
  forall binders tys ps,
    match_binder_params_opt binders tys = Some ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  induction binders as [| x xs IH]; intros tys ps Hmatch;
    destruct tys as [| T Ts]; simpl in Hmatch; try discriminate.
  - inversion Hmatch. reflexivity.
  - destruct (match_binder_params_opt xs Ts) as [ps_tail |] eqn:Htail;
      try discriminate.
    inversion Hmatch; subst ps; simpl.
    rewrite (IH Ts ps_tail Htail). reflexivity.
Qed.

Lemma match_payload_params_opt_names :
  forall binders lts args v ps,
    match_payload_params_opt binders lts args v = Some ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  intros binders lts args v ps Hmatch.
  unfold match_payload_params_opt in Hmatch.
  eapply match_binder_params_opt_names. exact Hmatch.
Qed.

Lemma place_borrow_roots_ctx_roots_named :
  forall R Σ p roots,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named (root_of_place p) Σ ->
    place_borrow_roots R p = Some roots ->
    root_set_ctx_roots_named roots Σ.
Proof.
  intros R Σ p roots Henv Hplace Hborrow.
  unfold place_borrow_roots in Hborrow.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - inversion Hborrow; subst roots. exact Hplace.
  - assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hborrow. }
    eapply root_env_lookup_ctx_roots_named; eassumption.
Qed.

Lemma resolve_root_set_fuel_ctx_roots_named :
  forall fuel R Σ roots out,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    resolve_root_set_fuel fuel R roots = Some out ->
    root_set_ctx_roots_named out Σ.
Proof.
  induction fuel as [| fuel IH]; intros R Σ roots out Henv Hroots Hres;
    simpl in Hres; try discriminate.
  destruct (singleton_store_root roots) as [x |] eqn:Hsingle.
  - destruct (root_env_lookup x R) as [env_roots |] eqn:Hlookup.
    + assert (Henv_roots : root_set_ctx_roots_named env_roots Σ).
      { eapply root_env_lookup_ctx_roots_named; eassumption. }
      destruct (singleton_store_root env_roots) as [y |] eqn:Henv_single.
      * destruct (ident_eqb x y) eqn:Hxy.
        -- inversion Hres; subst out. exact Hroots.
        -- eapply IH; eassumption.
      * eapply IH; eassumption.
    + inversion Hres; subst out. exact Hroots.
  - inversion Hres; subst out. exact Hroots.
Qed.

Lemma place_resolved_roots_ctx_roots_named :
  forall R Σ p roots,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named (root_of_place p) Σ ->
    place_resolved_roots R p = Some roots ->
    root_set_ctx_roots_named roots Σ.
Proof.
  intros R Σ p roots Henv Hplace Hresolved.
  unfold place_resolved_roots in Hresolved.
  destruct (place_borrow_roots R p) as [borrow_roots |] eqn:Hborrow;
    try discriminate.
  assert (Hborrow_named : root_set_ctx_roots_named borrow_roots Σ).
  { eapply place_borrow_roots_ctx_roots_named; eassumption. }
  unfold resolve_root_set in Hresolved.
  eapply resolve_root_set_fuel_ctx_roots_named; eassumption.
Qed.

Lemma typed_match_tail_roots_lookup_ready :
  forall env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss
      name vdef e,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    lookup_enum_variant name variants = Some vdef ->
    lookup_expr_branch name branches = Some e ->
    exists T Σv_payload Rv_payload Rv roots ps binders R_payload,
      R_payload = root_env_add_params_roots_same ps roots_scrut R /\
      params_names_nodup_b ps = true /\
      ctx_lookup_params_none_b ps Σ = true /\
      root_env_lookup_params_none_b ps R = true /\
      lookup_expr_branch_binders name branches = Some binders /\
      match_payload_params_opt binders lts args vdef = Some ps /\
      typed_env_roots env Ω n R_payload (sctx_add_params ps Σ) e T
        Σv_payload Rv_payload roots /\
      params_ok_sctx_b env ps Σv_payload = true /\
      EnvStructuralRules.roots_exclude_params ps roots /\
      Rv = root_env_remove_match_params ps Rv_payload /\
      EnvStructuralRules.root_env_excludes_params ps Rv /\
      ty_core T = expected_core /\
      root_env_equiv Rv R_out /\
      In roots rootss.
Proof.
  intros env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss
    name vdef e Htail.
  induction Htail as
    [lts args R roots_scrut Σ branches expected_core R_out
    |R R_payload Rv_payload Rv Σ branches v rest e0 T
       Σv_payload Σv R_out roots Σs Ts rootss expected_core
       binders ps lts args roots_scrut
       Hbinders Hparams Hnodup Hctx_none Hroot_none Hlookup Hpayload
       Htyped Hno_lbound Hparams_ok Hroots_excl Hremove Henv_excl
       Hctx_remove Hcore Hequiv Htail IHtail];
    intros Hvariant Hbranch.
  - simpl in Hvariant. discriminate.
  - simpl in Hvariant.
    destruct (String.eqb name (enum_variant_name v)) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name.
      rewrite Hlookup in Hbranch. inversion Hbranch; subst e.
      inversion Hvariant; subst vdef.
	      exists T, Σv_payload, Rv_payload, Rv, roots, ps, binders, R_payload.
	      repeat split; simpl; try assumption.
	      * eapply match_payload_params_opt_infer_ok. exact Hparams.
	      * left. reflexivity.
	    + destruct (IHtail Hvariant Hbranch) as
	        [T' [Σ' [Rv_payload' [Rv' [roots' [ps' [binders'
	          [R_payload' Hrest]]]]]]]].
	      destruct Hrest as [Hpayload' Hrest].
	      destruct Hrest as [Hnodup' Hrest].
	      destruct Hrest as [Hctx_none' Hrest].
	      destruct Hrest as [Hroot_none' Hrest].
	      destruct Hrest as [Hbinders' Hrest].
	      destruct Hrest as [Hparams' Hrest].
	      destruct Hrest as [Htyped' Hrest].
	      destruct Hrest as [Hparams_ok' Hrest].
	      destruct Hrest as [Hroots_excl' Hrest].
	      destruct Hrest as [Hremove' Hrest].
	      destruct Hrest as [Henv_excl' Hrest].
	      destruct Hrest as [Hcore' Hrest].
	      destruct Hrest as [Hequiv' Hin].
	      exists T', Σ', Rv_payload', Rv', roots', ps', binders', R_payload'.
	      repeat split; simpl; try assumption.
	      right. exact Hin.
Qed.

Lemma first_unknown_variant_branch_lookup_some :
  forall branches variants name e,
    first_unknown_variant_branch branches variants = None ->
    lookup_expr_branch name branches = Some e ->
    exists vdef, lookup_enum_variant name variants = Some vdef.
Proof.
  intros branches.
  induction branches as [| [[name0 binders0] e0] rest IH]; intros variants name e
    Hunknown Hlookup; simpl in Hunknown, Hlookup.
  - discriminate.
  - destruct (lookup_enum_variant name0 variants) as [vdef0 |] eqn:Hknown0;
      [| discriminate].
    destruct (String.eqb name name0) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name0.
      inversion Hlookup; subst e0. exists vdef0. exact Hknown0.
    + eapply IH; eassumption.
Qed.

Lemma lookup_expr_branch_lookup_expr_field :
  forall name branches,
    lookup_expr_branch name branches = lookup_match_branch name branches.
Proof.
  reflexivity.
Qed.

Lemma value_roots_within_root_sets_union_in :
  forall roots rootss v,
    In roots rootss ->
    value_roots_within roots v ->
    value_roots_within (root_sets_union rootss) v.
Proof.
  intros roots rootss v Hin Hwithin.
  induction rootss as [| roots_hd rest IH]; simpl in Hin; try contradiction.
  destruct Hin as [Heq | Hin].
  - subst roots_hd. apply value_roots_within_union_l. exact Hwithin.
  - apply value_roots_within_union_r. apply IH; assumption.
Qed.

Lemma Forall2_value_roots_within_root_sets_union :
  forall roots vs,
    Forall2 value_roots_within roots vs ->
    Forall (value_roots_within (root_sets_union roots)) vs.
Proof.
  intros roots vs H.
  induction H as [| roots_hd v roots_tail vs_tail Hwithin _ IH].
  - constructor.
  - constructor.
    + apply value_roots_within_root_sets_union_in with (roots := roots_hd).
      * simpl. left. reflexivity.
      * exact Hwithin.
    + eapply Forall_impl; [| exact IH].
      intros v_tail Hwithin_tail.
      apply value_roots_within_union_r. exact Hwithin_tail.
Qed.

Lemma value_roots_within_enum_payloads :
  forall roots enum_name variant_name lts args values,
    value_roots_within roots (VEnum enum_name variant_name lts args values) ->
    Forall (value_roots_within roots) values.
Proof.
  intros roots enum_name variant_name lts args values Hwithin.
  inversion Hwithin; subst; assumption.
Qed.

Lemma store_roots_within_add_params_roots_same :
  forall ps roots R s,
    params_names_nodup_b ps = true ->
    root_env_lookup_params_none_b ps R = true ->
    store_roots_within R s ->
    store_roots_within (root_env_add_params_roots_same ps roots R) s.
Proof.
  induction ps as [| [m x T] ps IH]; intros roots R s Hnodup Hnone Hstore.
  - exact Hstore.
  - simpl in Hnodup, Hnone |- *.
    destruct (root_env_lookup x R) eqn:Hlookup; try discriminate.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    apply store_roots_within_add_env.
    + apply IH.
      * exact Hnodup_tail.
      * exact Hnone.
      * exact Hstore.
    + apply root_env_lookup_add_params_roots_same_none.
      * exact Hlookup.
      * intros Hin.
        apply ident_in_b_false_not_in with (x := x) (xs := ctx_names (params_ctx ps)).
        -- apply negb_true_iff. exact Hnotin_b.
        -- exact Hin.
Qed.

Lemma store_roots_within_name_lookup_some :
  forall R s x,
    store_roots_within R s ->
    In x (store_names s) ->
    exists roots, root_env_lookup x R = Some roots.
Proof.
  intros R s x Hstore Hin.
  induction Hstore as [R | R se rest Hentry Hrest IH]; simpl in Hin.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst x. inversion Hentry; subst. eexists. eassumption.
    + apply IH. exact Hin.
Qed.

Lemma store_roots_within_params_fresh_in_store :
  forall ps R s,
    root_env_lookup_params_none_b ps R = true ->
    store_roots_within R s ->
    params_fresh_in_store ps s.
Proof.
  unfold params_fresh_in_store.
  intros ps R s Hnone Hstore x Hin Hstore_name.
  destruct (store_roots_within_name_lookup_some R s x Hstore Hstore_name)
    as [roots Hlookup].
  pose proof (root_env_lookup_params_none_b_not_in ps R x Hnone Hin) as Hnone_x.
  apply Hnone_x.
  eapply root_env_lookup_some_in_names. exact Hlookup.
Qed.

Lemma bind_params_store_no_shadow_names :
  forall ps vs s,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    Datatypes.length vs = Datatypes.length ps ->
    store_no_shadow s ->
    store_no_shadow (bind_params ps vs s).
Proof.
  induction ps as [| p ps IH]; intros vs s Hnodup Hfresh Hlen Hshadow.
  - destruct vs; exact Hshadow.
  - destruct vs as [| v vs'].
    + exact Hshadow.
    + simpl.
      inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
      simpl in Hlen. inversion Hlen as [Hlen_tail].
      apply store_no_shadow_add.
      * apply IH.
        -- exact Hnodup_tail.
        -- unfold params_fresh_in_store in *.
           intros x Hin Hstore.
           apply (Hfresh x); [right; exact Hin | exact Hstore].
        -- exact Hlen_tail.
        -- exact Hshadow.
      * apply store_lookup_not_in_names.
        rewrite (store_names_bind_params_length_readiness ps vs' s Hlen_tail).
        intros Hin.
        apply in_app_or in Hin as [Hin_params | Hin_store].
        -- apply Hnotin. exact Hin_params.
        -- unfold params_fresh_in_store in Hfresh.
           apply (Hfresh (param_name p)); [left; reflexivity | exact Hin_store].
Qed.

Lemma root_env_lookup_params_none_b_names :
  forall ps1 ps2 R,
    ctx_names (params_ctx ps1) = ctx_names (params_ctx ps2) ->
    root_env_lookup_params_none_b ps1 R = true ->
    root_env_lookup_params_none_b ps2 R = true.
Proof.
  induction ps1 as [| p1 ps1 IH]; intros ps2 R Hnames Hnone;
    destruct ps2 as [| p2 ps2]; simpl in Hnames, Hnone; try discriminate.
  - reflexivity.
  - inversion Hnames as [[Hhead Htail]].
    simpl.
    rewrite <- Hhead.
    destruct (root_env_lookup (param_name p1) R); try discriminate.
    apply IH; assumption.
Qed.

Lemma params_names_nodup_b_names :
  forall ps1 ps2,
    ctx_names (params_ctx ps1) = ctx_names (params_ctx ps2) ->
    params_names_nodup_b ps1 = true ->
    params_names_nodup_b ps2 = true.
Proof.
  unfold params_names_nodup_b.
  intros ps1 ps2 Hnames Hnodup.
  rewrite <- Hnames. exact Hnodup.
Qed.

Lemma store_roots_within_bind_params_roots_same_names :
  forall ps_store ps_env roots R s vs,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_env) ->
    params_names_nodup_b ps_env = true ->
    root_env_lookup_params_none_b ps_env R = true ->
    store_roots_within R s ->
    Forall (value_roots_within roots) vs ->
    Datatypes.length vs = Datatypes.length ps_store ->
    store_roots_within (root_env_add_params_roots_same ps_env roots R)
      (bind_params ps_store vs s).
Proof.
  induction ps_store as [| p_store ps_store IH];
    intros ps_env roots R s vs Hnames Hnodup Hnone Hstore Hvs Hlen;
    destruct ps_env as [| p_env ps_env]; simpl in Hnames; try discriminate.
  - simpl in Hlen. destruct vs; try discriminate. exact Hstore.
  - destruct vs as [| v vs']; simpl in Hlen; try discriminate.
    inversion Hnames as [[Hname Hnames_tail]].
    inversion Hvs as [| ? ? Hv Hvs_tail]; subst.
    simpl in Hnodup, Hnone |- *.
    destruct (root_env_lookup (param_name p_env) R) eqn:Hlookup; try discriminate.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    rewrite Hname.
    apply store_add_roots_within.
    + apply IH.
      * exact Hnames_tail.
      * exact Hnodup_tail.
      * exact Hnone.
      * exact Hstore.
      * exact Hvs_tail.
      * inversion Hlen. reflexivity.
    + apply root_env_lookup_add_params_roots_same_none.
      * exact Hlookup.
      * intros Hin.
        apply ident_in_b_false_not_in with
          (x := param_name p_env) (xs := ctx_names (params_ctx ps_env)).
        -- apply negb_true_iff. exact Hnotin_b.
        -- exact Hin.
    + exact Hv.
Qed.

Lemma store_roots_within_remove_match_params :
  forall ps R s,
    store_roots_within R s ->
    NoDup (ctx_names (params_ctx ps)) ->
    store_no_shadow s ->
    store_roots_within (root_env_remove_match_params ps R)
      (store_remove_params ps s).
Proof.
  induction ps as [| [m x T] ps IH]; intros R s Hstore Hnodup Hshadow.
  - exact Hstore.
  - simpl in Hnodup |- *.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    apply IH.
    + apply store_remove_roots_within.
      * exact Hstore.
      * eapply store_no_shadow_remove_no_name. exact Hshadow.
    + exact Hnodup_tail.
    + apply store_no_shadow_remove. exact Hshadow.
Qed.

Lemma store_roots_within_remove_match_params_names :
  forall ps_store ps_env R s,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_env) ->
    store_roots_within R s ->
    NoDup (ctx_names (params_ctx ps_env)) ->
    store_no_shadow s ->
    store_roots_within (root_env_remove_match_params ps_env R)
      (store_remove_params ps_store s).
Proof.
  induction ps_store as [| p_store ps_store IH];
    intros ps_env R s Hnames Hstore Hnodup Hshadow;
    destruct ps_env as [| p_env ps_env]; simpl in Hnames; try discriminate.
  - exact Hstore.
  - inversion Hnames as [[Hname Hnames_tail]].
    simpl.
    apply IH.
    + exact Hnames_tail.
    + rewrite <- Hname.
      apply store_remove_roots_within.
      * exact Hstore.
      * eapply store_no_shadow_remove_no_name. exact Hshadow.
    + inversion Hnodup; subst. assumption.
    + apply store_no_shadow_remove. exact Hshadow.
Qed.

Lemma store_no_shadow_remove_params :
  forall ps s,
    store_no_shadow s ->
    store_no_shadow (store_remove_params ps s).
Proof.
  induction ps as [| p ps IH]; intros s Hshadow.
  - exact Hshadow.
  - simpl. apply IH. apply store_no_shadow_remove. exact Hshadow.
Qed.

Lemma root_env_ctx_roots_named_add_params_roots_same :
  forall ps roots R Σ,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named
      (root_env_add_params_roots_same ps roots R)
      (sctx_add_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros roots R Σ Henv Hroots.
  - exact Henv.
  - simpl.
    apply root_env_ctx_roots_named_add_binding.
    + apply IH; assumption.
    + unfold root_set_ctx_roots_named in *.
      intros z Hin.
      unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      apply in_or_app. right.
      apply Hroots. exact Hin.
Qed.

Lemma root_env_ctx_keys_named_add_params_roots_same :
  forall ps roots R Σ,
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named
      (root_env_add_params_roots_same ps roots R)
      (sctx_add_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros roots R Σ Hkeys.
  - exact Hkeys.
  - simpl. apply root_env_ctx_keys_named_add_binding.
    apply IH. exact Hkeys.
Qed.

Lemma root_env_ctx_roots_named_remove_match_params :
  forall ps R Σ,
    root_env_no_shadow R ->
    EnvStructuralRules.root_env_excludes_params ps
      (root_env_remove_match_params ps R) ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named
      (root_env_remove_match_params ps R)
      (sctx_remove_params ps Σ).
Proof.
  intros ps R Σ Hrn Hexcl Henv.
  eapply root_env_sctx_roots_named_remove_match_params; eassumption.
Qed.

Lemma root_set_ctx_roots_named_remove_params :
  forall ps roots Σ,
    EnvStructuralRules.roots_exclude_params ps roots ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots (sctx_remove_params ps Σ).
Proof.
  induction ps as [| [m x T] ps IH]; intros roots Σ Hexcl Hnamed.
  - exact Hnamed.
  - simpl in Hexcl |- *.
    inversion Hexcl as [| ? ? Hhead Htail]; subst.
    apply IH.
    + exact Htail.
    + apply root_set_ctx_roots_named_remove_binding; assumption.
Qed.

Theorem typed_roots_ctx_roots_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    root_set_ctx_roots_named roots Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    Forall (fun roots => root_set_ctx_roots_named roots Σ') roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    root_set_ctx_roots_named roots Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots_scrut Σ ->
    Forall (fun roots => root_set_ctx_roots_named roots Σ) rootss).
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros; try solve
    [ split; try assumption; apply root_set_ctx_roots_named_nil ].
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split.
    + eapply root_env_ctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_env_lookup_ctx_roots_named_consume_path; eassumption.
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split.
    + eapply root_env_ctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_env_lookup_ctx_roots_named_consume_path; eassumption.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IH Hrn Henv) as [Henv_args Hroots_args];
        split; [exact Henv_args | apply root_sets_ctx_roots_named_union; exact Hroots_args]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IH Hrn Henv) as [Henv_args Hroots_args];
        split; [exact Henv_args | apply root_sets_ctx_roots_named_union; exact Hroots_args]
    end.
  - match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 ?roots_callee,
      Hargs_typed : typed_args_roots env Ω n ?R1 ?Σ1 _ _ ?Σ2 ?R2 ?arg_roots,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - (* TER_CallExpr_TypeForall: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 ?roots_callee,
      Hargs_typed : typed_args_roots env Ω n ?R1 ?Σ1 _ _ ?Σ2 ?R2 ?arg_roots,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 ?roots_callee,
      Hargs_typed : typed_args_roots env Ω n ?R1 ?Σ1 _ _ ?Σ2 ?R2 ?arg_roots,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - (* TER_CallExprGeneric_TypeForall: same callee+args pattern *)
    match goal with
    | IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - (* TER_CallExpr_MixedForall: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 ?roots_callee,
      Hargs_typed : typed_args_roots env Ω n ?R1 ?Σ1 _ _ ?Σ2 ?R2 ?arg_roots,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - (* TER_CallExpr_Forall_Fn: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 ?roots_callee,
      Hargs_typed : typed_args_roots env Ω n ?R1 ?Σ1 _ _ ?Σ2 ?R2 ?arg_roots,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - (* TER_CallExpr_Forall_Closure: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 ?roots_callee,
      Hargs_typed : typed_args_roots env Ω n ?R1 ?Σ1 _ _ ?Σ2 ?R2 ?arg_roots,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_callee ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_args];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union;
          [eapply root_set_ctx_roots_named_typed_args_tail; eassumption
          | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IH Hrn Henv) as [Henv_args Hroots_args];
        split; [exact Henv_args | apply root_sets_ctx_roots_named_union; exact Hroots_args]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        root_set_ctx_roots_named ?roots ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IH Hrn Henv) as [Henv_args Hroots_args];
        split; [exact Henv_args | apply root_sets_ctx_roots_named_union; exact Hroots_args]
    end.
  - destruct (H H2 H3) as [Henv1 _].
    destruct (H H2 H3) as [_ Hroots_scrut_named].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hrn_payload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Henv_payload :
      root_env_ctx_roots_named R_payload (sctx_add_params ps_head Σ1)).
    { subst R_payload.
      apply root_env_ctx_roots_named_add_params_roots_same; assumption. }
    destruct (H0 Hrn_payload Henv_payload) as [Henv_head Hroots_head].
    pose proof (H1 Hrn1 Henv1 Hroots_scrut_named) as Hroots_tail.
    assert (Hsame_head_final :
      sctx_same_bindings Σ_head (sctx_of_ctx Γ_out)).
    { eapply ctx_merge_many_same_bindings_left.
      match goal with
      | Hmerge : ctx_merge_many (ctx_of_sctx Σ_head) _ = Some Γ_out |- _ =>
          exact Hmerge
      end. }
    assert (Hsame_1_head : sctx_same_bindings Σ1 Σ_head).
    { subst Σ_head.
      apply sctx_same_bindings_remove_added_params.
      eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      match goal with
      | Htyped : typed_env_roots _ _ _ R_payload (sctx_add_params ps_head Σ1) _ _ _ _ _ |- _ =>
          exact Htyped
      end. }
    assert (Hsame_1_final :
      sctx_same_bindings Σ1 (sctx_of_ctx Γ_out)).
    { eapply sctx_same_bindings_trans; eassumption. }
    assert (Hroots_tail_final :
      Forall (fun roots => root_set_ctx_roots_named roots (sctx_of_ctx Γ_out))
        roots_tail).
    { eapply Forall_impl.
      - intros roots0 Hnamed.
        eapply root_set_ctx_roots_named_same_bindings.
        + exact Hsame_1_final.
        + exact Hnamed.
      - exact Hroots_tail. }
    assert (Henv_out : root_env_ctx_roots_named R_out Σ_head).
    { subst R_out Σ_head.
	      apply root_env_ctx_roots_named_remove_match_params.
	      - eapply typed_env_roots_no_shadow; eassumption.
	      - exact r0.
	      - exact Henv_head. }
    assert (Hroots_head_scoped : root_set_ctx_roots_named roots_head Σ_head).
    { subst Σ_head.
      apply root_set_ctx_roots_named_remove_params; assumption. }
    split.
    + eapply root_env_ctx_roots_named_same_bindings.
      * exact Hsame_head_final.
      * exact Henv_out.
    + apply root_sets_ctx_roots_named_union.
      simpl. constructor.
      * eapply root_set_ctx_roots_named_same_bindings.
        -- exact Hsame_head_final.
        -- exact Hroots_head_scoped.
      * exact Hroots_tail_final.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Henv_add :
      root_env_ctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_ctx_roots_named_add_binding; assumption. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    split.
    + apply root_env_ctx_roots_named_remove_binding; assumption.
    + apply root_set_ctx_roots_named_remove_binding; assumption.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Henv_add :
      root_env_ctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_ctx_roots_named_add_binding; assumption. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    split.
    + apply root_env_ctx_roots_named_remove_binding; assumption.
    + apply root_set_ctx_roots_named_remove_binding; assumption.
  - destruct (H H0 H1) as [Henv Hroots].
    split; [exact Henv | apply root_set_ctx_roots_named_nil].
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hroots_old : root_set_ctx_roots_named roots_old Σ1)
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    split.
    + eapply root_env_ctx_roots_named_update_union_restore_path;
        eassumption.
    + eapply root_env_lookup_result_ctx_roots_named_after_typed_restore_path;
        eassumption.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hroots_old : root_set_ctx_roots_named roots_old Σ1)
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    assert (Hroots_result_Σ : root_set_ctx_roots_named roots_result Σ)
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    assert (Hsame : sctx_same_bindings Σ Σ1).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural. eassumption. }
    split.
    + eapply root_env_ctx_roots_named_update_union; eassumption.
    + eapply root_set_ctx_roots_named_same_bindings; eassumption.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hroots_old : root_set_ctx_roots_named roots_old Σ')
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    split.
    + eapply root_env_ctx_roots_named_update_union; eassumption.
    + apply root_set_ctx_roots_named_nil.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hroots_old : root_set_ctx_roots_named roots_old Σ')
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    split.
    + eapply root_env_ctx_roots_named_update_union; eassumption.
    + apply root_set_ctx_roots_named_nil.
  - split; try assumption.
    eapply root_of_place_ctx_roots_named. eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_borrow_roots ?R ?p = Some ?roots |-
        root_set_ctx_roots_named ?roots ?Σ =>
        rewrite (place_borrow_roots_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_ctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply place_resolved_roots_ctx_roots_named.
    + eassumption.
    + eapply root_of_place_ctx_roots_named. eassumption.
    + eassumption.
  - split; try assumption.
    eapply root_store_single_ctx_roots_named_of_place_path; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_borrow_roots ?R ?p = Some ?roots |-
        root_set_ctx_roots_named ?roots ?Σ =>
        rewrite (place_borrow_roots_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_ctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply place_resolved_roots_ctx_roots_named.
    + eassumption.
    + eapply root_of_place_ctx_roots_named. eassumption.
    + eassumption.
  - split; try assumption.
    eapply place_resolved_write_target_writable_chain_ctx_roots_named; eassumption.
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_root_lookup ?R ?p = Some ?roots |-
        root_set_ctx_roots_named ?roots ?Σ =>
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_ctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply place_resolved_roots_ctx_roots_named.
    + eassumption.
    + eapply root_of_place_ctx_roots_named. eassumption.
    + eassumption.
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_root_lookup ?R ?p = Some ?roots |-
        root_set_ctx_roots_named ?roots ?Σ =>
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_ctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply place_resolved_roots_ctx_roots_named.
    + eassumption.
    + eapply root_of_place_ctx_roots_named. eassumption.
    + eassumption.
  - match goal with
    | IHcond : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_cond ?Σ1,
      IHthen : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        root_set_ctx_roots_named ?roots2 ?Σ2,
      IHelse : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R3 ?Σ3 /\
        root_set_ctx_roots_named ?roots3 ?Σ3,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcond Hrn Henv) as [Henv1 _];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHthen Hrn1 Henv1) as [Henv2 Hroots2];
        destruct (IHelse Hrn1 Henv1) as [_ Hroots3];
        split;
        [ eapply root_env_ctx_roots_named_ctx_merge_left; eassumption
        | eapply root_set_ctx_roots_named_if_merge; eassumption ]
    end.
  - split; try assumption. constructor.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?roots_rest,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_rest];
        split; [exact Henv2 | constructor; [| exact Hroots_rest]];
        eapply root_set_ctx_roots_named_typed_args_tail; eassumption
    end.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_field ?Σ1,
      IHfields : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        root_set_ctx_roots_named ?roots_rest ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHfields Hrn1 Henv1) as [Henv2 Hroots_rest];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union; [| exact Hroots_rest]];
        eapply root_set_ctx_roots_named_typed_fields_tail; eassumption
    end.
  - constructor.
  - assert (Hrn_payload : root_env_no_shadow R_payload)
      by (subst R_payload; eapply root_env_add_params_roots_same_no_shadow; eauto).
    assert (Henv_payload :
      root_env_ctx_roots_named R_payload (sctx_add_params ps Σ)).
    { subst R_payload.
      apply root_env_ctx_roots_named_add_params_roots_same; assumption. }
    destruct (H Hrn_payload Henv_payload) as [_ Hroot].
    pose proof (H0 H1 H2 H3) as Hroots_tail.
    constructor; [| exact Hroots_tail].
    assert (Hroot_scoped : root_set_ctx_roots_named roots Σv).
    { subst Σv. eapply root_set_ctx_roots_named_remove_params; eauto. }
    eapply root_set_ctx_roots_named_same_bindings.
    + apply sctx_same_bindings_sym.
      subst Σv.
      apply sctx_same_bindings_remove_added_params.
      eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural. exact t.
    + rewrite <- e10. exact Hroot_scoped.
Qed.

Lemma typed_value_roots_assoc_ctx_roots_named :
  forall env Ω n R Σ e T_expected Σ' R' roots,
    typed_value_roots_assoc env Ω n R Σ e T_expected Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    root_set_ctx_roots_named roots Σ'.
Proof.
  intros env Ω n R Σ e T_expected Σ' R' roots Htyped Hshadow Hnamed.
  inversion Htyped; subst.
  exact (proj1 (typed_roots_ctx_roots_named_mutual env Ω n)
    R Σ e T_actual Σ' R' roots H Hshadow Hnamed).
Qed.

Lemma typed_args_roots_assoc_ctx_roots_named :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    Forall (fun roots => root_set_ctx_roots_named roots Σ') roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots Hargs Hshadow Hnamed.
  induction Hargs.
  - split; [exact Hnamed | constructor].
  - destruct (proj1 (typed_roots_ctx_roots_named_mutual env Ω n)
      R Σ e T_e Σ1 R1 roots H Hshadow Hnamed) as [Hnamed1 Hroots].
    assert (Hshadow1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    destruct (IHHargs Hshadow1 Hnamed1) as [Hnamed2 Hroots_rest].
    split.
    + exact Hnamed2.
    + constructor.
      * eapply root_set_ctx_roots_named_same_bindings.
        -- eapply typed_args_roots_assoc_same_bindings. exact Hargs.
        -- exact Hroots.
      * exact Hroots_rest.
Qed.

Theorem typed_roots_ctx_keys_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R' Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R' Σ') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R' Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    True).
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros; try assumption.
  - eapply root_env_ctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - eapply root_env_ctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - (* TER_CallExpr_TypeForall: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - (* TER_CallExprGeneric_TypeForall: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - (* TER_CallExpr_MixedForall: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - (* TER_CallExpr_Forall_Fn: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - (* TER_CallExpr_Forall_Closure: same callee+args pattern *)
    match goal with
    | Htyped : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHcallee Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (IHargs Hrn1 Hkeys1)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - pose proof (H H2 H3) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hrn_payload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hkeys_payload :
      root_env_ctx_keys_named R_payload (sctx_add_params ps_head Σ1)).
    { subst R_payload.
      apply root_env_ctx_keys_named_add_params_roots_same. exact Hkeys1. }
    pose proof (H0 Hrn_payload Hkeys_payload) as Hkeys_head_payload.
    assert (Hrn_head_payload : root_env_no_shadow R_head_payload)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hkeys_out : root_env_ctx_keys_named R_out Σ_head).
    { subst R_out Σ_head.
      eapply root_env_sctx_keys_named_remove_match_params; eassumption. }
    eapply root_env_ctx_keys_named_same_bindings.
    + eapply ctx_merge_many_same_bindings_left.
      match goal with
      | Hmerge : ctx_merge_many (ctx_of_sctx Σ_head) _ = Some _ |- _ =>
          exact Hmerge
      end.
    + exact Hkeys_out.
	  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hkeys_add :
      root_env_ctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_ctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    apply root_env_ctx_keys_named_remove_binding; assumption.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hkeys_add :
      root_env_ctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_ctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    apply root_env_ctx_keys_named_remove_binding; assumption.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      Hrestore : sctx_restore_path ?Σ1 ?x ?path = infer_ok ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        apply root_env_ctx_keys_named_update;
        eapply root_env_ctx_keys_named_same_bindings;
        [ eapply sctx_restore_path_same_bindings; exact Hrestore
        | exact (IH Hrn Henv) ]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        apply root_env_ctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        apply root_env_ctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        apply root_env_ctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - repeat match goal with
    | Hstep : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        let Hkeys' := fresh "Hkeys_step" in
        let Hrn' := fresh "Hrn_step" in
        pose proof (Hstep Hrn Hkeys) as Hkeys';
        assert (Hrn' : root_env_no_shadow R')
          by (eapply typed_env_roots_no_shadow; eassumption);
        clear Hstep
    end.
    eapply root_env_ctx_keys_named_same_bindings.
    + eapply ctx_merge_same_bindings_left. eassumption.
    + eassumption.
  - match goal with
    | Htyped1 : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      Hexpr : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      Hargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hexpr Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (Hargs Hrn1 Hkeys1)
    end.
  - match goal with
    | Hfield : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      Hrest : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hfield Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (Hrest Hrn1 Hkeys1)
    end.
  - exact I.
  - exact I.
Qed.

Theorem eval_preserves_roots_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_roots_within R' s' /\
        value_roots_within roots v /\
        store_no_shadow s' /\
        root_env_no_shadow R') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_roots_within R' s' /\
        Forall2 value_roots_within roots vs /\
        store_no_shadow s' /\
        root_env_no_shadow R') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_roots_within R' s' /\
        value_fields_roots_within roots values /\
        store_no_shadow s' /\
        root_env_no_shadow R')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s i Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s f Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s b Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    dependent destruction Htyped.
    all: repeat split; try assumption;
      eapply store_roots_within_lookup_value; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    dependent destruction Htyped.
    all: repeat split; try (apply store_mark_used_roots_within; exact Hroots);
      try (eapply store_roots_within_lookup_value; eassumption);
      try (apply store_no_shadow_mark_used; exact Hnodup);
      try exact Hrn.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hroots Hnodup Hrn Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    all: repeat split; try assumption;
      match goal with
      | Hpath_typed : place_path ?p_typed = Some (?root, ?path_typed),
        Heval_p : eval_place ?s_typed ?p_typed ?x_eval0 ?path_eval0,
        Hvalue_path : value_lookup_path (se_val ?se0) ?path_eval0 = Some ?v_target,
        Hroot_lookup : root_env_lookup ?root ?Rcur = Some ?roots_cur
        |- value_roots_within ?roots_cur ?v_target =>
          destruct (eval_place_matches_place_path s_typed p_typed x_eval0 path_eval0
                      root path_typed Heval_p Hpath_typed) as [Hx Hpath];
          subst x_eval0 path_eval0;
          eapply value_lookup_path_roots_within;
          [ eapply store_roots_within_lookup_value; eassumption
          | exact Hvalue_path ]
      end.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    all: repeat split; try exact Hrn;
      try
        (unfold store_consume_path in Hstore_consume;
         destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
           try discriminate;
         destruct (binding_available_b (se_state se0) path_eval);
           try discriminate;
         eapply store_update_state_roots_within; eassumption);
      try
        (unfold store_consume_path in Hstore_consume;
         destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
           try discriminate;
         destruct (binding_available_b (se_state se0) path_eval);
           try discriminate;
         eapply store_no_shadow_update_state; eassumption);
      match goal with
      | Hpath_typed : place_path ?p_typed = Some (?root, ?path_typed),
        Heval_p : eval_place ?s_typed ?p_typed ?x_eval0 ?path_eval0,
        Hvalue_path : value_lookup_path (se_val ?se0) ?path_eval0 = Some ?v_target,
        Hroot_lookup : root_env_lookup ?root ?Rcur = Some ?roots_cur
        |- value_roots_within ?roots_cur ?v_target =>
          destruct (eval_place_matches_place_path s_typed p_typed x_eval0 path_eval0
                      root path_typed Heval_p Hpath_typed) as [Hx Hpath];
          subst x_eval0 path_eval0;
          eapply value_lookup_path_roots_within;
          [ eapply store_roots_within_lookup_value; eassumption
          | exact Hvalue_path ]
      end.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_struct name env = Some ?sdef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst sdef_typed
    end.
    match goal with
    | Hready_fields : provenance_ready_fields fields,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ fields
        (struct_fields sdef) Σ' R' roots |- _ =>
        destruct (IHfields Ω n lts args R Σ Σ' R' roots
                    Hready_fields Hroots Hnodup Hrn Htyped_fields)
          as [Hroots' [Hvals [Hnodup' Hrn']]]
    end.
    repeat split; try assumption.
    constructor. exact Hvals.
  - intros s s' enum_name variant_name lts variant_lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IHargs Ω n R Σ T Σ' R' roots Hready Hroots
      Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_enum enum_name env = Some ?edef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst edef_typed
    end.
    match goal with
    | Hvariant_typed : lookup_enum_variant variant_name (enum_variants edef) =
          Some ?vdef_typed |- _ =>
        rewrite Hvariant in Hvariant_typed; inversion Hvariant_typed; subst vdef_typed
    end.
    match goal with
    | Hready_args : provenance_ready_args payloads,
      Htyped_args : typed_args_roots env Ω n R Σ payloads _ Σ' R' ?payload_roots |- _ =>
        destruct (IHargs Ω n R Σ _ Σ' R' payload_roots
                    Hready_args Hroots Hnodup Hrn Htyped_args)
          as [Hroots' [Hvals [Hnodup' Hrn']]]
    end.
    repeat split; try assumption.
    apply VRW_Enum.
    + apply Forall2_value_roots_within_root_sets_union. exact Hvals.
    + intros root Hexclude.
      eapply value_roots_exclude_root_forall2.
      * exact Hvals.
      * apply roots_exclude_root_sets_union_inv. exact Hexclude.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready1 : provenance_ready_expr e1,
      Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_expr ?Σ1_expr
        ?R1_expr ?roots1_expr |- _ =>
        destruct (IH1 Ω n R Σ T1_expr Σ1_expr R1_expr roots1_expr
                    Hready1 Hroots Hnodup Hrn Htyped1)
          as [Hroots1 [Hv1 [Hnodup1 Hrn1]]]
    end.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_ann v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_nodup : store_no_shadow (store_add x T_ann v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    match goal with
    | Hready2 : provenance_ready_expr e2,
      Htyped2 : typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T_ann m Σ1) e2 ?T_body ?Σ2_body ?R2_body
        ?roots2_body |- _ =>
        destruct (IH2 Ω n (root_env_add x roots1 R1)
                    (sctx_add x T_ann m Σ1) T_body Σ2_body R2_body
                    roots2_body Hready2 Hadd_roots Hadd_nodup Hadd_rn Htyped2)
          as [Hroots2 [Hv2 [Hnodup2 Hrn2]]]
    end.
    repeat split.
    + eapply store_remove_roots_within.
      * exact Hroots2.
      * apply store_no_shadow_remove_no_name. exact Hnodup2.
    + exact Hv2.
    + apply store_no_shadow_remove. exact Hnodup2.
    + apply root_env_no_shadow_remove. exact Hrn2.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ_e ?R_e ?roots_e |- _ =>
        destruct (IH Ω n R Σ T_e Σ_e R_e roots_e Hready_e
                    Hroots Hnodup Hrn Htyped_e)
          as [Hroots' [_ [Hnodup' Hrn']]]
    end.
    repeat split; try assumption; constructor.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    match goal with
    | Hlookup_store : store_lookup ?x_store s = Some old_e |- _ =>
        assert (Hroots2 : store_roots_within
          (root_env_update x_store (root_set_union roots_old roots_new) R1) s2)
    end.
    { eapply store_update_val_roots_within_union; eassumption. }
    assert (Hnodup2 : store_no_shadow s2)
      by (eapply store_no_shadow_update_val; eassumption).
    match goal with
    | Hlookup_store : store_lookup ?x_store s = Some old_e |- _ =>
        assert (Hroots3 : store_roots_within
          (root_env_update x_store (root_set_union roots_old roots_new) R1) s3)
    end.
    { unfold store_restore_path in Hrestore.
      eapply store_update_state_roots_within; eassumption. }
    assert (Hnodup3 : store_no_shadow s3).
    { unfold store_restore_path in Hrestore.
      eapply store_no_shadow_update_state; eassumption. }
    repeat split; try assumption.
    + eapply store_roots_within_lookup_value.
      * exact Hroots.
      * exact Hlookup.
      * match goal with
        | Hroot_lookup : root_env_lookup _ R = Some roots |- _ =>
            exact Hroot_lookup
        end.
    + apply root_env_no_shadow_update. exact Hrn1.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    repeat split.
    + eapply store_update_val_roots_within_union; eassumption.
    + constructor.
    + eapply store_no_shadow_update_val; eassumption.
    + apply root_env_no_shadow_update. exact Hrn1.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    assert (Hroots2 : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s2).
    { eapply eval_place_update_path_roots_within_union.
      - exact Hroots1.
      - exact Hnodup1.
      - match goal with
        | Hpath_static : place_path _ = Some _ |- _ =>
            exact Hpath_static
        end.
      - exact Heval_place.
      - match goal with
        | Hroot_old_lookup : root_env_lookup x R1 = Some roots_old |- _ =>
            exact Hroot_old_lookup
        end.
      - exact Hvnew.
      - exact Hupdate. }
    assert (Hnodup2 : store_no_shadow s2)
      by (eapply store_no_shadow_update_path; eassumption).
    assert (Hroots3 : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s3).
    { unfold store_restore_path in Hrestore.
      eapply store_update_state_roots_within; eassumption. }
    assert (Hnodup3 : store_no_shadow s3).
    { unfold store_restore_path in Hrestore.
      eapply store_no_shadow_update_state; eassumption. }
    repeat split; try assumption.
    + eapply eval_place_lookup_path_roots_within.
      * exact Hroots.
      * match goal with
        | Hpath_static : place_path p = Some (x, path) |- _ =>
            exact Hpath_static
        end.
      * exact Heval_place.
      * exact Hlookup_old.
      * match goal with
        | Hroot_lookup : root_env_lookup x R = Some roots |- _ =>
            exact Hroot_lookup
        end.
    + apply root_env_no_shadow_update. exact Hrn1.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
          ?R1_new ?roots_new0 |- _ =>
          destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                      Hready_new Hroots Hnodup Hrn Htyped_new)
            as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
      end.
      assert (Hroots2 : store_roots_within
        (root_env_update x (root_set_union roots_old roots_new) R1) s2).
      { eapply eval_place_resolved_update_path_roots_within_union.
        - exact Hroots.
        - match goal with
          | Hstore_nodup : store_no_shadow s1 |- _ => exact Hstore_nodup
          end.
        - match goal with
          | Hstore_roots : store_roots_within R1 s1 |- _ => exact Hstore_roots
          end.
        - match goal with
          | Hroot_old_lookup : root_env_lookup x R1 = Some roots_old |- _ =>
              exact Hroot_old_lookup
          end.
        - exact Heval_place.
        - match goal with
          | Htarget : place_resolved_write_target R p = Some x |- _ => exact Htarget
          end.
        - exact Hvnew.
        - exact Hupdate. }
      assert (Hnodup2 : store_no_shadow s2)
        by (eapply store_no_shadow_update_path; eassumption).
      assert (Hroots3 : store_roots_within
        (root_env_update x (root_set_union roots_old roots_new) R1) s3).
      { unfold store_restore_path in Hrestore.
        eapply store_update_state_roots_within; eassumption. }
      assert (Hnodup3 : store_no_shadow s3).
      { unfold store_restore_path in Hrestore.
        eapply store_no_shadow_update_state; eassumption. }
      repeat split; try assumption.
      * eapply eval_place_resolved_lookup_path_roots_within.
        -- exact Hroots.
        -- exact Heval_place.
        -- exact Hlookup_old.
        -- match goal with
           | Htarget : place_resolved_write_target R p = Some x |- _ => exact Htarget
           end.
        -- match goal with
           | Hroot_lookup : root_env_lookup x R = Some roots |- _ => exact Hroot_lookup
           end.
      * apply root_env_no_shadow_update. exact Hrn1.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    repeat split.
    + eapply eval_place_update_path_roots_within_union; eassumption.
    + constructor.
    + eapply store_no_shadow_update_path; eassumption.
    + apply root_env_no_shadow_update. exact Hrn1.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
          ?R1_new ?roots_new0 |- _ =>
          destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                      Hready_new Hroots Hnodup Hrn Htyped_new)
            as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
      end.
      repeat split.
      * eapply eval_place_resolved_update_path_roots_within_union.
        -- exact Hroots.
        -- match goal with
           | Hstore_nodup : store_no_shadow s1 |- _ => exact Hstore_nodup
           end.
        -- match goal with
           | Hstore_roots : store_roots_within R1 s1 |- _ => exact Hstore_roots
           end.
        -- match goal with
           | Hroot_old_lookup : root_env_lookup x R1 = Some roots_old |- _ =>
               exact Hroot_old_lookup
           end.
        -- exact Heval_place.
        -- match goal with
           | Htarget : place_resolved_write_target R p = Some x |- _ => exact Htarget
           end.
        -- exact Hvnew.
        -- exact Hupdate.
      * constructor.
      * eapply store_no_shadow_update_path; eassumption.
      * apply root_env_no_shadow_update. exact Hrn1.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try congruence.
    + repeat split; try assumption.
      match goal with
      | Hpath_static : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_matches_place_path s p x path
                      x_static path_static Heval_place Hpath_static)
            as [Hx Hpath];
          subst x path;
          unfold root_of_place;
          rewrite Hpath_static;
          constructor; simpl; left; reflexivity
      end.
    + repeat split; try assumption.
      match goal with
      | Hpath_static : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_matches_place_path s p x path
                      x_static path_static Heval_place Hpath_static)
            as [Hx Hpath];
          subst x path;
          constructor; simpl; left; reflexivity
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn
      Htyped.
    dependent destruction Hready.
    inversion Heval_r; subst.
    dependent destruction Htyped; try congruence.
    + repeat split; try assumption.
      match goal with
      | Hevalp : eval_place ?s0 ?p0 ?x0 ?path0,
        Hlookup0 : store_lookup ?x0 ?s0 = Some ?se0,
        Hvalue0 : value_lookup_path (se_val ?se0) ?path0 = Some ?v0 |- _ =>
          assert (Hlookup_path : store_lookup_path x0 path0 s0 = Some v0)
            by (unfold store_lookup_path; rewrite Hlookup0; exact Hvalue0);
          eapply eval_place_lookup_path_roots_within; eassumption
      end.
    + repeat split; try assumption.
      match goal with
      | Hevalp : eval_place ?s0 ?p0 ?x0 ?path0,
        Hlookup0 : store_lookup ?x0 ?s0 = Some ?se0,
        Hvalue0 : value_lookup_path (se_val ?se0) ?path0 = Some ?v0 |- _ =>
          assert (Hlookup_path : store_lookup_path x0 path0 s0 = Some v0)
            by (unfold store_lookup_path; rewrite Hlookup0; exact Hvalue0);
          eapply eval_place_lookup_path_roots_within; eassumption
      end.
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hroots.
    + constructor.
    + exact Hnodup.
    + exact Hrn.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R' roots
      Hready _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond0 ?Σ1_cond
        ?R1_cond ?roots_cond0 |- _ =>
        destruct (IHcond Ω n R Σ T_cond0 Σ1_cond R1_cond roots_cond0
                    Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]]
    end.
    match goal with
    | Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1_cond ?Σ1_cond e2
        ?T2_then ?Σ2_then ?R2_then ?roots2_then |- _ =>
        destruct (IHthen Ω n R1_cond Σ1_cond T2_then Σ2_then R2_then
                    roots2_then Hready_then Hroots1 Hnodup1 Hrn1 Htyped_then)
          as [Hroots2 [Hv2 [Hnodup2 Hrn2]]]
    end.
    repeat split; try assumption.
    + apply value_roots_within_union_l. exact Hv2.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond0 ?Σ1_cond
        ?R1_cond ?roots_cond0 |- _ =>
        destruct (IHcond Ω n R Σ T_cond0 Σ1_cond R1_cond roots_cond0
                    Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]]
    end.
    match goal with
    | Hready_else : provenance_ready_expr e3,
      Htyped_else : typed_env_roots env Ω n ?R1_cond ?Σ1_cond e3
        ?T3_else ?Σ3_else ?R3_else ?roots3_else |- _ =>
	        destruct (IHelse Ω n R1_cond Σ1_cond T3_else Σ3_else R3_else
	                    roots3_else Hready_else Hroots1 Hnodup1 Hrn1 Htyped_else)
	          as [Hroots3 [Hv3 [Hnodup3 Hrn3]]]
	    end.
	    assert (Hrn2 : root_env_no_shadow R')
	      by (eapply typed_env_roots_no_shadow; eassumption).
	    assert (Hroots3_out : store_roots_within R' s2).
	    { eapply store_roots_within_equiv.
	      - apply root_env_equiv_sym. eassumption.
	      - exact Hroots3. }
		    repeat split.
		    + exact Hroots3_out.
		    + apply value_roots_within_union_r. exact Hv3.
		    + exact Hnodup3.
		    + exact Hrn2.
  - intros s s_scrut s_branch s' scrut branches enum_name variant_name
      lts args values edef vdef binders ps e_branch v
      Heval_scrut IHscrut Hlookup_enum Hlookup_variant Hlookup_binders
      Hparams Hlen Hlookup Heval_branch IHbranch Hstore
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHscrut Ω n R Σ T_scrut Σ1 R1 roots_scrut
                ltac:(match goal with
                | H : provenance_ready_expr scrut |- _ => exact H
                end) Hroots Hnodup Hrn
                ltac:(match goal with
                | H : typed_env_roots env Ω n R Σ scrut T_scrut Σ1 R1
                    roots_scrut |- _ => exact H
                end))
	      as [Hroots_scrut [Hv_scrut [Hnodup_scrut Hrn_scrut]]].
    assert (Hready_branch : provenance_ready_expr e_branch).
    { unfold lookup_match_branch in Hlookup.
      eapply provenance_ready_match_branches_lookup; eassumption. }
    unfold lookup_match_branch in Hlookup.
	    assert (Hlookup_branch :
	      lookup_expr_branch variant_name branches = Some e_branch).
	    { rewrite lookup_expr_branch_lookup_expr_field. exact Hlookup. }
	    assert (Hvariant_known :
	      exists vdef, lookup_enum_variant variant_name (enum_variants edef0) =
	        Some vdef).
	    { eapply first_unknown_variant_branch_lookup_some; eassumption. }
	    match goal with
	    | Hvariants : enum_variants edef0 = v_head :: v_tail |- _ =>
	        rewrite Hvariants in Hvariant_known
	    end.
	    simpl in Hvariant_known.
	    destruct (String.eqb variant_name (enum_variant_name v_head))
	      eqn:Hvariant_head.
	    + apply String.eqb_eq in Hvariant_head. subst variant_name.
	      match goal with
	      | H : lookup_expr_branch (enum_variant_name v_head) branches =
	            Some e_head |- _ => rewrite H in Hlookup_branch
	      end.
	      inversion Hlookup_branch; subst.
	      assert (Hnames_payload : ctx_names (params_ctx ps) =
	        ctx_names (params_ctx ps_head)).
	      { assert (Hnames_runtime :
	          ctx_names (params_ctx ps) = binders).
	        { eapply match_payload_params_opt_names. exact Hparams. }
	        assert (Hhead :
	          exists binders_head,
	            lookup_expr_branch_binders (enum_variant_name v_head) branches =
	              Some binders_head /\
	            ctx_names (params_ctx ps_head) = binders_head).
	        { match goal with
	          | Hlookup_head : lookup_expr_branch_binders
	              (enum_variant_name v_head) branches = Some ?binders_head,
	            Hparams_head : match_payload_params ?binders_head ?lts_head
	              ?args_head v_head = infer_ok ps_head |- _ =>
	              exists binders_head; split;
	              [ exact Hlookup_head
	              | eapply match_payload_params_names; exact Hparams_head ]
	          end. }
	        destruct Hhead as [binders_head0 [Hlookup_head Hnames_head]].
	        rewrite Hnames_runtime, Hnames_head.
	        rewrite Hlookup_binders in Hlookup_head.
	        inversion Hlookup_head. reflexivity. }
	      pose proof (value_roots_within_enum_payloads roots_scrut enum_name
	        (enum_variant_name v_head) lts args values Hv_scrut) as Hvalues_roots.
	      assert (Hroots_payload :
	        store_roots_within
	          (root_env_add_params_roots_same ps_head roots_scrut R1)
	          (bind_params ps values s_scrut)).
	      { eapply store_roots_within_bind_params_roots_same_names.
	        - exact Hnames_payload.
	        - eassumption.
	        - eassumption.
	        - exact Hroots_scrut.
	        - exact Hvalues_roots.
	        - exact Hlen. }
	      destruct (IHbranch Ω n
	                  (root_env_add_params_roots_same ps_head roots_scrut R1)
	                  (sctx_add_params ps_head Σ1)
	                  T_head Σ_head_payload R_head_payload roots_head
	                  Hready_branch Hroots_payload
	                  ltac:(apply bind_params_store_no_shadow_names;
	                        [ eapply params_names_nodup_b_sound;
	                          eapply params_names_nodup_b_names;
	                          [ symmetry; exact Hnames_payload | eassumption ]
	                        | eapply store_roots_within_params_fresh_in_store;
	                          [ eapply root_env_lookup_params_none_b_names;
	                            [ symmetry; exact Hnames_payload | eassumption ]
	                          | exact Hroots_scrut ]
	                        | exact Hlen
	                        | exact Hnodup_scrut ])
	                  ltac:(eapply root_env_add_params_roots_same_no_shadow; eauto)
	                  Htyped2)
	        as [Hroots_branch [Hv_branch [Hnodup_branch Hrn_branch]]].
	      repeat split.
	      * eapply store_roots_within_remove_match_params_names.
	        -- exact Hnames_payload.
	        -- exact Hroots_branch.
	        -- eapply params_names_nodup_b_sound. eassumption.
	        -- exact Hnodup_branch.
	      * apply value_roots_within_union_l. exact Hv_branch.
	      * apply store_no_shadow_remove_params. exact Hnodup_branch.
	      * apply root_env_remove_match_params_no_shadow.
	        exact Hrn_branch.
	    + destruct Hvariant_known as [vdef_tail Hvariant_tail].
	      destruct (typed_match_tail_roots_lookup_ready env Ω n lts0 args0 R1
	                  roots_scrut Σ1 branches v_tail
		                  (ty_core T_head)
		                  (root_env_remove_match_params ps_head R_head_payload)
		                  Σ_tail Ts_tail roots_tail
		                  variant_name vdef_tail e_branch
		                  ltac:(match goal with
		                    | Htail : typed_match_tail_roots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
		                        exact Htail
		                    end)
		                  Hvariant_tail
		                  Hlookup_branch)
	        as [T_branch
	            [Σ_branch
	            [R_branch_payload
	            [R_branch
	            [roots_branch
	            [ps_branch
		            [binders_branch
		            [R_payload
		            Htail_branch]]]]]]]].
	      destruct Htail_branch as [HRpayload Htail_branch].
	      destruct Htail_branch as [Hnodup_branch_params Htail_branch].
	      destruct Htail_branch as [Hctx_none_branch Htail_branch].
	      destruct Htail_branch as [Hroot_none_branch Htail_branch].
	      destruct Htail_branch as [Hbinders_branch Htail_branch].
	      destruct Htail_branch as [Hparams_branch Htail_branch].
	      destruct Htail_branch as [Htyped_branch Htail_branch].
	      destruct Htail_branch as [Hparams_ok_branch Htail_branch].
	      destruct Htail_branch as [Hroots_excl_branch Htail_branch].
	      destruct Htail_branch as [Hremove_branch Htail_branch].
	      destruct Htail_branch as [Henv_excl_branch Htail_branch].
	      destruct Htail_branch as [Hcore_branch Htail_branch].
	      destruct Htail_branch as [Hequiv_branch Hin_roots].
	      assert (Hbinders_same : binders_branch = binders).
	      { rewrite Hlookup_binders in Hbinders_branch.
	        inversion Hbinders_branch. reflexivity. }
	      subst binders_branch.
	      assert (Hnames_payload : ctx_names (params_ctx ps) =
	        ctx_names (params_ctx ps_branch)).
	      { rewrite (match_payload_params_opt_names binders lts args vdef ps Hparams).
	        rewrite (match_payload_params_opt_names binders lts0 args0 vdef_tail
	          ps_branch Hparams_branch).
	        reflexivity. }
	      pose proof (value_roots_within_enum_payloads roots_scrut enum_name
	        variant_name lts args values Hv_scrut) as Hvalues_roots.
	      assert (Hroots_payload :
	        store_roots_within R_payload (bind_params ps values s_scrut)).
	      { subst R_payload.
	        eapply store_roots_within_bind_params_roots_same_names.
	        - exact Hnames_payload.
		        - exact Hnodup_branch_params.
		        - exact Hroot_none_branch.
	        - exact Hroots_scrut.
	        - exact Hvalues_roots.
	        - exact Hlen. }
	      destruct (IHbranch Ω n R_payload (sctx_add_params ps_branch Σ1)
	                  T_branch Σ_branch R_branch_payload roots_branch
	                  Hready_branch Hroots_payload
	                  ltac:(apply bind_params_store_no_shadow_names;
	                        [ eapply params_names_nodup_b_sound;
	                          eapply params_names_nodup_b_names;
		                          [ symmetry; exact Hnames_payload
		                          | exact Hnodup_branch_params ]
		                        | eapply store_roots_within_params_fresh_in_store;
		                          [ eapply root_env_lookup_params_none_b_names;
		                            [ symmetry; exact Hnames_payload
		                            | exact Hroot_none_branch ]
	                          | exact Hroots_scrut ]
	                        | exact Hlen
	                        | exact Hnodup_scrut ])
	                  ltac:(subst R_payload;
	                        eapply root_env_add_params_roots_same_no_shadow; eauto)
	                  Htyped_branch)
	        as [Hroots_branch [Hv_branch [Hnodup_branch Hrn_branch]]].
	      repeat split.
	      * rewrite Hstore.
	        eapply store_roots_within_equiv.
	        -- exact Hequiv_branch.
	        -- rewrite Hremove_branch.
	           eapply store_roots_within_remove_match_params_names.
	           ++ exact Hnames_payload.
	           ++ exact Hroots_branch.
	           ++ eapply params_names_nodup_b_sound.
	              exact Hnodup_branch_params.
	           ++ exact Hnodup_branch.
	      * apply value_roots_within_union_r.
	        eapply value_roots_within_root_sets_union_in; eassumption.
	      * rewrite Hstore.
	        apply store_no_shadow_remove_params. exact Hnodup_branch.
	      * apply root_env_remove_match_params_no_shadow.
	        eapply typed_env_roots_no_shadow.
	        -- exact Htyped2.
	        -- eapply root_env_add_params_roots_same_no_shadow; eauto.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
		      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
		      roots Hready _ _ _ _.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args0 vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ
	      T Σ' R' roots Hready _ _ _ _.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
	      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee type_args args0 fname captured fdef fcall
      vs ret used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ ps Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ ps Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1_e ?R1_e ?roots_e,
      Htyped_rest : typed_args_roots env Ω n ?R1_e ?Σ1_e es ?ps_rest
        Σ' R' ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1_e R1_e roots_e
                    Hready_e Hroots Hnodup Hrn Htyped_e)
          as [Hroots1 [Hv [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n R1_e Σ1_e ps_rest Σ' R' roots_rest
                    Hready_rest Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hroots2 [Hvs [Hnodup2 Hrn2]]]
    end.
    repeat split; try assumption.
    constructor; assumption.
  - intros s Ω n lts args0 R Σ Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args0 R Σ Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1_field
        ?R1_field ?roots_field,
      Htyped_rest : typed_fields_roots env Ω n lts args0 ?R1_field ?Σ1_field
        ?fields0 rest Σ' R' ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1_field R1_field roots_field
                    Hready_field Hroots Hnodup Hrn Htyped_field)
          as [Hroots1 [Hv [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n lts args0 R1_field Σ1_field Σ' R' roots_rest
                    Hready Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hroots2 [Hvals [Hnodup2 Hrn2]]]
    end.
    repeat split; try assumption.
    constructor.
    + apply value_roots_within_union_l. exact Hv.
    + apply value_fields_roots_within_union_r. exact Hvals.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
      Hready Hroots Hnodup Hrn Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0'
        R0' roots0 Hready Hroots Hnodup Hrn Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 Hready Hroots Hnodup Hrn Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

Definition eval_preserves_typing_ready_prefix_for_roots_ready_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').

Theorem eval_preserves_roots_ready_prefix_mutual_with_preservation_core :
  eval_preserves_typing_ready_prefix_for_roots_ready_statement ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s').
Proof.
  intros Hpreservation_prefix.
  split.
  - intros env s e s' v Heval Ω n R Σ T Σ' R' roots
      Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 Hpreservation_prefix
                env s e s' v Heval Ω n Σ T Σ' Hpres_ready Hstore
                (typed_env_roots_structural env Ω n R Σ e T Σ' R' roots
                  Htyped))
      as [Hstore' [_ Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env s args s' vs Heval Ω n R Σ ps Σ' R' roots
        Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 Hpreservation_prefix)
                  env s args s' vs Heval Ω n Σ ps Σ' Hpres_ready Hstore
                  (typed_args_roots_structural env Ω n R Σ args ps Σ' R'
                    roots Htyped))
        as [Hstore' [_ Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
                  env s args s' vs Heval Ω n R Σ ps Σ' R' roots
                  Hprov Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
        roots Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj2 (proj2 Hpreservation_prefix)
                  env s fields defs s' values Heval Ω n lts args Σ Σ'
                  Hpres_ready Hstore
                  (typed_fields_roots_structural env Ω n lts args R Σ
                    fields defs Σ' R' roots Htyped))
        as [Hstore' [_ Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual)
                  env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
                  roots Hprov Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.
