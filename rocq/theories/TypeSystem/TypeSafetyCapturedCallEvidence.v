From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCaptureFacts.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma alpha_rename_params_initial_root_env_rename_stable_tail_ts :
  forall used ps psr tail rho used',
    NoDup (ctx_names (params_ctx (ps ++ tail))) ->
    alpha_rename_params [] used ps = (psr, rho, used') ->
    root_env_rename rho (initial_root_env_for_params (ps ++ tail)) =
      initial_root_env_for_params_origin (ps ++ tail) (psr ++ tail).
Proof.
  intros used ps.
  revert used.
  induction ps as [| p ps IH]; intros used psr tail rho used' Hnodup Hrename.
  - simpl in Hrename. inversion Hrename; subst.
    induction tail as [| p tail IHtail]; simpl; try reflexivity.
    destruct p as [m x T]. simpl.
    inversion Hnodup; subst.
    change (root_env_rename [] (initial_root_env_for_params_origin tail tail))
      with (root_env_rename [] (initial_root_env_for_params ([] ++ tail))).
    change (initial_root_env_for_params_origin tail tail)
      with (initial_root_env_for_params_origin ([] ++ tail) ([] ++ tail)).
    rewrite (IHtail H2). reflexivity.
  - destruct p as [m x T]. simpl in Hrename.
    destruct (alpha_rename_params [] (fresh_ident x used :: used) ps)
      as [[ps'' rho''] used''] eqn:Hps.
    inversion Hrename; subst psr rho used'. simpl.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    rewrite ident_eqb_refl.
    rewrite root_env_rename_cons_initial_root_env_for_params_origin_notin.
    + change (root_env_rename rho''
          (initial_root_env_for_params_origin (ps ++ tail) (ps ++ tail)))
        with (root_env_rename rho'' (initial_root_env_for_params (ps ++ tail))).
      rewrite (IH (fresh_ident x used :: used) ps'' tail rho'' used''
        Hnodup_tail Hps).
      reflexivity.
    + exact Hnotin.
Qed.

Lemma alpha_rename_fn_def_binding_initial_support_facts :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params f ++ fn_captures f))) ->
    exists rho used_params,
      alpha_rename_params []
        (param_names (fn_params f) ++
         param_names (fn_captures f) ++ free_vars_expr (fn_body f) ++ used)
        (fn_params f) = (fn_params fr, rho, used_params) /\
      alpha_rename_expr rho used_params (fn_body f) =
        (fn_body fr, used') /\
      ctx_alpha rho
        (sctx_of_ctx (params_ctx (fn_params f ++ fn_captures f)))
        (sctx_of_ctx (params_ctx (fn_params fr ++ fn_captures fr))) /\
      root_env_no_shadow
        (initial_root_env_for_params (fn_params f ++ fn_captures f)) /\
      root_env_no_shadow
        (initial_root_env_for_params_origin
          (fn_params f ++ fn_captures f)
          (fn_params fr ++ fn_captures fr)) /\
      root_env_equiv
        (initial_root_env_for_params_origin
          (fn_params f ++ fn_captures f)
          (fn_params fr ++ fn_captures fr))
        (root_env_rename rho
          (initial_root_env_for_params (fn_params f ++ fn_captures f))) /\
      root_env_sctx_keys_named
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        (sctx_of_ctx (params_ctx (fn_params f ++ fn_captures f))) /\
      root_env_sctx_roots_named
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        (sctx_of_ctx (params_ctx (fn_params f ++ fn_captures f))) /\
      rename_no_collision_on rho
        (root_env_names
          (initial_root_env_for_params (fn_params f ++ fn_captures f))) /\
      (forall x,
        In x (ctx_names
          (sctx_of_ctx
            (params_ctx (fn_params fr ++ fn_captures fr)))) ->
        In x used_params) /\
      (forall x, In x (rename_range rho) -> In x used_params) /\
      disjoint_names (free_vars_expr (fn_body f)) (rename_range rho).
Proof.
  intros used f fr used' Hrename Hnodup_binding.
  assert (Hnodup_params : NoDup (ctx_names (params_ctx (fn_params f)))).
  { rewrite params_ctx_app, ctx_names_app in Hnodup_binding.
    eapply NoDup_app_left_ts. exact Hnodup_binding. }
  destruct (alpha_rename_fn_def_initial_support_facts
              used f fr used' Hrename Hnodup_params)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        _ & _ & _ & _ & _ & _ & _ & _ & Hrange_used & Hdisj).
  assert (Halpha_binding :
    ctx_alpha rho
      (sctx_of_ctx (params_ctx (fn_params f ++ fn_captures f)))
      (sctx_of_ctx (params_ctx (fn_params fr ++ fn_captures fr)))).
  { destruct f as [fname lifetimes outs captures ps ret body].
    unfold alpha_rename_fn_def in Hrename. simpl in *.
    destruct (alpha_rename_params []
      (param_names ps ++ param_names captures ++ free_vars_expr body ++ used)
      ps) as [[psr rho1] used1] eqn:Hps.
    destruct (alpha_rename_expr rho1 used1 body) as [bodyr used2] eqn:Hbody.
    inversion Hrename; subst. simpl in *.
    inversion Hparams_rename; subst.
    eapply alpha_rename_params_ctx_alpha_stable_tail. exact Hps. }
  assert (Hnodup_binding_r :
    NoDup (ctx_names
      (sctx_of_ctx (params_ctx (fn_params fr ++ fn_captures fr))))).
  { eapply ctx_alpha_nodup_names; eassumption. }
  assert (Hlen_binding :
    List.length (fn_params f ++ fn_captures f) =
    List.length (fn_params fr ++ fn_captures fr)).
  { pose proof (alpha_rename_fn_def_shape used f fr used' Hrename)
      as [_ [_ Hparams_alpha]].
    rewrite !length_app.
    rewrite <- (params_alpha_length _ _ Hparams_alpha).
    rewrite (alpha_rename_fn_def_captures used f fr used' Hrename).
    reflexivity. }
  destruct (alpha_rename_fn_def_params_body_facts
              used f fr used' Hrename)
    as (rho0 & used_params0 & Hparams_rename0 & _ & _ &
        Hctx_used_params & _ & _).
  rewrite Hparams_rename in Hparams_rename0.
  inversion Hparams_rename0; subst rho0 used_params0.
  exists rho, used_params.
  repeat split.
  - exact Hparams_rename.
  - exact Hbody_rename.
  - exact Halpha_binding.
  - apply initial_root_env_for_params_no_shadow. exact Hnodup_binding.
  - apply initial_root_env_for_params_origin_no_shadow.
    + exact Hlen_binding.
    + exact Hnodup_binding_r.
  - destruct f as [fname lifetimes outs captures ps ret body].
    unfold alpha_rename_fn_def in Hrename. simpl in *.
    destruct (alpha_rename_params []
      (param_names ps ++ param_names captures ++ free_vars_expr body ++ used)
      ps) as [[psr rho1] used1] eqn:Hps.
    destruct (alpha_rename_expr rho1 used1 body) as [bodyr used2] eqn:Hbody.
    inversion Hrename; subst. simpl in *.
	    inversion Hparams_rename; subst.
	    rewrite (alpha_rename_params_initial_root_env_rename_stable_tail_ts
	      (param_names ps ++ param_names captures ++ free_vars_expr body ++ used)
	      ps psr captures rho used_params Hnodup_binding Hps).
    apply root_env_equiv_refl.
  - unfold initial_root_env_for_params.
    apply initial_root_env_for_params_origin_sctx_keys_named. reflexivity.
  - unfold initial_root_env_for_params.
    apply initial_root_env_for_params_origin_sctx_roots_named.
  - rewrite initial_root_env_for_params_names.
    eapply ctx_alpha_no_collision_on; eassumption.
  - intros x Hin.
	    change (ctx_names
	      (sctx_of_ctx (params_ctx (fn_params fr ++ fn_captures fr))))
	      with (ctx_names (params_ctx (fn_params fr ++ fn_captures fr))) in Hin.
	    rewrite params_ctx_app, ctx_names_app in Hin.
	    apply in_app_or in Hin as [Hin | Hin].
    + apply Hctx_used_params. exact Hin.
    + eapply alpha_rename_params_used_extends.
	      * exact Hparams_rename.
	      * apply in_or_app. right. apply in_or_app. left.
	        rewrite <- (alpha_rename_fn_def_captures used f fr used' Hrename).
	        rewrite params_ctx_names_param_names in Hin.
	        exact Hin.
  - exact Hrange_used.
  - exact Hdisj.
Qed.

Lemma captured_call_callee_body_root_shadow_provenance_instantiated_bridge :
  forall env R_origin R_params
      fcall rho T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_origin
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      rho ->
    root_env_no_shadow R_origin ->
    root_env_no_shadow R_params ->
    root_env_equiv R_params (root_env_instantiate rho R_origin) ->
    (forall x,
      In x (ctx_names (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude x rho) ->
    callee_body_root_shadow_provenance_ready_at env fcall R_params.
Proof.
  intros env R_origin R_params fcall rho T_body Γ_out R_body
    roots_body Hprov Htyped Hcompat Hexclude_roots Hexclude_env
    Hsubst_fresh Hrn_origin Hrn_params Hparams_equiv Himages_exclude.
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fcall) (fn_lifetimes fcall) rho R_origin
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
              roots_body R_params Htyped Hsubst_fresh Hrn_origin
              Hrn_params Hparams_equiv)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env.
      + exact Himages_exclude. }
  unfold callee_body_root_shadow_provenance_ready_at.
  exists T_body, Γ_out, R_body_inst, roots_body_inst.
  repeat split; try assumption.
  - eapply roots_exclude_params_app_inv_l. exact Hexclude_roots_inst.
  - eapply root_env_excludes_params_app_inv_l. exact Hexclude_env_inst.
Qed.

Lemma captured_call_callee_body_root_shadow_provenance_instantiated_bridge_with_result_subset :
  forall env R_origin R_params
      fcall rho T_body Γ_out R_body roots_body result_roots,
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_origin
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      rho ->
    root_env_no_shadow R_origin ->
    root_env_no_shadow R_params ->
    root_env_equiv R_params (root_env_instantiate rho R_origin) ->
    (forall x,
      In x (ctx_names (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude x rho) ->
    root_set_stores_subset (root_set_instantiate rho roots_body)
      result_roots ->
    callee_body_root_shadow_provenance_ready_at_result_subset
      env fcall R_params result_roots.
Proof.
  intros env R_origin R_params fcall rho T_body Γ_out R_body
    roots_body result_roots Hprov Htyped Hcompat Hexclude_roots
    Hexclude_env Hsubst_fresh Hrn_origin Hrn_params Hparams_equiv
    Himages_exclude Hsubset.
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fcall) (fn_lifetimes fcall) rho R_origin
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
              roots_body R_params Htyped Hsubst_fresh Hrn_origin
              Hrn_params Hparams_equiv)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env.
      + exact Himages_exclude. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst result_roots).
  { eapply root_set_stores_subset_equiv.
    - exact Hroots_inst_equiv.
    - exact Hsubset. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Γ_out, R_body_inst, roots_body_inst.
  repeat split; try assumption.
  - eapply roots_exclude_params_app_inv_l. exact Hexclude_roots_inst.
  - eapply root_env_excludes_params_app_inv_l. exact Hexclude_env_inst.
Qed.

Lemma captured_call_callee_body_root_shadow_provenance_instantiated_tail_frame :
  forall env R_origin R_params_base R_tail fcall rho T_body Γ_out
      R_body roots_body roots_bound,
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_origin (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      rho ->
    root_env_no_shadow R_origin ->
    root_env_no_shadow R_params_base ->
    root_env_equiv R_params_base (root_env_instantiate rho R_origin) ->
    (forall x,
      In x (ctx_names (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude x rho) ->
    root_set_stores_subset (root_set_instantiate rho roots_body)
      roots_bound ->
    root_env_tail_fresh_names R_tail (expr_local_store_names (fn_body fcall)) ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_tail ->
    exists T_body_i Γ_out_i R_body_i roots_body_i,
      provenance_ready_expr (fn_body fcall) /\
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        (R_params_base ++ R_tail) (sctx_of_ctx (fn_body_ctx fcall))
        (fn_body fcall) T_body_i (sctx_of_ctx Γ_out_i)
        (R_body_i ++ R_tail) roots_body_i /\
      ty_compatible_b (fn_outlives fcall) T_body_i (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall ++ fn_captures fcall)
        roots_body_i /\
      root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
        (R_body_i ++ R_tail) /\
      root_set_stores_subset roots_body_i roots_bound.
Proof.
  intros env R_origin R_params_base R_tail fcall rho T_body Γ_out
    R_body roots_body roots_bound Hprov Htyped Hcompat Hexclude_roots
    Hexclude_env Hsubst_fresh Hrn_origin Hrn_params_base Hparams_equiv
    Himages_exclude Hsubset Htail_fresh Htail_exclude.
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fcall) (fn_lifetimes fcall) rho R_origin
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
              roots_body R_params_base Htyped Hsubst_fresh Hrn_origin
              Hrn_params_base Hparams_equiv)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & _ & Hbody_inst_equiv & Hroots_inst_equiv).
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env.
      + exact Himages_exclude. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst roots_bound).
  { eapply root_set_stores_subset_equiv.
    - exact Hroots_inst_equiv.
    - exact Hsubset. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      (R_params_base ++ R_tail) (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out)
      (R_body_inst ++ R_tail) roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  exists T_body, Γ_out, R_body_inst, roots_body_inst.
  repeat split; try assumption.
  - eapply typed_env_roots_shadow_safe_roots. exact Htyped_tail.
  - apply root_env_excludes_params_app; assumption.
Qed.

Lemma captured_call_callee_body_root_shadow_provenance_instantiated_tail_frame_no_env :
  forall env R_origin R_params_base R_tail fcall rho T_body Γ_out
      R_body roots_body roots_bound,
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_origin (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      rho ->
    root_env_no_shadow R_origin ->
    root_env_no_shadow R_params_base ->
    root_env_equiv R_params_base (root_env_instantiate rho R_origin) ->
    (forall x,
      In x (ctx_names (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude x rho) ->
    root_set_stores_subset (root_set_instantiate rho roots_body)
      roots_bound ->
    root_env_tail_fresh_names R_tail (expr_local_store_names (fn_body fcall)) ->
    exists T_body_i Γ_out_i R_body_i roots_body_i,
      provenance_ready_expr (fn_body fcall) /\
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        (R_params_base ++ R_tail) (sctx_of_ctx (fn_body_ctx fcall))
        (fn_body fcall) T_body_i (sctx_of_ctx Γ_out_i)
        (R_body_i ++ R_tail) roots_body_i /\
      ty_compatible_b (fn_outlives fcall) T_body_i (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall ++ fn_captures fcall)
        roots_body_i /\
      root_set_stores_subset roots_body_i roots_bound.
Proof.
  intros env R_origin R_params_base R_tail fcall rho T_body Γ_out
    R_body roots_body roots_bound Hprov Htyped Hcompat Hexclude_roots
    Hsubst_fresh Hrn_origin Hrn_params_base Hparams_equiv Himages_exclude
    Hsubset Htail_fresh.
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fcall) (fn_lifetimes fcall) rho R_origin
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
              roots_body R_params_base Htyped Hsubst_fresh Hrn_origin
              Hrn_params_base Hparams_equiv)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & _ & Hbody_inst_equiv & Hroots_inst_equiv).
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots.
      + exact Himages_exclude. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst roots_bound).
  { eapply root_set_stores_subset_equiv.
    - exact Hroots_inst_equiv.
    - exact Hsubset. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      (R_params_base ++ R_tail) (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out)
      (R_body_inst ++ R_tail) roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  exists T_body, Γ_out, R_body_inst, roots_body_inst.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped_tail.
Qed.
