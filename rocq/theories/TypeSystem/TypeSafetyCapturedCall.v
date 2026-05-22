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

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args s_body vs ret R_args Σ_args arg_roots captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  intros Htyping Hroots Hnames Hkeys Hframe Hprefix Hparam env Ω n R Σ
    args fname captures captured fdef fcall used' s s_args s_body vs ret
    R_args Σ_args arg_roots captured_tys T_body Γ_out R_body roots_body
    Hstore Hroots_store Hshadow Hrn Hnamed Hkeys_named Heval_make Hlookup
    Heval_args Hrename Heval_body Hcheck Hnodup_caps Hready_args
    Htyped_args Hprov_body Htyped_body Hcompat_body Hexclude_roots
    Hexclude_env.
  destruct
    (eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core
      Htyping (eval_preserves_roots_ready_mutual_statement_to_package Hroots)
      Hnames Hkeys env Ω n R Σ args fname captures
      captured fdef fcall used' s s_args vs R_args Σ_args arg_roots
      captured_tys Hstore Hroots_store Hshadow Hrn Hnamed Hkeys_named
      Heval_make Hlookup Heval_args Hrename Hcheck Hnodup_caps
      Hready_args Htyped_args)
    as [[Hframe_ready Hcaptured_params_typed]
        [Hstore_args [Hargs_fcall [_ [Hroots_bind [Hshadow_bind
          [Hrn_bind Hcover_params]]]]]]].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hcover_all :
    root_env_covers_params (fn_params fcall ++ fn_captures fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))).
  { eapply captured_call_runtime_root_env_covers_params_captures;
      eassumption. }
  destruct
    (eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
      Hframe
      Hprefix
      Hparam env Ω s s_args s_body args fname captures
      captured fdef fcall vs ret used' (empty_root_env_for_store captured)
      R_args Σ Σ_args captured_tys [] T_body Γ_out
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      R_body roots_body Hstore Heval_make Hlookup Heval_args Hrename
      Heval_body Hcheck Hframe_ready Hstore_args Hargs_fcall Hroots_bind
      Hshadow_bind Hrn_bind Hcover_all Hprov_body Htyped_body
      Hcompat_body Hexclude_roots Hexclude_env)
    as [Heval_final [Hstore_final Hv_final]].
  repeat split; assumption.
Qed.

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args s_body vs ret R_args Σ_args arg_roots env_lt captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  intros Htyping Hroots_mutual Hnames Hkeys_mutual Hframe Hprefix Hparam
    env Ω n R Σ args fname captures captured fdef fcall used'
    s s_args s_body vs ret R_args Σ_args arg_roots env_lt captured_tys
    T_body Γ_out R_body roots_body Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Heval_make Hlookup Heval_args Hrename Heval_body Hcheck Hnodup_caps
    Hready_args Htyped_args Hnodup_binding Hprov_body Htyped_body
    Hcompat_body Hexclude_roots Hexclude_env.
  destruct (eval_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_core
              Htyping (eval_preserves_roots_ready_mutual_statement_to_package Hroots_mutual)
              Hnames Hkeys_mutual env Ω n R Σ args fname captures captured fdef fcall used'
              s s_args vs R_args Σ_args arg_roots env_lt captured_tys
              Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval_make Hlookup
              Heval_args Hrename Hcheck Hnodup_caps Hready_args
              Htyped_args)
    as [[Hframe_ready Hcaptured_params_typed]
        [Hstore_args [Hargs_fcall [Hvalue_roots [Hroots_bind
          [Hshadow_bind [Hrn_bind Hcover_params]]]]]]].
  pose proof
    (eval_make_closure_copy_capture_store_as_ts
      env s fname captures captured fdef Heval_make Hlookup) as Hcopy.
  destruct (alpha_rename_fn_def_binding_initial_support_facts
              (store_names (captured ++ s_args)) fdef fcall used'
              Hrename Hnodup_binding)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_binding & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names (captured ++ s_args)) fdef fcall used'
              Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Hlen_captured_fdef :
    List.length captured = List.length (fn_captures fdef)).
  { pose proof Hcaptured_params_typed as Hcaptured_params_len.
    unfold captured_params_store_typed_in_frame in Hcaptured_params_len.
    pose proof (Forall2_length Hcaptured_params_len) as Hlen_captured.
    rewrite params_ctx_length_ts in Hlen_captured.
    rewrite Hcaps_eq in Hlen_captured. exact Hlen_captured. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx fdef))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
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
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_params
                (fn_params fdef ++ fn_captures fdef))
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (sctx_of_ctx (fn_body_ctx fdef))
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_binding Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_binding.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_binding.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_binding_roots :
    List.length
      (arg_roots ++ capture_store_root_sets captured) =
    List.length (fn_params fdef ++ fn_captures fdef)).
  { rewrite length_app, capture_store_root_sets_length, length_app.
    rewrite Hlen_arg_roots_fdef.
    unfold captured_params_store_typed_in_frame in Hcaptured_params_typed.
    pose proof (Forall2_length Hcaptured_params_typed) as Hlen_captured.
    rewrite params_ctx_length_ts in Hlen_captured.
    rewrite Hlen_captured.
    rewrite Hcaps_eq. reflexivity. }
  assert (Harg_roots_named_sargs :
    Forall (fun roots => root_set_store_roots_named roots s_args)
      arg_roots).
  { pose proof (preservation_ready_args_implies_provenance_ready_closure
                  args Hready_args) as Hprov_args.
    destruct (proj1 (proj2 Hnames)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hbinding_roots_named :
    Forall
      (fun roots => root_set_store_roots_named roots (captured ++ s_args))
      (arg_roots ++ capture_store_root_sets captured)).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_weaken_store.
      + exact Harg_roots_named_sargs.
      + intros z Hin. rewrite store_names_app.
        apply in_or_app. right. exact Hin.
    - eapply capture_store_root_sets_store_roots_named_in_frame.
      exact Hcaptured_params_typed. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ capture_store_root_sets captured))).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Hbinding_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  assert (Hparams_fresh_captured :
    params_fresh_in_store (fn_params fcall) captured).
  { assert (Hfresh :
      params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
    { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
    unfold params_fresh_in_store in *.
    intros x Hin Hstore_x. apply (Hfresh x Hin).
    rewrite store_names_app. apply in_or_app. left. exact Hstore_x. }
  assert (Hbase_equiv :
    root_env_equiv
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured))
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ capture_store_root_sets captured))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall)))).
  { eapply captured_call_binding_runtime_root_env_equiv_with_roots.
    - exact Hrename.
    - exact Hnodup_binding.
    - exact Hlen_arg_roots_fdef.
    - rewrite capture_store_root_sets_length.
      unfold captured_params_store_typed_in_frame in Hcaptured_params_typed.
      pose proof (Forall2_length Hcaptured_params_typed) as Hlen_captured.
      rewrite params_ctx_length_ts in Hlen_captured.
      rewrite Hlen_captured.
      rewrite Hcaps_eq. reflexivity.
    - eapply capture_store_root_env_equiv_root_env_add_params_roots_in_frame.
      exact Hcaptured_params_typed.
    - intros x Hin.
      apply root_env_lookup_not_in_names.
      rewrite capture_store_root_env_names.
      exact (Hparams_fresh_captured x Hin). }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hrn_base :
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured))).
  { apply call_param_root_env_no_shadow.
    - exact Hnodup_fcall.
    - unfold captured_call_frame_ready_in_frame in Hframe_ready.
      destruct Hframe_ready as [[_ [_ [_ [Hrn_cap _]]]] _].
      exact Hrn_cap. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params
                (fn_params fdef ++ fn_captures fdef)
                (arg_roots ++ capture_store_root_sets captured))
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots
                (capture_store_root_env captured))
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_base)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & _ & Hbody_inst_equiv & Hroots_inst_equiv).
  { exact Hbase_equiv. }
  assert (Hfresh_binding_sargs :
    params_fresh_in_store (fn_params fcall ++ fn_captures fcall) s_args).
  { unfold params_fresh_in_store.
    intros x Hin Hstore_x.
    rewrite params_ctx_app, ctx_names_app in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_caps].
    - assert (Hfresh :
        params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
      { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
      apply (Hfresh x Hin_params).
      rewrite store_names_app. apply in_or_app. right. exact Hstore_x.
    - pose proof (captured_params_store_typed_in_frame_store_param_prefix
                    env captured s_args (fn_captures fcall)
                    Hcaptured_params_typed) as Hprefix_caps0.
      pose proof (store_param_prefix_append_frame
                    (fn_captures fcall) captured s_args []
                    Hprefix_caps0) as Hprefix_caps.
      simpl in Hprefix_caps.
      assert (Hshadow_frame : store_no_shadow (captured ++ s_args)).
      { unfold captured_call_frame_ready_in_frame in Hframe_ready.
        destruct Hframe_ready as [_ [_ [Hshadow_frame _]]].
        exact Hshadow_frame. }
      pose proof (store_param_prefix_frame_static_fresh
                    (fn_captures fcall) (captured ++ s_args) s_args
                    Hprefix_caps Hshadow_frame) as Hfresh_caps.
      apply (Hfresh_caps x).
      + unfold sctx_of_ctx. exact Hin_caps.
      + exact Hstore_x. }
  assert (Hcap_roots_named_frame :
    Forall
      (fun roots => root_set_store_roots_named roots (captured ++ s_args))
      (capture_store_root_sets captured)).
  { eapply capture_store_root_sets_store_roots_named_in_frame.
    exact Hcaptured_params_typed. }
  assert (Hcap_roots_named_s :
    Forall (fun roots => root_set_store_roots_named roots s)
      (capture_store_root_sets captured)).
  { eapply capture_store_root_sets_store_roots_named_in_store.
    eapply copy_capture_store_as_captured_entries_typed_with_env_preserved.
    - exact Hstore.
    - apply store_ref_targets_preserved_refl.
    - exact Hcopy.
    - exact Hcheck. }
  assert (Hfresh_caps_s :
    params_fresh_in_store (fn_captures fcall) s).
  { rewrite Hcaps_eq.
    eapply check_make_closure_captures_exact_sctx_with_env_params_fresh_in_store;
      eassumption. }
  assert (Hbinding_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall ++ fn_captures fcall))
      (arg_roots ++ capture_store_root_sets captured)).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_excludes_params; eassumption.
    - apply Forall_forall. intros roots Hin_roots.
      unfold roots_exclude_params.
      intros x Hin_x.
      rewrite params_ctx_app, ctx_names_app in Hin_x.
      apply in_app_or in Hin_x as [Hin_params | Hin_caps].
      + assert (Hroot_named :
          root_set_store_roots_named roots (captured ++ s_args)).
        { apply (proj1 (Forall_forall _ _) Hcap_roots_named_frame).
          exact Hin_roots. }
        assert (Hfresh_params_frame :
          params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
        { eapply alpha_rename_fn_def_params_fresh_in_store.
          exact Hrename. }
        pose proof
          (root_set_store_roots_named_excludes_params
            (fn_params fcall) roots (captured ++ s_args)
            Hroot_named Hfresh_params_frame)
          as Hexcl_params.
        apply Hexcl_params. exact Hin_params.
      + assert (Hroot_named :
          root_set_store_roots_named roots s).
        { apply (proj1 (Forall_forall _ _) Hcap_roots_named_s).
          exact Hin_roots. }
        pose proof
          (root_set_store_roots_named_excludes_params
            (fn_captures fcall) roots s
            Hroot_named Hfresh_caps_s)
          as Hexcl_caps.
        apply Hexcl_caps. exact Hin_caps. }
  assert (Himages_exclude :
    forall x,
      In x
        (ctx_names
          (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ capture_store_root_sets captured))).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Hbinding_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { unfold root_env_tail_fresh_names.
    intros y Hin.
    unfold captured_call_frame_ready_in_frame in Hframe_ready.
    destruct Hframe_ready as [_ [_ [_ [Hrn_tail
      [Hnamed_tail Hkeys_tail]]]]].
    assert (Hkeys_args : root_env_store_keys_named R_args
      (captured ++ s_args)).
    { unfold root_env_store_keys_named, root_env_keys_named in *.
      intros z Hz.
      apply Hkeys_tail.
      rewrite root_env_names_app.
      apply in_or_app. right. exact Hz. }
    assert (Hnamed_args : root_env_store_roots_named R_args
      (captured ++ s_args)).
    { unfold root_env_store_roots_named in *.
      intros z roots r Hlookup_args Hin_root.
      eapply Hnamed_tail.
      - assert (Hlookup_cap :
          root_env_lookup z (capture_store_root_env captured) = None).
        { eapply root_env_no_shadow_app_lookup_right_none; eassumption. }
        rewrite (root_env_lookup_app_right z
          (capture_store_root_env captured) R_args Hlookup_cap).
        exact Hlookup_args.
      - exact Hin_root. }
    pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                  (store_names (captured ++ s_args)) fdef fcall used'
                  Hrename) as Hfresh_names.
    assert (Hfresh_y : ~ In y (store_names (captured ++ s_args))).
    { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
    assert (Hlookup_y : root_env_lookup y R_args = None).
    { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
    assert (Hexcl_y : root_env_excludes y R_args).
    { eapply root_env_store_roots_named_excludes_name; eassumption. }
    assert (Hrn_args0 : root_env_no_shadow R_args).
    { unfold root_env_no_shadow in *.
      rewrite root_env_names_app in Hrn_tail.
      eapply NoDup_app_right_ts. exact Hrn_tail. }
    split.
    - apply root_env_lookup_remove_params_none_preserved. exact Hlookup_y.
    - eapply root_env_remove_params_preserves_excludes.
      + exact Hrn_args0.
      + exact Hexcl_y. }
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold captured_call_frame_ready_in_frame in Hframe_ready.
    destruct Hframe_ready as [_ [_ [_ [Hrn_tail _]]]].
    unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_tail.
    eapply NoDup_app_right_ts. exact Hrn_tail. }
  assert (Hnamed_args : root_env_store_roots_named R_args s_args).
  { pose proof (preservation_ready_args_implies_provenance_ready_closure
                  args Hready_args) as Hprov_args.
    destruct (proj1 (proj2 Hnames)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args)
      as [Henv_named _].
    exact Henv_named. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { eapply captured_call_runtime_args_tail_excludes_binding_params;
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured) ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_decompose :
    call_param_root_env (fn_params fcall) arg_roots
      (capture_store_root_env captured ++ R_args) =
    call_param_root_env (fn_params fcall) arg_roots
      (capture_store_root_env captured) ++
      root_env_remove_params (fn_params fcall) R_args).
  { apply captured_call_runtime_root_env_tail_decompose.
    intros x Hin.
    apply root_env_lookup_not_in_names.
    rewrite capture_store_root_env_names.
    exact (Hparams_fresh_captured x Hin). }
  assert (Htyped_tail_roots :
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++ R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { rewrite Houts. rewrite Hlts.
    rewrite Htail_decompose.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_tail. }
  assert (Hcompat_fcall :
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true).
  { rewrite Houts. rewrite Hret. exact Hcompat_body. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hnodup_binding_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall ++ fn_captures fcall)))).
  { pose proof (store_param_prefix_bind_params
                  env Ω (captured ++ s_args) vs (fn_params fcall)
                  Hargs_fcall) as Hprefix_params.
    pose proof (captured_params_store_typed_in_frame_store_param_prefix
                  env captured s_args (fn_captures fcall)
                  Hcaptured_params_typed) as Hprefix_caps0.
    pose proof (store_param_prefix_append_frame
                  (fn_captures fcall) captured s_args []
                  Hprefix_caps0) as Hprefix_caps.
    simpl in Hprefix_caps.
    pose proof (store_param_prefix_app
                  (fn_params fcall) (fn_captures fcall)
                  (bind_params (fn_params fcall) vs (captured ++ s_args))
                  (captured ++ s_args) s_args
                  Hprefix_params Hprefix_caps) as Hprefix_all.
    pose proof (store_names_store_param_prefix
                  (fn_params fcall ++ fn_captures fcall)
                  (bind_params (fn_params fcall) vs (captured ++ s_args))
                  s_args Hprefix_all) as Hnames_prefix.
    unfold store_no_shadow in Hshadow_bind.
    rewrite Hnames_prefix in Hshadow_bind.
    exact (NoDup_app_left_ts _ _ Hshadow_bind). }
  assert (Hcover_all :
    root_env_covers_params (fn_params fcall ++ fn_captures fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++ R_args))).
  { eapply captured_call_runtime_root_env_covers_params_captures_with_roots.
    - exact Hnodup_binding_fcall.
    - exact Hlen_arg_roots_fcall.
    - rewrite capture_store_root_sets_length.
      rewrite Hcaps_eq.
      exact Hlen_captured_fdef.
    - eapply capture_store_root_env_equiv_root_env_add_params_roots_in_frame.
      exact Hcaptured_params_typed.
    - intros x Hin.
      apply root_env_lookup_not_in_names.
      rewrite capture_store_root_env_names.
      exact (Hparams_fresh_captured x Hin). }
  destruct
    (eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
      Hframe
      Hprefix
      Hparam env Ω s s s_args s_body
      (EMakeClosure fname captures) args fname captured fdef fcall vs ret
      used' (capture_store_root_env captured) R_args Σ_args [] T_body
      Γ_out_r
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++ R_args))
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst Heval_make Hlookup Heval_args Hrename Heval_body
      (conj Hframe_ready Hcaptured_params_typed) Hstore_args Hargs_fcall
      Hroots_bind Hshadow_bind Hrn_bind Hcover_all Hprov_fcall
      Htyped_tail_roots Hcompat_fcall Hexclude_roots_inst Hexclude_env_tail)
    as [Heval_final [Hstore_final [Hv_final _]]].
  repeat split; assumption.
Qed.


Lemma eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env Ω n R Σ m x T args fname captures fdef
      s s_final ret R_args Σ_args arg_roots env_lt captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args)) s_final ret ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    lookup_fn fname (env_fns env) = Some fdef ->
    ~ In x (store_names s) ->
    ~ In x (ctx_names (params_ctx (fn_captures fdef))) ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_typed env s_final Σ_args /\
    value_has_type env s_final ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  intros Htyping Hroots_mutual Hnames Hkeys_mutual Hframe Hprefix Hparam
    env Ω n R Σ m x T args fname captures fdef s s_final ret
    R_args Σ_args arg_roots env_lt captured_tys T_body Γ_out R_body roots_body
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Husage Heval Hcheck Hnodup_caps
    Hready_args Htyped_args Hnodup_binding Hprov_body Htyped_body
    Hcompat_body Hexclude_roots Hexclude_env Hlookup Hfresh_s
    Hfresh_cap_names Hfree_args Hlocal_args.
  assert (Hrefs_s : store_refs_exclude_root x s).
  { eapply store_roots_within_named_fresh_refs_exclude_root; eassumption. }
  destruct (eval_let_make_closure_captured_call_args_strip
              env s s_final m x T fname captures args ret Husage Heval
              Hready_args Hfree_args Hlocal_args Hrefs_s)
    as (captured & fdef_pkg & s_args_hidden & s_args & vs & fcall &
        used' & s_body & Hlookup_pkg & Hcopy & Hhidden & Heval_args &
        Hrefs_args & Hvs_refs & Hrename & Heval_body & Hfinal).
  assert (Hfdef_eq : fdef_pkg = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef_pkg.
  assert (Hcleanup :
    forall sigma_result Σ_args0 T_body0 Γ_out0 R_params R_body0 roots_body0
        roots_bound,
      captured_params_store_typed_in_frame env captured s_args_hidden
        (fn_captures fcall) ->
      store_typed env s_args Σ_args0 ->
      eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
        (fn_params fcall) ->
      store_roots_within R_params
        (bind_params (fn_params fcall) vs
          (captured ++ s_args_hidden)) ->
      store_no_shadow
        (bind_params (fn_params fcall) vs
          (captured ++ s_args_hidden)) ->
      root_env_no_shadow R_params ->
      root_env_covers_params (fn_params fcall ++ fn_captures fcall)
        R_params ->
      provenance_ready_expr (fn_body fcall) ->
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        R_params (sctx_of_ctx (fn_body_ctx fcall))
        (fn_body fcall) T_body0 (sctx_of_ctx Γ_out0) R_body0
        roots_body0 ->
      ty_compatible_b (fn_outlives fcall) T_body0 (fn_ret fcall) = true ->
      roots_exclude_params (fn_params fcall ++ fn_captures fcall)
        roots_body0 ->
      root_set_stores_subset roots_body0 roots_bound ->
      roots_exclude x roots_bound ->
      store_typed env s_final Σ_args0 /\
      value_has_type env s_final ret
        (apply_lt_ty sigma_result (fn_ret fdef)) /\
      s_final = s_args).
  { intros sigma_result Σ_args0 T_body0 Γ_out0 R_params R_body0
      roots_body0 roots_bound Hcaptured_params0 Htyped_args0 Hargs_fcall0
      Hroots_bind0 Hshadow_bind0 Hrn_params0 Hcover_all0 Hprov_body0
      Htyped_body0 Hcompat_body0 Hexclude_all0 Hsubset0
      Hroot_exclude_bound0.
    subst s_final.
    eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core
              Hframe
              Hprefix
              Hparam); try eassumption.
    eapply roots_exclude_stores_subset; eassumption. }
  assert (Hfresh_captured : ~ In x (store_names captured)).
  { rewrite (copy_capture_store_as_store_names
               captures (fn_captures fdef) s captured Hcopy).
    exact Hfresh_cap_names. }
  destruct (eval_let_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_core
              Htyping (eval_preserves_roots_ready_mutual_statement_to_package Hroots_mutual)
              Hnames Hkeys_mutual env Ω n R Σ args fname captures captured fdef fcall used'
              s s_args_hidden s_args vs R_args Σ_args arg_roots
              env_lt captured_tys x T Hstore Hroots Hshadow Hrn Hnamed Hkeys
              Hlookup Hcopy Hhidden Heval_args Hrename Hcheck Hnodup_caps
              Hready_args Htyped_args Hfresh_s Hfresh_captured)
    as [[Hframe_ready Hcaptured_params_typed]
        [Hstore_args [Hargs_fcall [Hvalue_roots [Hroots_bind
          [Hshadow_bind [Hrn_bind Hcover_params]]]]]]].
  destruct (alpha_rename_fn_def_binding_initial_support_facts
              (store_names (captured ++ s_args_hidden)) fdef fcall used'
              Hrename Hnodup_binding)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_binding & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names (captured ++ s_args_hidden)) fdef fcall used'
              Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx fdef))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
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
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_params
                (fn_params fdef ++ fn_captures fdef))
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (sctx_of_ctx (fn_body_ctx fdef))
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_binding Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_binding.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_binding.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape
                (store_names (captured ++ s_args_hidden)) fdef fcall used'
                Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hlen_captured_fdef :
    List.length (capture_store_root_sets captured) =
    List.length (fn_captures fdef)).
  { rewrite capture_store_root_sets_length.
    unfold captured_params_store_typed_in_frame in Hcaptured_params_typed.
    pose proof (Forall2_length Hcaptured_params_typed) as Hlen_captured.
    rewrite params_ctx_length_ts in Hlen_captured.
    rewrite Hlen_captured.
    rewrite Hcaps_eq. reflexivity. }
  assert (Harg_roots_named_sargs :
    Forall (fun roots => root_set_store_roots_named roots s_args)
      arg_roots).
  { pose proof (preservation_ready_args_implies_provenance_ready_closure
                  args Hready_args) as Hprov_args.
    destruct (proj1 (proj2 Hnames)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hbinding_roots_named :
    Forall
      (fun roots =>
        root_set_store_roots_named roots (captured ++ s_args_hidden))
      (arg_roots ++ capture_store_root_sets captured)).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_weaken_store.
      + exact Harg_roots_named_sargs.
      + intros z Hin. rewrite store_names_app.
        apply in_or_app. right.
        subst s_args_hidden. simpl. right. exact Hin.
    - eapply capture_store_root_sets_store_roots_named_in_frame.
      exact Hcaptured_params_typed. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ capture_store_root_sets captured))).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Hbinding_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  assert (Hparams_fresh_captured :
    params_fresh_in_store (fn_params fcall) captured).
  { assert (Hfresh :
      params_fresh_in_store (fn_params fcall) (captured ++ s_args_hidden)).
    { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
    unfold params_fresh_in_store in *.
    intros y Hin Hstore_y. apply (Hfresh y Hin).
    rewrite store_names_app. apply in_or_app. left. exact Hstore_y. }
  assert (Hbase_equiv :
    root_env_equiv
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured))
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ capture_store_root_sets captured))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall)))).
  { eapply captured_call_binding_runtime_root_env_equiv_with_roots.
    - exact Hrename.
    - exact Hnodup_binding.
    - exact Hlen_arg_roots_fdef.
    - exact Hlen_captured_fdef.
    - eapply capture_store_root_env_equiv_root_env_add_params_roots_in_frame.
      exact Hcaptured_params_typed.
    - intros y Hin.
      apply root_env_lookup_not_in_names.
      rewrite capture_store_root_env_names.
      exact (Hparams_fresh_captured y Hin). }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hrn_base :
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured))).
  { apply call_param_root_env_no_shadow.
    - exact Hnodup_fcall.
    - unfold captured_call_frame_ready_in_frame in Hframe_ready.
      destruct Hframe_ready as [[_ [_ [_ [Hrn_cap _]]]] _].
      exact Hrn_cap. }
  assert (Hfresh_binding_hidden :
    params_fresh_in_store (fn_params fcall ++ fn_captures fcall)
      s_args_hidden).
  { unfold params_fresh_in_store.
    intros y Hin Hstore_y.
    rewrite params_ctx_app, ctx_names_app in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_caps].
    - assert (Hfresh :
        params_fresh_in_store (fn_params fcall)
          (captured ++ s_args_hidden)).
      { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
      apply (Hfresh y Hin_params).
      rewrite store_names_app. apply in_or_app. right. exact Hstore_y.
    - pose proof (captured_params_store_typed_in_frame_store_param_prefix
                    env captured s_args_hidden (fn_captures fcall)
                    Hcaptured_params_typed) as Hprefix_caps0.
      pose proof (store_param_prefix_append_frame
                    (fn_captures fcall) captured s_args_hidden []
                    Hprefix_caps0) as Hprefix_caps.
      simpl in Hprefix_caps.
      assert (Hshadow_frame : store_no_shadow (captured ++ s_args_hidden)).
      { unfold captured_call_frame_ready_in_frame in Hframe_ready.
        destruct Hframe_ready as [_ [_ [Hshadow_frame _]]].
        exact Hshadow_frame. }
      pose proof (store_param_prefix_frame_static_fresh
                    (fn_captures fcall) (captured ++ s_args_hidden)
                    s_args_hidden Hprefix_caps Hshadow_frame) as Hfresh_caps.
      apply (Hfresh_caps y).
      + unfold sctx_of_ctx. exact Hin_caps.
      + exact Hstore_y. }
  assert (Hcap_roots_named_frame :
    Forall
      (fun roots =>
        root_set_store_roots_named roots (captured ++ s_args_hidden))
      (capture_store_root_sets captured)).
  { eapply capture_store_root_sets_store_roots_named_in_frame.
    exact Hcaptured_params_typed. }
  assert (Hcap_roots_named_s :
    Forall (fun roots => root_set_store_roots_named roots s)
      (capture_store_root_sets captured)).
  { eapply capture_store_root_sets_store_roots_named_in_store.
    eapply copy_capture_store_as_captured_entries_typed_with_env_preserved.
    - exact Hstore.
    - apply store_ref_targets_preserved_refl.
    - exact Hcopy.
    - exact Hcheck. }
  assert (Hfresh_caps_s :
    params_fresh_in_store (fn_captures fcall) s).
  { rewrite Hcaps_eq.
    eapply check_make_closure_captures_exact_sctx_with_env_params_fresh_in_store;
      eassumption. }
  assert (Hbinding_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall ++ fn_captures fcall))
      (arg_roots ++ capture_store_root_sets captured)).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_excludes_params.
      + exact Harg_roots_named_sargs.
      + intros y Hin Hstore_y.
        apply (Hfresh_binding_hidden y Hin).
        subst s_args_hidden. simpl. right. exact Hstore_y.
    - apply Forall_forall. intros roots Hin_roots.
      unfold roots_exclude_params.
      intros y Hin_y.
      rewrite params_ctx_app, ctx_names_app in Hin_y.
      apply in_app_or in Hin_y as [Hin_params | Hin_caps].
      + assert (Hroot_named :
          root_set_store_roots_named roots (captured ++ s_args_hidden)).
        { apply (proj1 (Forall_forall _ _) Hcap_roots_named_frame).
          exact Hin_roots. }
        assert (Hfresh_params_frame :
          params_fresh_in_store (fn_params fcall)
            (captured ++ s_args_hidden)).
        { eapply alpha_rename_fn_def_params_fresh_in_store.
          exact Hrename. }
        pose proof
          (root_set_store_roots_named_excludes_params
            (fn_params fcall) roots (captured ++ s_args_hidden)
            Hroot_named Hfresh_params_frame) as Hexclude_params.
        apply Hexclude_params. exact Hin_params.
      + assert (Hroot_named :
          root_set_store_roots_named roots s).
        { apply (proj1 (Forall_forall _ _) Hcap_roots_named_s).
          exact Hin_roots. }
        pose proof
          (root_set_store_roots_named_excludes_params
            (fn_captures fcall) roots s Hroot_named Hfresh_caps_s)
          as Hexclude_caps.
        apply Hexclude_caps. exact Hin_caps. }
  assert (Himages_exclude :
    forall y,
      In y
        (ctx_names
          (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude y
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ capture_store_root_sets captured))).
  { intros y Hin_y.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Hbinding_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_y. }
  assert (Hsame_body_r :
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx fcall)) Γ_out_r).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_renamed. }
  assert (Hroots_set_body_r :
    root_set_sctx_roots_named roots_body_r Γ_out_r).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    destruct (Hroots_expr
                (initial_root_env_for_params_origin
                  (fn_params fdef ++ fn_captures fdef)
                  (fn_params fcall ++ fn_captures fcall))
                (sctx_of_ctx (fn_body_ctx fcall))
                (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
                Htyped_renamed Hrn_initial_r
                (initial_root_env_for_params_origin_sctx_roots_named
                  (fn_params fdef ++ fn_captures fdef)
                  (fn_params fcall ++ fn_captures fcall)))
      as [_ Hroots_set].
    exact Hroots_set. }
    assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
    { eapply root_set_no_store_of_sctx_named_excludes_params.
      - exact Hsame_body_r.
      - exact Hroots_set_body_r.
      - exact Hexclude_roots_renamed. }
  assert (Hsubset_inst_input :
    root_set_stores_subset (root_set_instantiate
      (root_subst_of_params
        (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ capture_store_root_sets captured))
      roots_body_r)
      (root_sets_union
        (arg_roots ++ capture_store_root_sets captured))).
  { eapply root_set_instantiate_no_store_stores_subset_root_sets_union.
    exact Hroots_body_r_no_store. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall)
        (root_env_add x (root_sets_union (capture_store_root_sets captured))
          R_args))
      (expr_local_store_names (fn_body fcall))).
  { eapply captured_call_runtime_args_tail_fresh_names_for_fresh_call_in_frame;
      eassumption. }
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  pose proof (proj1 (proj2 Hnames)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args) as Hnames_args.
  destruct Hnames_args as [Hnamed_args Harg_roots_named].
  assert (Hprov_fcall0 : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Htyped_renamed_fcall :
    typed_env_roots_shadow_safe env (fn_outlives fcall)
      (fn_lifetimes fcall)
      (initial_root_env_for_params_origin
        (fn_params fdef ++ fn_captures fdef)
        (fn_params fcall ++ fn_captures fcall))
      (sctx_of_ctx (fn_body_ctx fcall)) (fn_body fcall) T_body
      Γ_out_r R_body_r roots_body_r).
  { rewrite Houts. rewrite Hlts. exact Htyped_renamed. }
  assert (Hcompat_fcall0 :
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true).
  { rewrite Houts. rewrite Hret. exact Hcompat_body. }
  destruct (captured_call_callee_body_root_shadow_provenance_instantiated_tail_frame_no_env
              env
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
              (fn_params fcall ++ fn_captures fcall))
              (call_param_root_env (fn_params fcall) arg_roots
                (capture_store_root_env captured))
              (root_env_remove_params (fn_params fcall)
                (root_env_add x
                  (root_sets_union (capture_store_root_sets captured))
                  R_args))
              fcall
              (root_subst_of_params
                (fn_params fdef ++ fn_captures fdef)
                (arg_roots ++ capture_store_root_sets captured))
              T_body (ctx_of_sctx Γ_out_r) R_body_r roots_body_r
              (root_sets_union
                (arg_roots ++ capture_store_root_sets captured)))
    as (T_body_i & Γ_out_i & R_body_i & roots_body_i &
        Hprov_fcall & Htyped_tail & Hcompat_fcall &
        Hexclude_roots_i & Hsubset_i);
    try exact Hprov_fcall0;
    try exact Htyped_renamed_fcall;
    try exact Hcompat_fcall0;
    try exact Hexclude_roots_renamed;
    try exact Hsubst_fresh;
    try exact Hrn_initial_r;
    try exact Hrn_base;
    try exact Hbase_equiv;
    try exact Himages_exclude;
    try exact Hsubset_inst_input;
    try exact Htail_fresh.
  assert (Htail_decompose :
    call_param_root_env (fn_params fcall) arg_roots
      (capture_store_root_env captured ++
        root_env_add x (root_sets_union (capture_store_root_sets captured))
          R_args) =
    call_param_root_env (fn_params fcall) arg_roots
      (capture_store_root_env captured) ++
      root_env_remove_params (fn_params fcall)
        (root_env_add x (root_sets_union (capture_store_root_sets captured))
          R_args)).
  { apply captured_call_runtime_root_env_tail_decompose.
    intros y Hin.
    apply root_env_lookup_not_in_names.
    rewrite capture_store_root_env_names.
    exact (Hparams_fresh_captured y Hin). }
  assert (Htyped_tail_roots :
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x
            (root_sets_union (capture_store_root_sets captured)) R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body_i (sctx_of_ctx Γ_out_i)
      (R_body_i ++
        root_env_remove_params (fn_params fcall)
          (root_env_add x
            (root_sets_union (capture_store_root_sets captured)) R_args))
      roots_body_i).
  { rewrite Htail_decompose. exact Htyped_tail. }
  assert (Hnodup_binding_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall ++ fn_captures fcall)))).
  { pose proof (store_param_prefix_bind_params
                  env Ω (captured ++ s_args_hidden) vs (fn_params fcall)
                  Hargs_fcall) as Hprefix_params.
    pose proof (captured_params_store_typed_in_frame_store_param_prefix
                  env captured s_args_hidden (fn_captures fcall)
                  Hcaptured_params_typed) as Hprefix_caps0.
    pose proof (store_param_prefix_append_frame
                  (fn_captures fcall) captured s_args_hidden []
                  Hprefix_caps0) as Hprefix_caps.
    simpl in Hprefix_caps.
    pose proof (store_param_prefix_app
                  (fn_params fcall) (fn_captures fcall)
                  (bind_params (fn_params fcall) vs
                    (captured ++ s_args_hidden))
                  (captured ++ s_args_hidden) s_args_hidden
                  Hprefix_params Hprefix_caps) as Hprefix_all.
    pose proof (store_names_store_param_prefix
                  (fn_params fcall ++ fn_captures fcall)
                  (bind_params (fn_params fcall) vs
                    (captured ++ s_args_hidden))
                  s_args_hidden Hprefix_all) as Hnames_prefix.
    unfold store_no_shadow in Hshadow_bind.
    rewrite Hnames_prefix in Hshadow_bind.
    exact (NoDup_app_left_ts _ _ Hshadow_bind). }
  assert (Hcover_all :
    root_env_covers_params (fn_params fcall ++ fn_captures fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x
            (root_sets_union (capture_store_root_sets captured)) R_args))).
  { eapply captured_call_runtime_root_env_covers_params_captures_with_roots.
    - exact Hnodup_binding_fcall.
    - exact Hlen_arg_roots_fcall.
    - rewrite Hcaps_eq. exact Hlen_captured_fdef.
    - eapply capture_store_root_env_equiv_root_env_add_params_roots_in_frame.
      exact Hcaptured_params_typed.
    - intros y Hin.
      apply root_env_lookup_not_in_names.
      rewrite capture_store_root_env_names.
      exact (Hparams_fresh_captured y Hin). }
  assert (Hroot_exclude_bound :
    roots_exclude x
      (root_sets_union
        (arg_roots ++ capture_store_root_sets captured))).
  { apply roots_exclude_root_sets_union.
    apply Forall_app. split.
    - apply Forall_forall. intros roots Hin_roots.
      eapply root_set_store_roots_named_excludes_name.
      + apply (proj1 (Forall_forall _ _) Harg_roots_named).
        exact Hin_roots.
      + pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                    env s args s_args vs Heval_args Hready_args)
          as Hnames_store.
        rewrite Hnames_store. exact Hfresh_s.
    - apply Forall_forall. intros roots Hin_roots.
      eapply root_set_store_roots_named_excludes_name.
      + apply (proj1 (Forall_forall _ _) Hcap_roots_named_s).
        exact Hin_roots.
      + exact Hfresh_s. }
  destruct (Hcleanup [] Σ_args T_body_i Γ_out_i
              (call_param_root_env (fn_params fcall) arg_roots
                (capture_store_root_env captured ++
                  root_env_add x
                    (root_sets_union (capture_store_root_sets captured))
                    R_args))
              (R_body_i ++
                root_env_remove_params (fn_params fcall)
                  (root_env_add x
                    (root_sets_union (capture_store_root_sets captured))
                    R_args))
              roots_body_i
              (root_sets_union
                (arg_roots ++ capture_store_root_sets captured))
              Hcaptured_params_typed Hstore_args Hargs_fcall Hroots_bind
              Hshadow_bind Hrn_bind Hcover_all Hprov_fcall Htyped_tail_roots
              Hcompat_fcall Hexclude_roots_i Hsubset_i
              Hroot_exclude_bound)
    as [Hstore_final [Hv_final _]].
  split; assumption.
Qed.
