From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyDirectCall.
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

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  (frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame)) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R')) ->
  ((forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame')) ->
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
      Htyping Hroots Hnames Hkeys env Ω n R Σ args fname captures
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
      Hframe Hprefix Hparam env Ω s s_args s_body args fname captures
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
