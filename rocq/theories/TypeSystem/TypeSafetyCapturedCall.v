From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyDirectCall.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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
