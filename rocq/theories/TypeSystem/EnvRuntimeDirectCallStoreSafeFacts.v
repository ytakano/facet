From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeNarrowRuntimePackage.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

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


Lemma direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used' seed,
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
      (forall y, In y (store_names s_args) -> In y seed) ->
      alpha_rename_fn_def seed fdef = (fcall, used') ->
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
    param_tys ret_ty s s_args vs used' seed Hsummary Hcaps Hbridge Hsafe_args
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hseed_names Hrename.
  unfold callee_body_root_shadow_store_safe_narrow_summary in Hsummary.
  destruct Hsummary as
    (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup_fdef & Hsummary_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              seed fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              seed fdef fcall used' Hrename)
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
  pose proof (alpha_rename_fn_def_shape seed fdef fcall used' Hrename)
    as Hshape.
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
    - eapply ctx_alpha_nodup_names; eassumption.
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
    - eapply Forall_fresh_weaken.
      + intros y Hy.
        eapply alpha_rename_params_used_extends.
        * exact Hparams_rename.
        * apply in_or_app. right.
          apply in_or_app. right.
          apply in_or_app. right. apply Hseed_names. exact Hy.
      + eapply alpha_rename_expr_local_store_names_fresh_used.
        exact Hbody_rename. }
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
  { unfold params_fresh_in_store.
    intros y Hy Hstore_y.
    pose proof (alpha_rename_fn_def_params_fresh_used
      seed fdef fcall used' Hrename) as Hfresh_seed.
    pose proof (Hfresh_seed y Hy) as Hnot_seed.
    apply Hnot_seed. apply Hseed_names. exact Hstore_y. }
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
  { unfold root_env_tail_fresh_names.
    intros y Hy.
    destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args (params_of_tys param_tys)
              Sigma_args R_args arg_roots s s_args vs
              Hsafe_args Htyped_args Heval_args Hnamed Hkeys)
      as [Hnamed_args [_ Hkeys_args]].
    assert (Hfresh_y : ~ In y (store_names s_args)).
    { intro Hstore_y.
      pose proof (alpha_rename_expr_local_store_names_fresh_used
        rho used_params (fn_body fdef) (fn_body fcall) used' Hbody_rename)
        as Hfresh_body.
      pose proof (proj1 (Forall_forall _ _) Hfresh_body y Hy) as Hnot_used.
      apply Hnot_used.
      eapply alpha_rename_params_used_extends.
      - exact Hparams_rename.
      - apply in_or_app. right.
        apply in_or_app. right.
        apply in_or_app. right. apply Hseed_names. exact Hstore_y. }
    assert (Hlookup : root_env_lookup y R_args = None).
    { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
    assert (Hexcl : root_env_excludes y R_args).
    { eapply root_env_store_roots_named_excludes_name; eassumption. }
    split.
    - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
    - apply root_env_remove_params_preserves_excludes.
      + eapply typed_args_roots_no_shadow; eassumption.
      + exact Hexcl. }
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
  intros.
  eapply direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed;
    try eassumption.
  intros y Hy. exact Hy.
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
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
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
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
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
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
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
  | Halpha : alpha_rename_fn_def (store_names (captured ++ s_args)) fdef = _ |- _ =>
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





