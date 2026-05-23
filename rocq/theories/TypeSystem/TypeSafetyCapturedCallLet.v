From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness
  TypeSafetyRootEnvParams.
From Facet.TypeSystem Require Export TypeSafetyCapturedCallMake.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params.
    - unfold fn_body_ctx, fn_body_params in Htyped_renamed.
      exact Htyped_renamed.
    - exact Hrn_initial_r.
    - exact Hexclude_roots_renamed. }
  assert (Hsubset_inst_input :
    root_set_stores_subset (root_set_instantiate
      (root_subst_of_params
        (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ capture_store_root_sets captured))
      roots_body_r)
      (root_sets_union
        (arg_roots ++ capture_store_root_sets captured))).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union.
    - unfold fn_body_ctx, fn_body_params in Htyped_renamed.
      exact Htyped_renamed.
    - exact Hrn_initial_r.
    - exact Hexclude_roots_renamed.
    - apply root_set_equiv_refl. }
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
