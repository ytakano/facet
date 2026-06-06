From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectAlphaRuntimeFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma store_hidden_frame_rel_remove_base :
  forall x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    store_remove x s_with = s_without.
Proof.
  intros x T hidden s_with s_without Hrel.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH]; simpl.
  - rewrite ident_eqb_refl. reflexivity.
  - destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst. contradiction.
    + rewrite IH. reflexivity.
Qed.

Lemma store_hidden_frame_rel_store_names_base_subset :
  forall x T hidden s_with s_without y,
    store_hidden_frame_rel x T hidden s_with s_without ->
    In y (store_names s_without) ->
    In y (store_names s_with).
Proof.
  intros x T hidden s_with s_without y Hrel.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH]; simpl; intros Hy.
  - right. exact Hy.
  - destruct Hy as [Hy | Hy].
    + left. exact Hy.
    + right. apply IH. exact Hy.
Qed.

Lemma store_hidden_frame_rel_name_in :
  forall x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    In x (store_names s_with).
Proof.
  intros x T hidden s_with s_without Hrel.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH].
  - unfold store_add. simpl. left. reflexivity.
  - simpl. right. exact IH.
Qed.

Lemma store_hidden_frame_rel_params_fresh_in_store_base :
  forall x T hidden s_with s_without ps,
    store_hidden_frame_rel x T hidden s_with s_without ->
    params_fresh_in_store ps s_with ->
    params_fresh_in_store ps s_without.
Proof.
  intros x T hidden s_with s_without ps Hrel Hfresh.
  unfold params_fresh_in_store in *.
  induction Hrel as [s | se s_with s_without Hneq Hrel IH];
    intros y Hy Hin.
  - apply (Hfresh y Hy). unfold store_add. simpl. right. exact Hin.
  - simpl in Hin. destruct Hin as [Hy_head | Hin_tail].
    + apply (Hfresh y Hy). simpl. left. exact Hy_head.
    + apply (IH (fun z Hz Hzin => Hfresh z Hz (or_intror Hzin)) y Hy Hin_tail).
Qed.

Lemma eval_args_values_have_types_store_remove_excluding_root :
  forall env Omega s root vs ps,
    eval_args_values_have_types env Omega s vs ps ->
    Forall (value_refs_exclude_root root) vs ->
    eval_args_values_have_types env Omega (store_remove root s) vs ps.
Proof.
  intros env Omega s root vs ps Hargs Hrefs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - constructor.
  - inversion Hrefs; subst.
    eapply AHT_Cons with (T_actual := T_actual).
    + eapply value_has_type_store_remove_excluding_root; eassumption.
    + exact Hcompat.
    + apply IH. assumption.
Qed.

Lemma alpha_rename_fn_def_used_name_fresh_params_and_body_locals :
  forall used fdef fcall used' type_args x,
    alpha_rename_fn_def used fdef = (fcall, used') ->
    In x used ->
    ~ In x (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fcall)))) /\
    ~ In x (expr_local_store_names
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros used fdef fcall used' type_args x Hrename Hused.
  split.
  - rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    intro Hin.
    eapply alpha_rename_fn_def_params_fresh_used; eassumption.
  - rewrite expr_local_store_names_subst_type_params_expr.
    intro Hlocal.
    pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
      used fdef fcall used' Hrename) as Hfresh.
    rewrite Forall_forall in Hfresh.
    specialize (Hfresh x Hlocal).
    exact (Hfresh Hused).
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_ready_free_vars_ctx_names :
  forall env Omega n R Sigma e T Sigma' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Sigma e T Sigma' R' roots ret_roots ->
    preservation_ready_expr e ->
    forall x, In x (free_vars_expr e) -> In x (ctx_names Sigma).
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots ret_roots Hsummary Hready.
  inversion Hsummary; subst; intros y Hy; simpl in Hy;
    try contradiction.
  - dependent destruction Hready.
  - dependent destruction Hready.
  - dependent destruction Hready.
  - dependent destruction Hready.
  - first
      [ destruct Hy as [Heq | Htail]; [ rewrite <- Heq | contradiction ]
      | rewrite <- Hy
      | rewrite Hy ];
    dependent destruction H;
    solve [eauto using typed_place_root_name_in_ctx_names].
  - first
      [ destruct Hy as [Heq | Htail]; [ rewrite <- Heq | contradiction ]
      | rewrite <- Hy
      | rewrite Hy ];
    dependent destruction H;
    solve [eauto using typed_place_root_name_in_ctx_names].
  - first
      [ destruct Hy as [Heq | Htail]; [ rewrite <- Heq | contradiction ]
      | rewrite <- Hy
      | rewrite Hy ];
    dependent destruction H;
      match goal with
      | Hplace : typed_place_env_structural _ _ ?p _ |- In (place_name ?p) _ =>
          exact (typed_place_root_name_in_ctx_names _ _ _ _ Hplace)
      end.
  - dependent destruction Hready.
    dependent destruction Hready.
  - inversion Hy as [Heq | Hnil]; [subst y | contradiction].
    dependent destruction H;
      match goal with
      | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
          inversion Hplace; subst; eapply sctx_lookup_in_ctx_names; eassumption
      end.
  - dependent destruction Hready.
    inversion Hy as [Heq | Hnil]; [subst y | contradiction].
    dependent destruction H.
    dependent destruction H.
    all: solve [eauto using typed_place_root_name_in_ctx_names].
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_alpha_renamed_ready_body_free_vars_hidden_seed_excludes :
  forall env fuel fdef type_args fcall used' x T hidden s_hidden s_base,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def (store_names s_hidden) fdef = (fcall, used') ->
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcall)) ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros env fuel fdef type_args fcall used' x T hidden s_hidden s_base
    Hsummary Hcaps Hrename Hrel Hready Hin_free.
  pose proof (store_hidden_frame_rel_name_in x T hidden s_hidden s_base Hrel)
    as Hused.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    (store_names s_hidden) fdef fcall used' type_args x Hrename Hused)
    as [Hnot_params _].
  destruct (callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases
    env fuel fdef type_args Hsummary) as [Hexpr | Hgeneric].
  - destruct Hexpr as (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup & Hnarrow & Hcompat & Hexcl_roots & Hexcl_env).
    rewrite params_ctx_apply_type_params in Hnodup.
    rewrite ctx_names_subst_type_params_ctx in Hnodup.
    destruct (alpha_rename_fn_def_initial_support_facts
      (store_names s_hidden) fdef fcall used' Hrename Hnodup)
      as (rho & used_params & Hparams_rename & Hbody_rename &
          Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
          Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
          Hrange_used & Hdisj).
    assert (Hsummary_params :
      expr_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots).
    { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
      exact Hnarrow. }
    assert (Htyped_body :
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body).
    { eapply expr_root_shadow_store_safe_narrow_summary_typed.
      exact Hsummary_params. }
    assert (Hkeys_initial_subst :
      root_env_sctx_keys_named (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))).
    { unfold root_env_sctx_keys_named, root_env_keys_named in *.
      intros y Hin. unfold sctx_of_ctx.
      rewrite ctx_names_subst_type_params_ctx.
      apply Hkeys_initial. exact Hin. }
    assert (Hroots_initial_subst :
      root_env_sctx_roots_named (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))).
    { unfold root_env_sctx_roots_named in *.
      intros y roots0 z Hlookup Hin.
      change (In z (ctx_names (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))).
      rewrite ctx_names_subst_type_params_ctx.
      eapply Hroots_initial; eassumption. }
    assert (Hctx_alpha_subst :
      ctx_alpha rho
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fcall))))).
    { apply ctx_alpha_subst_type_params_ctx. exact Halpha_params. }
    assert (Hctx_used_subst :
      forall y,
        In y (ctx_names (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fcall))))) ->
        In y used_params).
    { intros y Hy. unfold sctx_of_ctx in Hy.
      rewrite ctx_names_subst_type_params_ctx in Hy.
      apply Hctx_used. exact Hy. }
    assert (Hdisj_subst :
      disjoint_names (free_vars_expr
        (subst_type_params_expr type_args (fn_body fdef)))
        (rename_range rho)).
    { rewrite expr_names_subst_type_params_expr. exact Hdisj. }
    assert (Hbody_rename_subst :
      alpha_rename_expr rho used_params
        (subst_type_params_expr type_args (fn_body fdef)) =
      (subst_type_params_expr type_args (fn_body fcall), used')).
    { apply alpha_rename_expr_subst_type_params_expr. exact Hbody_rename. }
    assert (Hkeys_body :
      root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                  (global_env_with_local_bounds env
                    (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
                  (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
      eapply Hkeys_expr; eassumption. }
    assert (Hrn_body : root_env_no_shadow R_body).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
      - exact Hrn_initial. }
    assert (Hsame_body :
      sctx_same_bindings
        (sctx_of_ctx (subst_type_params_ctx type_args
          (params_ctx (fn_params fdef))))
        (sctx_of_ctx Gamma_out)).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
    assert (Hnodup_apply :
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef))))).
    { rewrite params_ctx_apply_type_params.
      rewrite ctx_names_subst_type_params_ctx. exact Hnodup. }
    assert (Hctx_alpha_apply :
      ctx_alpha rho
        (sctx_of_ctx (params_ctx
          (apply_type_params type_args (fn_params fdef))))
        (sctx_of_ctx (params_ctx
          (apply_type_params type_args (fn_params fcall))))).
    { rewrite params_ctx_apply_type_params.
      rewrite params_ctx_apply_type_params. exact Hctx_alpha_subst. }
    assert (Hsame_body_apply :
      sctx_same_bindings
        (sctx_of_ctx (params_ctx
          (apply_type_params type_args (fn_params fdef))))
        (sctx_of_ctx Gamma_out)).
    { rewrite params_ctx_apply_type_params. exact Hsame_body. }
    assert (Hnocoll_body :
      rename_no_collision_on rho (root_env_names R_body)).
    { eapply rename_no_collision_on_root_env_names_from_typed_support.
      - exact Hctx_alpha_apply.
      - exact Hsame_body_apply.
      - exact Hnodup_apply.
      - exact Hkeys_body. }
    destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (subst_type_params_expr type_args (fn_body fdef))
      T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots
      Hsummary_params rho
      (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall))))
      (subst_type_params_expr type_args (fn_body fcall))
      used_params used' Hctx_alpha_subst Hrn_initial Hrn_initial_r
      Hinitial_equiv Hkeys_initial_subst Hroots_initial_subst Hnocoll_initial
      Hnocoll_body Hctx_used_subst Hrange_used Hdisj_subst Hbody_rename_subst)
      as (Gamma_out_r & R_body_r & roots_body_r & ret_roots_r &
          Hsummary_renamed & _).
    apply Hnot_params.
    assert (Hfree_ctx :
      In x (ctx_names (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall)))))).
    { eapply expr_root_shadow_store_safe_narrow_summary_ready_free_vars_ctx_names.
      - exact Hsummary_renamed.
      - exact Hready.
      - exact Hin_free. }
    unfold sctx_of_ctx in Hfree_ctx.
    rewrite <- params_ctx_apply_type_params in Hfree_ctx.
    exact Hfree_ctx.
  - destruct Hgeneric as (fuel' & fname & nested_type_args & args & raw_body &
      synthetic_body & fcallee & T_body & Gamma_out & R_body & roots_body &
      Hfuel & Hbody & Htarget & Hsynthetic & Hsafe & Hin & Hname & Harity &
      Hbounds & Hnested & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
    destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime
      env type_args (store_names s_hidden) fdef fcall used' fname
      nested_type_args args raw_body synthetic_body Hbody Htarget Hsynthetic
      Hsafe Hrename)
      as (argsr & Hbody_runtime & Hsafe_runtime).
    rewrite Hbody_runtime in Hready.
    dependent destruction Hready.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_generic_direct_alpha_renamed_body_free_vars_hidden_seed_excludes :
  forall env fuel fdef type_args fname nested_type_args args raw_body
      synthetic_body fcallee T_body Gamma_out R_body roots_body fcall used'
      x T hidden s_hidden s_base,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fcallee nested_type_args ->
    NoDup (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fdef)))) ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
    roots_exclude_params (apply_type_params type_args (fn_params fdef))
      roots_body ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def (store_names s_hidden) fdef = (fcall, used') ->
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros env fuel fdef type_args fname nested_type_args args raw_body
    synthetic_body fcallee T_body Gamma_out R_body roots_body fcall used' x T
    hidden s_hidden s_base Hbody Htarget Hsynthetic Hsafe _ Hnodup Htyped
    Hexcl_roots Hcaps Hrename Hrel.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args
    env type_args (store_names s_hidden) fdef fcall used' fname
    nested_type_args args raw_body synthetic_body T_body Gamma_out R_body
    roots_body Hbody Htarget Hsynthetic Hsafe Hcaps Hrename Hnodup Htyped
    Hexcl_roots)
    as (argsr & fcallee_runtime & sigma & arg_roots & Sigma_out &
        R_out & roots_out & Hbody_runtime & Hsafe_runtime & Htyped_runtime &
        Htyped_args & _ & _ & _).
  rewrite Hbody_runtime. simpl.
  intros Hin.
  pose proof (store_hidden_frame_rel_name_in x T hidden s_hidden s_base Hrel)
    as Hused.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    (store_names s_hidden) fdef fcall used' type_args x Hrename Hused)
    as [Hnot_params _].
  assert (Hfree_ctx :
    In x (ctx_names (sctx_of_ctx
      (subst_type_params_ctx type_args (fn_body_ctx fcall))))).
  { eapply store_safe_function_value_call_args_typed_roots_free_vars_ctx_names.
    - eapply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_runtime.
    - exact Htyped_args.
    - exact Hin. }
  apply Hnot_params.
  rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall) in Hfree_ctx.
  - unfold sctx_of_ctx in Hfree_ctx.
    rewrite <- params_ctx_apply_type_params in Hfree_ctx.
    exact Hfree_ctx.
  - rewrite <- Hcaps.
    eapply alpha_rename_fn_def_captures. exact Hrename.
Qed.





Lemma hidden_frame_eval_strip_alpha_renamed_fn_body :
  forall env used fdef fcall used' type_args x T hidden s_with s_base
      s_body_with ret,
    alpha_rename_fn_def used fdef = (fcall, used') ->
    In x used ->
    eval env s_with
      (subst_type_params_expr type_args (fn_body fcall)) s_body_with ret ->
    store_hidden_frame_rel x T hidden s_with s_base ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcall)) ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))) ->
    store_refs_exclude_root x s_base ->
    exists s_body_base,
      store_hidden_frame_rel x T hidden s_body_with s_body_base /\
      eval env s_base
        (subst_type_params_expr type_args (fn_body fcall)) s_body_base ret /\
      store_refs_exclude_root x s_body_base /\
      value_refs_exclude_root x ret.
Proof.
  intros env used fdef fcall used' type_args x T hidden s_with s_base
    s_body_with ret Hrename Hused Heval Hrel Hready Hnot_free Hrefs.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    used fdef fcall used' type_args x Hrename Hused)
    as [_ Hnot_local].
  eapply (proj1 hidden_frame_eval_strip_rel_mutual); eassumption.
Qed.

Lemma eval_generic_direct_call_hidden_frame_args_strip :
  forall env x T hidden s_hidden s_base s_hidden' fname type_args args ret,
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s_base ->
    eval env s_hidden (ECallGeneric fname type_args args) s_hidden' ret ->
    exists fdef fcall used' s_args_hidden s_args vs s_body_hidden,
      lookup_fn fname (env_fns env) = Some fdef /\
      fn_captures fdef = [] /\
      store_hidden_frame_rel x T hidden s_args_hidden s_args /\
      eval_args env s_hidden args s_args_hidden vs /\
      eval_args env s_base args s_args vs /\
      store_refs_exclude_root x s_args /\
      Forall (value_refs_exclude_root x) vs /\
      alpha_rename_fn_def (store_names s_args_hidden) fdef =
        (fcall, used') /\
      eval env
        (bind_params (apply_type_params type_args (fn_params fcall))
          vs s_args_hidden)
        (subst_type_params_expr type_args (fn_body fcall))
        s_body_hidden ret /\
      s_hidden' =
        store_remove_params
          (apply_type_params type_args (fn_params fcall)) s_body_hidden.
Proof.
  intros env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    Hrel Hready Hnot_free Hnot_local Hrefs Heval.
  inversion Heval; subst; clear Heval.
  match goal with
  | Heval_args : eval_args env s_hidden args s_args vs |- _ =>
      destruct (proj1 (proj2 hidden_frame_eval_strip_rel_mutual)
        env s_hidden args s_args vs Heval_args x T hidden s_base Hrel Hready
        Hnot_free Hnot_local Hrefs)
        as (s_args_base & Hrel_args & Heval_args_base & Hrefs_args & Hvs_refs)
  end.
  exists fdef, fcall, used', s_args, s_args_base, vs, s_body.
  repeat split; try eassumption; reflexivity.
Qed.

Lemma eval_generic_direct_call_hidden_frame_expr_body_strip :
  forall env x T hidden s_hidden s_base s_hidden' fname type_args args ret
      fdef fcall used' s_args_hidden s_args vs s_body_hidden,
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s_base ->
    eval env s_hidden (ECallGeneric fname type_args args) s_hidden' ret ->
    lookup_fn fname (env_fns env) = Some fdef ->
    fn_captures fdef = [] ->
    store_hidden_frame_rel x T hidden s_args_hidden s_args ->
    eval_args env s_base args s_args vs ->
    store_refs_exclude_root x s_args ->
    Forall (value_refs_exclude_root x) vs ->
    alpha_rename_fn_def (store_names s_args_hidden) fdef =
      (fcall, used') ->
    eval env
      (bind_params (apply_type_params type_args (fn_params fcall))
        vs s_args_hidden)
      (subst_type_params_expr type_args (fn_body fcall))
      s_body_hidden ret ->
    s_hidden' =
      store_remove_params
        (apply_type_params type_args (fn_params fcall)) s_body_hidden ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcall)) ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))) ->
    exists s_body_base s_final_base,
      store_hidden_frame_rel x T hidden s_body_hidden s_body_base /\
      eval env
        (bind_params (apply_type_params type_args (fn_params fcall))
          vs s_args)
        (subst_type_params_expr type_args (fn_body fcall))
        s_body_base ret /\
      store_refs_exclude_root x s_body_base /\
      value_refs_exclude_root x ret /\
      s_final_base =
        store_remove_params
          (apply_type_params type_args (fn_params fcall)) s_body_base /\
      store_hidden_frame_rel x T hidden s_hidden' s_final_base /\
      store_remove x s_hidden' = s_final_base.
Proof.
  intros env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    fdef fcall used' s_args_hidden s_args vs s_body_hidden Hrel Hready
    Hnot_free Hnot_local Hrefs Heval Hlookup Hcaps Hrel_args Heval_args
    Hrefs_args Hvs_refs Hrename Heval_body Hfinal Hready_body Hbody_not_free.
  pose proof (store_hidden_frame_rel_name_in x T hidden s_args_hidden s_args
    Hrel_args) as Hused.
  destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
    (store_names s_args_hidden) fdef fcall used' type_args x Hrename Hused)
    as [Hnotin_params Hnotin_body_locals].
  pose (ps := apply_type_params type_args (fn_params fcall)).
  assert (Hrel_bind :
    store_hidden_frame_rel x T hidden
      (bind_params ps vs s_args_hidden) (bind_params ps vs s_args)).
  { subst ps. eapply store_hidden_frame_rel_bind_params; eassumption. }
  assert (Hrefs_bind :
    store_refs_exclude_root x (bind_params ps vs s_args)).
  { subst ps. eapply bind_params_refs_exclude_root; eassumption. }
  destruct (hidden_frame_eval_strip_alpha_renamed_fn_body
    env (store_names s_args_hidden) fdef fcall used' type_args x T hidden
    (bind_params ps vs s_args_hidden) (bind_params ps vs s_args)
    s_body_hidden ret Hrename Hused Heval_body Hrel_bind Hready_body
    Hbody_not_free Hrefs_bind)
    as [s_body_base [Hrel_body [Heval_body_base [Hrefs_body Hv_refs]]]].
  exists s_body_base,
    (store_remove_params (apply_type_params type_args (fn_params fcall))
      s_body_base).
  repeat split; try eassumption; try reflexivity.
  - subst ps.
    rewrite Hfinal.
    eapply store_hidden_frame_rel_remove_params; eassumption.
  - eapply store_hidden_frame_rel_remove_base.
    subst ps.
    rewrite Hfinal.
    eapply store_hidden_frame_rel_remove_params; eassumption.
Qed.


Lemma eval_generic_direct_call_hidden_frame_package_from_stripped_body :
  forall env x T hidden s_hidden s_base s_hidden' fname type_args args ret
      Sigma_args R_args arg_roots ret_ty,
    store_hidden_frame_rel x T hidden s_hidden s_base ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s_base ->
    eval env s_hidden (ECallGeneric fname type_args args) s_hidden' ret ->
    (forall (fdef fcall : fn_def) (used' : list ident)
        (s_args_hidden s_args : store) (vs : list value)
        (s_body_hidden : store),
      lookup_fn fname (env_fns env) = Some fdef ->
      fn_captures fdef = [] ->
      store_hidden_frame_rel x T hidden s_args_hidden s_args ->
      eval_args env s_hidden args s_args_hidden vs ->
      eval_args env s_base args s_args vs ->
      store_refs_exclude_root x s_args ->
      Forall (value_refs_exclude_root x) vs ->
      alpha_rename_fn_def (store_names s_args_hidden) fdef =
        (fcall, used') ->
      eval env
        (bind_params (apply_type_params type_args (fn_params fcall))
          vs s_args_hidden)
        (subst_type_params_expr type_args (fn_body fcall))
        s_body_hidden ret ->
      s_hidden' =
        store_remove_params
          (apply_type_params type_args (fn_params fcall)) s_body_hidden ->
      generic_direct_call_runtime_package env s_base (store_remove x s_hidden')
        ret Sigma_args R_args arg_roots ret_ty) ->
    generic_direct_call_runtime_package env s_base (store_remove x s_hidden')
      ret Sigma_args R_args arg_roots ret_ty.
Proof.
  intros env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    Sigma_args R_args arg_roots ret_ty Hrel Hready Hnot_free Hnot_local Hrefs
    Heval Hpackage_body.
  destruct (eval_generic_direct_call_hidden_frame_args_strip
    env x T hidden s_hidden s_base s_hidden' fname type_args args ret
    Hrel Hready Hnot_free Hnot_local Hrefs Heval)
    as (fdef & fcall & used' & s_args_hidden & s_args & vs &
        s_body_hidden & Hlookup & Hcaps & Hrel_args & Heval_args_hidden &
        Heval_args_base & Hrefs_args & Hvs_refs & Hrename &
        Heval_body_hidden & Hfinal_hidden).
  eapply Hpackage_body; eassumption.
Qed.
