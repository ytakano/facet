From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeFinalStoreScopeFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_store_safe_narrow_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Inductive callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (env : global_env) : nat -> fn_def -> list Ty -> Prop :=
  | CBRSSNI_Expr : forall fuel fdef type_args T_body Gamma_out R_body
      roots_body ret_roots,
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) ->
      expr_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots ->
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true ->
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body ->
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env fuel fdef type_args
  | CBRSSNI_GenericDirect : forall fuel fdef type_args fname
      nested_type_args args raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
      raw_body = subst_type_params_expr type_args (fn_body fdef) ->
      generic_direct_call_target_expr raw_body =
        Some (fname, nested_type_args, args, synthetic_body) ->
      synthetic_body = ECallGeneric fname nested_type_args args ->
      store_safe_function_value_call_args env args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      Datatypes.length nested_type_args = fn_type_params fcallee ->
      check_struct_bounds
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_bounds fcallee) nested_type_args = None ->
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
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true ->
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body ->
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env (S fuel) fdef type_args.

Lemma check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound :
  forall fuel env fdef type_args,
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      fuel env fdef type_args = true ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args.
Proof.
  induction fuel as [| fuel' IH]; intros env fdef type_args Hcheck.
  - simpl in Hcheck. discriminate.
  - cbn [check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel]
      in Hcheck.
    remember (subst_type_params_ctx type_args (fn_body_ctx fdef)) as body_ctx.
    remember (subst_type_params_expr type_args (fn_body fdef)) as body.
    remember (apply_type_params type_args (fn_params fdef)) as params.
    remember (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef))) as body_env.
    destruct (infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef))
      as [[[[T_env Gamma_env] R_env] roots_env] | err_env] eqn:Henv;
      try discriminate.
    apply orb_true_iff in Hcheck as [Hexact | Hgeneric].
    + destruct (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel_exact_sound
        (S fuel') env fdef type_args Hexact) as
        (T_body & Gamma_out & R_body & roots_body & ret_roots & Hnodup &
          Hsummary & Hcompat & Hroots & Hroot_env).
      eapply CBRSSNI_Expr; eassumption.
    + destruct (generic_direct_call_target_expr body)
        as [[[[fname nested_type_args] args] synthetic_body] |] eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hgeneric as [Hsafe_args Hgeneric].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      apply andb_true_iff in Hgeneric as [Harity Hgeneric].
      apply Nat.eqb_eq in Harity.
      destruct (check_struct_bounds body_env
        (fn_bounds fcallee) nested_type_args) as [bounds_err |] eqn:Hbounds;
        try discriminate.
      destruct (infer_core_env_roots_shadow_safe body_env
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef) body_ctx synthetic_body)
        as [[[[T_body Gamma_out] R_body] roots_body] | err_body]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hgeneric.
      destruct Hgeneric as [[[Hrecursive Hcompat] Hroots] Hroot_env].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      specialize (IH env fcallee nested_type_args Hrecursive).
      pose proof (infer_core_env_roots_shadow_safe_sound body_env
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef) body_ctx synthetic_body
        T_body Gamma_out R_body roots_body Hbody_env) as Htyped_body.
      subst body_ctx params body_env.
      eapply CBRSSNI_GenericDirect with
        (raw_body := body) (synthetic_body := synthetic_body)
        (fcallee := fcallee) (T_body := T_body)
        (Gamma_out := Gamma_out) (R_body := R_body)
        (roots_body := roots_body).
      * subst body. reflexivity.
      * exact Htarget.
      * subst body. unfold generic_direct_call_target_expr in Htarget.
        destruct (subst_type_params_expr type_args (fn_body fdef));
          try discriminate.
        inversion Htarget. reflexivity.
      * apply store_safe_function_value_call_args_b_sound. exact Hsafe_args.
      * exact Hin_callee.
      * exact Hname_callee.
      * exact Harity.
      * exact Hbounds.
      * exact IH.
      * rewrite params_ctx_apply_type_params.
        rewrite ctx_names_subst_type_params_ctx.
        eapply infer_env_roots_shadow_safe_params_nodup. exact Henv.
      * exact Htyped_body.
      * exact Hcompat.
      * apply fn_params_roots_exclude_b_sound. exact Hroots.
      * apply fn_params_root_env_excludes_b_sound. exact Hroot_env.
Qed.

Lemma check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound :
  forall env fdef type_args,
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args = true ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fdef type_args.
Proof.
  intros env fdef type_args Hcheck.
  unfold check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
    in Hcheck.
  eapply check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound.
  exact Hcheck.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds :
  forall env bounds fuel fdef type_args,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      (global_env_with_local_bounds env bounds) fuel fdef type_args.
Proof.
  intros env bounds fuel fdef type_args Hunique Hsummary.
  revert bounds.
  induction Hsummary; intros bounds.
  - eapply CBRSSNI_Expr.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
  - eapply CBRSSNI_GenericDirect with
      (raw_body := raw_body) (synthetic_body := synthetic_body)
      (fcallee := fcallee) (T_body := T_body)
      (Gamma_out := Gamma_out) (R_body := R_body)
      (roots_body := roots_body).
    + exact H.
    + exact H0.
    + exact H1.
    + apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact H2.
    + change (env_fns (global_env_with_local_bounds env bounds))
        with (env_fns env).
      exact H3.
    + exact H4.
    + exact H5.
    + change (check_struct_bounds
        (global_env_with_local_bounds
          (global_env_with_local_bounds env bounds)
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_bounds fcallee) nested_type_args)
        with (check_struct_bounds
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
          (fn_bounds fcallee) nested_type_args).
      exact H6.
    + apply IHHsummary.
    + exact H7.
    + change (typed_env_roots_shadow_safe
        (global_env_with_local_bounds
          (global_env_with_local_bounds env bounds)
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body)
        with (typed_env_roots_shadow_safe
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
          (fn_outlives fdef) (fn_lifetimes fdef)
          (initial_root_env_for_fn fdef)
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
          synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body).
      exact H8.
    + exact H9.
    + exact H10.
    + exact H11.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases :
  forall env fuel fdef type_args,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    (exists T_body Gamma_out R_body roots_body ret_roots,
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) /\
      expr_root_shadow_store_safe_narrow_summary
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        (subst_type_params_expr type_args (fn_body fdef))
        T_body (sctx_of_ctx Gamma_out) R_body roots_body ret_roots /\
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true /\
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body /\
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body) \/
    (exists fuel' fname nested_type_args args raw_body synthetic_body fcallee
        T_body Gamma_out R_body roots_body,
      fuel = S fuel' /\
      raw_body = subst_type_params_expr type_args (fn_body fdef) /\
      generic_direct_call_target_expr raw_body =
        Some (fname, nested_type_args, args, synthetic_body) /\
      synthetic_body = ECallGeneric fname nested_type_args args /\
      store_safe_function_value_call_args env args /\
      In fcallee (env_fns env) /\
      fn_name fcallee = fname /\
      Datatypes.length nested_type_args = fn_type_params fcallee /\
      check_struct_bounds
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_bounds fcallee) nested_type_args = None /\
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        env fuel' fcallee nested_type_args /\
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fdef)))) /\
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fdef) T_body
        (subst_type_params_ty type_args (fn_ret fdef)) = true /\
      roots_exclude_params (apply_type_params type_args (fn_params fdef))
        roots_body /\
      root_env_excludes_params (apply_type_params type_args (fn_params fdef))
        R_body).
Proof.
  intros env fuel fdef type_args Hsummary.
  inversion Hsummary; subst.
  - left. repeat eexists; repeat split; eauto.
  - right. repeat eexists; repeat split; eauto.
Qed.


Lemma generic_direct_call_target_expr_preservation_ready_false :
  forall e fname type_args args synthetic_body,
    generic_direct_call_target_expr e =
      Some (fname, type_args, args, synthetic_body) ->
    preservation_ready_expr e ->
    False.
Proof.
  intros e fname type_args args synthetic_body Htarget Hready.
  unfold generic_direct_call_target_expr in Htarget.
  destruct e; try discriminate.
  dependent destruction Hready.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_ready :
  forall env fuel fdef type_args,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env fuel fdef type_args ->
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fdef)) ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args.
Proof.
  intros env fuel fdef type_args Hsummary Hready.
  destruct (callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_cases
    env fuel fdef type_args Hsummary) as [Hexpr | Hgeneric].
  - exact Hexpr.
  - destruct Hgeneric as (fuel' & fname & nested_type_args & args & raw_body &
      synthetic_body & fcallee & T_body & Gamma_out & R_body & roots_body &
      Hfuel & Hbody & Htarget & Hsynthetic & Hsafe & Hin & Hname & Harity &
      Hbounds & Hnested & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
    subst raw_body.
    exfalso.
    eapply generic_direct_call_target_expr_preservation_ready_false;
      eassumption.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_zero :
  forall env fdef type_args,
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 0 fdef type_args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args.
Proof.
  intros env fdef type_args Hsummary.
  inversion Hsummary; subst; try discriminate.
  unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated.
  repeat eexists; repeat split; eauto.
Qed.

Lemma generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args type_args fdef fcall param_tys ret_ty s s_args vs used' seed,
      callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fdef type_args ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (apply_type_params type_args (fn_params fdef)))
        (subst_type_params_ty type_args (fn_ret fdef)) param_tys ret_ty ->
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
        expr_root_shadow_store_safe_narrow_summary
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall)))
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R_args)
          (sctx_of_ctx (params_ctx
            (apply_type_params type_args (fn_params fcall))))
          (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
          R_body roots_body ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body
          (subst_type_params_ty type_args (fn_ret fcall)) = true /\
        roots_exclude_params (apply_type_params type_args (fn_params fcall))
          roots_body /\
        root_env_excludes_params
          (apply_type_params type_args (fn_params fcall)) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args type_args
    fdef fcall param_tys ret_ty s s_args vs used' seed Hsummary Hcaps Hbridge
    Hsafe_args Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hseed_names Hrename.
  set (body_env := global_env_with_local_bounds env
    (subst_type_params_trait_bounds type_args (fn_bounds fdef))).
  set (fdefT := fn_subst_type_params type_args fdef).
  set (fcallT := fn_subst_type_params type_args fcall).
  destruct (alpha_rename_fn_def_static_fields seed fdef fcall used' Hrename)
    as [_ [_ [_ [_ [_ [_ Hbounds]]]]]].
  assert (HsummaryT :
    callee_body_root_shadow_store_safe_narrow_summary body_env fdefT).
  { subst body_env fdefT.
    unfold callee_body_root_shadow_store_safe_narrow_summary.
    unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated in Hsummary.
    destruct Hsummary as (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup & Hbody & Hcompat & Hexcl_roots & Hexcl_env).
    exists T_body, Gamma_out, R_body, roots_body, ret_roots.
    simpl. repeat split; try assumption.
    - rewrite initial_root_env_for_fn_fn_subst_type_params.
      rewrite fn_body_ctx_fn_subst_type_params.
      exact Hbody. }
  assert (HcapsT : fn_captures fdefT = []).
  { subst fdefT. simpl. rewrite Hcaps. reflexivity. }
  assert (HrenameT :
    alpha_rename_fn_def seed fdefT = (fcallT, used')).
  { subst fdefT fcallT.
    apply alpha_rename_fn_def_subst_type_params. exact Hrename. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Htyped_args_body :
    typed_args_roots body_env Omega n R Sigma args
      (params_of_tys param_tys) Sigma_args R_args arg_roots).
  { subst body_env.
    eapply typed_args_roots_store_safe_global_env_with_local_bounds;
      eassumption. }
  assert (Heval_args_body : eval_args body_env s args s_args vs).
  { subst body_env. apply eval_args_global_env_with_local_bounds. exact Heval_args. }
  assert (Hstore_body : store_typed_prefix body_env s Sigma).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore. }
  destruct (direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed
    body_env Omega n R Sigma Sigma_args R_args arg_roots args fdefT fcallT
    param_tys ret_ty s s_args vs used' seed HsummaryT HcapsT Hbridge
    Hsafe_args_body Htyped_args_body Heval_args_body Hprov_args Hstore_body
    Hroots Hshadow Hrn Hnamed Hkeys Hseed_names HrenameT)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
      Hbody & Hcompat & Hexcl_roots & Hexcl_env & Hsubset).
  subst fcallT body_env. simpl in *.
  exists T_body, Sigma_out, R_body, roots_body, ret_roots.
  rewrite Hbounds.
  repeat split; try assumption.
Qed.


Lemma generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args type_args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fdef type_args ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (apply_type_params type_args (fn_params fdef)))
        (subst_type_params_ty type_args (fn_ret fdef)) param_tys ret_ty ->
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
        expr_root_shadow_store_safe_narrow_summary
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall)))
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R_args)
          (sctx_of_ctx (params_ctx
            (apply_type_params type_args (fn_params fcall))))
          (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
          R_body roots_body ret_roots /\
        ty_compatible_b (fn_outlives fcall) T_body
          (subst_type_params_ty type_args (fn_ret fcall)) = true /\
        roots_exclude_params (apply_type_params type_args (fn_params fcall))
          roots_body /\
        root_env_excludes_params
          (apply_type_params type_args (fn_params fcall)) R_body /\
        root_set_stores_subset roots_body (root_sets_union arg_roots).
Proof.
  intros.
  eapply generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed;
    try eassumption.
  intros y Hy. exact Hy.
Qed.
