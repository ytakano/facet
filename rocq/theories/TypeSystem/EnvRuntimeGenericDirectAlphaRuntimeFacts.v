From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectRuntimePackage.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma alpha_rename_store_safe_call_args_hidden_seed_excludes :
  forall env rho used args argsr used' x,
    store_safe_function_value_call_args env args ->
    (forall y, In y (rename_range rho) -> y <> x) ->
    ~ In x (args_free_vars_ts args) ->
    ((fix go (used0 : list ident) (args0 : list expr)
        : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr rho used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end) used args) = (argsr, used') ->
    ~ In x (args_free_vars_ts argsr) /\
    ~ In x (args_local_store_names argsr).
Proof.
  intros env rho used args argsr used' x Hsafe Hrange Hfree Hrename.
  revert used argsr used' Hfree Hrename.
  induction Hsafe as [| arg rest Harg Hsafe_rest IH];
    intros used argsr used' Hfree Hrename; simpl in Hrename.
  - injection Hrename as <- _. simpl. split; intros Hin; contradiction.
  - destruct Harg as [| lit | y | fname0 fdef0 Hin0 Hname0 Hsummary0 | name lts tys sdef Hlookup Hbounds]; simpl in Hrename.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. right. exact Hin.
      * exact Hrest.
      * split.
        -- simpl. intros Hin. destruct Hin as [Heq | Hin].
           ++ destruct (lookup_rename_in_range_or_self rho y)
                as [Hin_range | Hself].
              ** apply (Hrange (lookup_rename y rho) Hin_range).
                 exact Heq.
              ** apply Hfree. simpl. left.
                 rewrite Hself in Heq. exact Heq.
           ++ apply Hfree_rest. exact Hin.
        -- simpl. exact Hlocal_rest.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
    + destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used rest) as [restr used_rest] eqn:Hrest.
      injection Hrename as <- <-.
      destruct (IH used restr used_rest) as [Hfree_rest Hlocal_rest].
      * intros Hin. apply Hfree. simpl. exact Hin.
      * exact Hrest.
      * simpl. split; assumption.
Qed.

Lemma generic_direct_call_target_alpha_rename_runtime_args_hidden_seed_excludes :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body argsr x,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    In x used ->
    ~ In x (args_free_vars_ts args) ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    subst_type_params_expr type_args (fn_body fcall) =
      ECallGeneric fname nested_type_args argsr ->
    ~ In x (args_free_vars_ts argsr) /\
    ~ In x (args_local_store_names argsr).
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body argsr x Hbody Htarget Hsynthetic Hsafe Hused
    Hfree Hrename Hbody_runtime.
  subst raw_body synthetic_body.
  destruct fdef as [fname_def lifetimes outs captures ps ret body].
  simpl in *.
  unfold generic_direct_call_target_expr in Htarget.
  destruct (subst_type_params_expr type_args body) eqn:Hsubst;
    try discriminate.
  inversion Htarget; subst i l l0; clear Htarget.
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr rho] used_params] eqn:Hparams.
  destruct (alpha_rename_expr rho used_params body) as [bodyr used_body]
    eqn:Hbody_rename.
  inversion Hrename; subst fcall used_body; clear Hrename.
  pose proof (alpha_rename_expr_subst_type_params_expr type_args rho
    used_params body bodyr used' Hbody_rename) as Hbody_subst_rename.
  rewrite Hsubst in Hbody_subst_rename.
  simpl in Hbody_subst_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used_params args) as [argsr0 used_args] eqn:Hargsr.
  injection Hbody_subst_rename as Hexpr_eq.
  simpl in Hbody_runtime.
  rewrite <- Hexpr_eq in Hbody_runtime.
  injection Hbody_runtime as Hargs_eq.
  assert (Hrange_fresh : forall y,
    In y (rename_range rho) -> y <> x).
  { intros y Hrange Hy.
    subst y.
    eapply alpha_rename_params_range_fresh_used_nil.
    - exact Hparams.
    - exact Hrange.
    - apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. right. exact Hused. }
  destruct (alpha_rename_store_safe_call_args_hidden_seed_excludes
    env rho used_params args argsr0 used_args x Hsafe Hrange_fresh Hfree Hargsr)
    as [Hfree_runtime Hlocal_runtime].
  split.
  - rewrite <- Hargs_eq. exact Hfree_runtime.
  - rewrite <- Hargs_eq. exact Hlocal_runtime.
Qed.


Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    exists argsr,
      subst_type_params_expr type_args (fn_body fcall) =
        ECallGeneric fname nested_type_args argsr /\
      store_safe_function_value_call_args env argsr.
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body Hbody Htarget Hsynthetic Hsafe Hrename.
  subst raw_body synthetic_body.
  unfold generic_direct_call_target_expr in Htarget.
  destruct (subst_type_params_expr type_args (fn_body fdef)) eqn:Hsubst;
    try discriminate.
  inversion Htarget; subst i l l0; clear Htarget.
  destruct (alpha_rename_fn_def_params_body used fdef fcall used' Hrename)
    as (rho & used_params & Hparams & Hbody_rename).
  pose proof (alpha_rename_expr_subst_type_params_expr type_args rho
    used_params (fn_body fdef) (fn_body fcall) used' Hbody_rename)
    as Hbody_subst_rename.
  rewrite Hsubst in Hbody_subst_rename.
  simpl in Hbody_subst_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used_params args) as [argsr used_args] eqn:Hargsr.
  inversion Hbody_subst_rename; subst.
  exists argsr.
  split; [reflexivity |].
  eapply store_safe_function_value_call_args_alpha_rename_call_go;
    eassumption.
Qed.





Lemma generic_direct_call_target_alpha_rename_runtime_body_free_vars_hidden_seed_excludes :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body x,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    In x used ->
    ~ In x (args_free_vars_ts args) ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    ~ In x (free_vars_expr
      (subst_type_params_expr type_args (fn_body fcall))).
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body x Hbody Htarget Hsynthetic Hsafe Hused Hfree
    Hrename.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime
    env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body Hbody Htarget Hsynthetic Hsafe Hrename)
    as [argsr [Hbody_runtime Hsafe_runtime]].
  rewrite Hbody_runtime. simpl.
  destruct (generic_direct_call_target_alpha_rename_runtime_args_hidden_seed_excludes
    env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body argsr x Hbody Htarget Hsynthetic Hsafe Hused
    Hfree Hrename Hbody_runtime) as [Hfree_runtime _].
  exact Hfree_runtime.
Qed.


Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body T_body Gamma_out R_body roots_body,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
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
    exists argsr fcallee (sigma : list lifetime),
      exists arg_roots Sigma_out_r R_body_r roots_body_r,
      subst_type_params_expr type_args (fn_body fcall) =
        ECallGeneric fname nested_type_args argsr /\
      store_safe_function_value_call_args env argsr /\
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        (ECallGeneric fname nested_type_args argsr)
        T_body Sigma_out_r R_body_r roots_body_r /\
      typed_args_roots
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        argsr
        (apply_lt_params sigma
          (apply_type_params nested_type_args (fn_params fcallee)))
        Sigma_out_r R_body_r arg_roots /\
      In fcallee (env_fns
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))) /\
      fn_name fcallee = fname /\
      roots_exclude_params (apply_type_params type_args (fn_params fcall))
        roots_body_r.
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body T_body Gamma_out R_body roots_body Hbody Htarget
    Hsynthetic Hsafe Hcaps Hrename Hnodup_applied Htyped Hexcl_roots.
  subst raw_body synthetic_body.
  rewrite params_ctx_apply_type_params in Hnodup_applied.
  rewrite ctx_names_subst_type_params_ctx in Hnodup_applied.
  destruct (alpha_rename_fn_def_initial_support_facts
              used fdef fcall used' Hrename Hnodup_applied)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields used fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [_ [_ Hbounds]]]]]].
  unfold generic_direct_call_target_expr in Htarget.
  destruct (subst_type_params_expr type_args (fn_body fdef)) eqn:Hsubst;
    try discriminate.
  inversion Htarget; subst i l l0; clear Htarget.
  pose proof (alpha_rename_expr_subst_type_params_expr type_args rho
    used_params (fn_body fdef) (fn_body fcall) used' Hbody_rename)
    as Hbody_subst_rename.
  rewrite Hsubst in Hbody_subst_rename.
  simpl in Hbody_subst_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used_params args) as [argsr used_args] eqn:Hargsr.
  inversion Hbody_subst_rename; subst used_args; clear Hbody_subst_rename.
  assert (Htyped_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (ECallGeneric fname nested_type_args args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures fdef Hcaps).
    exact Htyped. }
  assert (Hctx_alpha_subst :
    ctx_alpha rho
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall))))).
  { apply ctx_alpha_subst_type_params_ctx. exact Halpha_params. }
  assert (Hkeys_initial_subst :
    root_env_sctx_keys_named (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))).
  { unfold root_env_sctx_keys_named, root_env_keys_named in *.
    intros x Hin. unfold sctx_of_ctx.
    rewrite ctx_names_subst_type_params_ctx.
    apply Hkeys_initial. exact Hin. }
  assert (Hroots_initial_subst :
    root_env_sctx_roots_named (initial_root_env_for_fn fdef)
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))).
  { unfold root_env_sctx_roots_named in *.
    intros x roots z Hlookup Hin.
    change (In z (ctx_names (subst_type_params_ctx type_args
      (params_ctx (fn_params fdef))))).
    rewrite ctx_names_subst_type_params_ctx.
    eapply Hroots_initial; eassumption. }
  assert (Hkeys_body :
    root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_params.
    - exact Hrn_initial. }
  assert (Hnodup_apply :
    NoDup (ctx_names (params_ctx
      (apply_type_params type_args (fn_params fdef))))).
  { rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx. exact Hnodup_applied. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fdef))))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_params. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support
      with (ps := apply_type_params type_args (fn_params fdef))
           (psr := apply_type_params type_args (fn_params fcall))
           (Σ := sctx_of_ctx Gamma_out).
    - rewrite params_ctx_apply_type_params.
      rewrite params_ctx_apply_type_params. exact Hctx_alpha_subst.
    - rewrite params_ctx_apply_type_params. exact Hsame_body.
    - exact Hnodup_apply.
    - exact Hkeys_body. }
  assert (Hrename_call_expr :
    alpha_rename_expr rho used_params
      (ECallGeneric fname nested_type_args args) =
    (ECallGeneric fname nested_type_args argsr, used')).
  { simpl. rewrite Hargsr. reflexivity. }
  assert (Hctx_used_subst :
    forall x,
      In x (ctx_names (sctx_of_ctx (subst_type_params_ctx type_args
        (params_ctx (fn_params fcall))))) ->
      In x used_params).
  { intros x Hin. unfold sctx_of_ctx in Hin.
    rewrite ctx_names_subst_type_params_ctx in Hin.
    apply Hctx_used. exact Hin. }
  assert (Hdisj_subst :
    disjoint_names
      (free_vars_expr (ECallGeneric fname nested_type_args args))
      (rename_range rho)).
  { rewrite <- Hsubst.
    rewrite expr_names_subst_type_params_expr.
    exact Hdisj. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env
                (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (subst_type_params_ctx type_args
                (params_ctx (fn_params fdef))))
              (sctx_of_ctx (subst_type_params_ctx type_args
                (params_ctx (fn_params fcall))))
              (ECallGeneric fname nested_type_args args)
              (ECallGeneric fname nested_type_args argsr)
              used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_params Hctx_alpha_subst Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial_subst Hroots_initial_subst
              Hnocoll_initial Hnocoll_body Hctx_used_subst Hrange_used Hdisj_subst
              Hrename_call_expr)
    as (Sigma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & _ & _ & Hroots_equiv).
  assert (Hsame_body_apply :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx
        (apply_type_params type_args (fn_params fdef))))
      (sctx_of_ctx Gamma_out)).
  { rewrite params_ctx_apply_type_params. exact Hsame_body. }
  assert (Hexcl_roots_r :
    roots_exclude_params (apply_type_params type_args (fn_params fcall))
      roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support
      with (rho := rho)
           (ps := apply_type_params type_args (fn_params fdef))
           (Σ := sctx_of_ctx Gamma_out)
           (roots := roots_body).
    - rewrite params_ctx_apply_type_params.
      rewrite params_ctx_apply_type_params.
      exact Hctx_alpha_subst.
    - exact Halpha_out.
    - exact Hsame_body_apply.
    - exact Hnodup_apply.
    - exact Hroots_equiv.
    - exact Hroots_set_body.
    - exact Hexcl_roots. }
  assert (Hbody_runtime :
    subst_type_params_expr type_args (fn_body fcall) =
      ECallGeneric fname nested_type_args argsr).
  { exact (eq_sym H0). }
  assert (Hsafe_runtime :
    store_safe_function_value_call_args env argsr).
  { eapply store_safe_function_value_call_args_alpha_rename_call_go;
      eassumption. }
  assert (Htyped_renamed_body_ctx :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
      (ECallGeneric fname nested_type_args argsr)
      T_body Sigma_out_r R_body_r roots_body_r).
  { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
    - exact Htyped_renamed.
    - rewrite <- Hcaps.
      eapply alpha_rename_fn_def_captures. exact Hrename. }
  destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
    (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
    (fn_outlives fdef) (fn_lifetimes fdef)
    (initial_root_env_for_params_origin (fn_params fdef) (fn_params fcall))
    (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
    fname nested_type_args argsr T_body Sigma_out_r R_body_r roots_body_r
    Htyped_renamed_body_ctx)
    as (fcallee & sigma & arg_roots & Hin & Hname & _ & _ & _ &
        Htyped_args & _ & _ & _).
  exists argsr, fcallee, sigma, arg_roots, Sigma_out_r, R_body_r,
    roots_body_r.
  repeat split; try assumption.
Qed.
Lemma typed_generic_direct_call_args_roots_call_frame_from_origin :
  forall env Omega n ps_orig ps_call outer_arg_roots R_args Sigma
      fname type_args argsr T Sigma_out R_body roots_body,
    params_alpha ps_orig ps_call ->
    NoDup (ctx_names (params_ctx ps_orig)) ->
    List.length outer_arg_roots = List.length ps_orig ->
    root_subst_images_exclude_names
      (expr_local_store_names (ECallGeneric fname type_args argsr))
      (root_subst_of_params ps_orig outer_arg_roots) ->
    root_env_no_shadow
      (initial_root_env_for_params_origin ps_orig ps_call) ->
    root_env_no_shadow
      (call_param_root_env ps_call outer_arg_roots []) ->
    root_env_tail_fresh_names
      (root_env_remove_params ps_call R_args)
      (expr_local_store_names (ECallGeneric fname type_args argsr)) ->
    typed_env_roots_shadow_safe env Omega n
      (initial_root_env_for_params_origin ps_orig ps_call) Sigma
      (ECallGeneric fname type_args argsr) T Sigma_out R_body roots_body ->
    Sigma = sctx_of_ctx (params_ctx ps_call) ->
    roots_exclude_params ps_call roots_body ->
    (forall x,
      In x (ctx_names (params_ctx ps_call)) ->
      root_subst_images_exclude x
        (root_subst_of_params ps_orig outer_arg_roots)) ->
    exists fcallee sigma arg_roots Sigma_args R_args_out,
      typed_args_roots env Omega n
        (call_param_root_env ps_call outer_arg_roots R_args) Sigma argsr
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fcallee)))
        Sigma_args R_args_out arg_roots /\
      In fcallee (env_fns env) /\
      fn_name fcallee = fname /\
      fn_captures fcallee = [] /\
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fcallee)) /\
      T = apply_lt_ty sigma
        (subst_type_params_ty type_args (fn_ret fcallee)) /\
      roots_exclude_params ps_call (root_sets_union arg_roots) /\
      root_set_stores_subset (root_sets_union arg_roots)
        (root_sets_union outer_arg_roots).
Proof.
  intros env Omega n ps_orig ps_call outer_arg_roots R_args Sigma fname
    type_args argsr T Sigma_out R_body roots_body Halpha Hnodup Hlen
    Hsubst_fresh Hrn_origin Hrn_call_empty Htail_fresh Htyped_origin
    Hsigma_eq Hexcl_roots Himages_exclude.
  subst Sigma.
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params ps_orig outer_arg_roots)
        (initial_root_env_for_params_origin ps_orig ps_call))
      (call_param_root_env ps_call outer_arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env Omega n
              (root_subst_of_params ps_orig outer_arg_roots)
              (initial_root_env_for_params_origin ps_orig ps_call)
              (sctx_of_ctx (params_ctx ps_call))
              (ECallGeneric fname type_args argsr) T Sigma_out R_body
              roots_body (call_param_root_env ps_call outer_arg_roots [])
              Htyped_origin Hsubst_fresh Hrn_origin Hrn_call_empty)
    as (R_body_inst & roots_body_inst & Htyped_inst & Hrn_body_inst &
        Hbody_inst_equiv & Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  pose proof (typed_env_roots_shadow_safe_tail_frame
    env Omega n (root_env_remove_params ps_call R_args)
    (call_param_root_env ps_call outer_arg_roots [])
    (sctx_of_ctx (params_ctx ps_call))
    (ECallGeneric fname type_args argsr) T Sigma_out R_body_inst
    roots_body_inst Htyped_inst Htail_fresh) as Htyped_tail.
  rewrite <- call_param_root_env_app_tail in Htyped_tail.
  destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
    env Omega n (call_param_root_env ps_call outer_arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_call)) fname type_args argsr T Sigma_out
    (R_body_inst ++ root_env_remove_params ps_call R_args)
    roots_body_inst Htyped_tail)
    as (fcallee & sigma & arg_roots & Hin & Hname & Hcaps & _ & _ &
        Htyped_args & Houtlives & Hret & Hroots_eq).
  exists fcallee, sigma, arg_roots, Sigma_out,
    (R_body_inst ++ root_env_remove_params ps_call R_args).
  assert (Hexcl_roots_inst :
    roots_exclude_params ps_call roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate; eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union outer_arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  repeat split; try assumption.
  - rewrite <- Hroots_eq. exact Hexcl_roots_inst.
  - rewrite <- Hroots_eq. exact Hsubset_inst.
Qed.

Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args_call_frame :
  forall env Omega n R Sigma Sigma_args R_args outer_arg_roots outer_args
      type_args sigma_outer fdef fcall used' fname nested_type_args args
      raw_body synthetic_body T_body Gamma_out R_body roots_body s s_args vs,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    fn_captures fdef = [] ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
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
    typed_args_roots env Omega n R Sigma outer_args
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots ->
    store_safe_function_value_call_args env outer_args ->
    eval_args env s outer_args s_args vs ->
    provenance_ready_args outer_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    exists argsr fcallee sigma_nested nested_arg_roots Sigma_nested R_nested,
      subst_type_params_expr type_args (fn_body fcall) =
        ECallGeneric fname nested_type_args argsr /\
      store_safe_function_value_call_args env argsr /\
      typed_args_roots
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (call_param_root_env (apply_type_params type_args (fn_params fcall))
          outer_arg_roots R_args)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
        argsr
        (apply_lt_params sigma_nested
          (apply_type_params nested_type_args (fn_params fcallee)))
        Sigma_nested R_nested nested_arg_roots /\
      In fcallee (env_fns
        (global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)))) /\
      fn_name fcallee = fname /\
      fn_captures fcallee = [] /\
      Forall (fun '(a, b) => outlives (fn_outlives fdef) a b)
        (apply_lt_outlives sigma_nested (fn_outlives fcallee)) /\
      T_body = apply_lt_ty sigma_nested
        (subst_type_params_ty nested_type_args (fn_ret fcallee)) /\
      roots_exclude_params (apply_type_params type_args (fn_params fcall))
        (root_sets_union nested_arg_roots) /\
      root_set_stores_subset (root_sets_union nested_arg_roots)
        (root_sets_union outer_arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args outer_arg_roots outer_args
    type_args sigma_outer fdef fcall used' fname nested_type_args args
    raw_body synthetic_body T_body Gamma_out R_body roots_body s s_args vs
    Hbody Htarget Hsynthetic Hsafe Hcaps Hrename Hnodup_applied Htyped_body
    Hexcl_roots Htyped_outer_args Hsafe_outer_args Heval_outer_args Hprov_outer_args Hstore Hroots Hshadow
    Hrn Hnamed Hkeys.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args
    env type_args (store_names s_args) fdef fcall used' fname
    nested_type_args args raw_body synthetic_body T_body Gamma_out R_body
    roots_body Hbody Htarget Hsynthetic Hsafe Hcaps Hrename Hnodup_applied
    Htyped_body Hexcl_roots)
    as (argsr & fcallee & sigma_nested & nested_arg_roots & Sigma_origin &
        R_origin & roots_origin & Hbody_runtime & Hsafe_runtime &
        Htyped_origin & Htyped_args_origin & Hin_nested & Hname_nested &
        Hexcl_roots_origin).
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hparams_alpha_applied :
    params_alpha (apply_type_params type_args (fn_params fdef))
      (apply_type_params type_args (fn_params fcall))).
  { apply params_alpha_apply_type_compat. exact Hparams_alpha. }
  assert (Hlen_outer_roots :
    List.length outer_arg_roots =
    List.length (apply_type_params type_args (fn_params fdef))).
  { pose proof (typed_args_roots_arg_roots_length
      env Omega n R Sigma outer_args
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots Htyped_outer_args) as Hlen.
    rewrite apply_lt_params_length in Hlen. exact Hlen. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args)
      outer_arg_roots).
  { destruct (store_safe_function_value_call_args_typed_roots_store_named
      env Omega n R Sigma outer_args
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots s s_args vs
      Hsafe_outer_args Htyped_outer_args Heval_outer_args Hnamed Hkeys)
      as [_ [Hroots_named _]].
    exact Hroots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names
      (expr_local_store_names (ECallGeneric fname nested_type_args argsr))
      (root_subst_of_params (apply_type_params type_args (fn_params fdef))
        outer_arg_roots)).
  { rewrite root_subst_of_params_apply_type_params.
    rewrite <- Hbody_runtime.
    rewrite expr_local_store_names_subst_type_params_expr.
    eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  assert (Hrn_origin_applied :
    root_env_no_shadow
      (initial_root_env_for_params_origin
        (apply_type_params type_args (fn_params fdef))
        (apply_type_params type_args (fn_params fcall)))).
  { rewrite initial_root_env_for_params_origin_apply_type_params.
    apply initial_root_env_for_params_origin_no_shadow.
    - apply params_alpha_length. exact Hparams_alpha.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hrn_call_empty :
    root_env_no_shadow
      (call_param_root_env (apply_type_params type_args (fn_params fcall))
        outer_arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - rewrite params_ctx_apply_type_params.
      rewrite ctx_names_subst_type_params_ctx.
      eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (apply_type_params type_args (fn_params fcall)))) ->
      root_subst_images_exclude x
        (root_subst_of_params (apply_type_params type_args (fn_params fdef))
          outer_arg_roots)).
  { intros x Hin_x.
    rewrite params_ctx_apply_type_params in Hin_x.
    rewrite ctx_names_subst_type_params_ctx in Hin_x.
    rewrite root_subst_of_params_apply_type_params.
    apply root_subst_of_params_images_exclude.
    assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
    { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
    assert (Harg_roots_exclude :
      Forall (roots_exclude_params (fn_params fcall)) outer_arg_roots).
    { eapply root_sets_store_roots_named_excludes_params; eassumption. }
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (apply_type_params type_args (fn_params fcall))
        R_args)
      (expr_local_store_names (ECallGeneric fname nested_type_args argsr))).
  { rewrite root_env_remove_params_apply_type_params.
    rewrite <- Hbody_runtime.
    rewrite expr_local_store_names_subst_type_params_expr.
    eapply (eval_args_root_tail_fresh_names_for_fresh_call_prefix_named
      env Omega n R Sigma
      (apply_lt_params sigma_outer
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args outer_arg_roots outer_args s s_args vs
      fdef fcall used'); eassumption. }
  assert (Htyped_origin_applied :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params_origin
        (apply_type_params type_args (fn_params fdef))
        (apply_type_params type_args (fn_params fcall)))
      (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
      (ECallGeneric fname nested_type_args argsr)
      T_body Sigma_origin R_origin roots_origin).
  { rewrite initial_root_env_for_params_origin_apply_type_params.
    exact Htyped_origin. }
  assert (Hsigma_origin_eq :
    sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)) =
    sctx_of_ctx (params_ctx (apply_type_params type_args (fn_params fcall)))).
  { rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall).
    - rewrite params_ctx_apply_type_params. reflexivity.
    - rewrite <- Hcaps.
      eapply alpha_rename_fn_def_captures. exact Hrename. }
  destruct (typed_generic_direct_call_args_roots_call_frame_from_origin
    (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
    (fn_outlives fdef) (fn_lifetimes fdef)
    (apply_type_params type_args (fn_params fdef))
    (apply_type_params type_args (fn_params fcall))
    outer_arg_roots R_args
    (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcall)))
    fname nested_type_args argsr T_body Sigma_origin R_origin roots_origin
    Hparams_alpha_applied Hnodup_applied Hlen_outer_roots Hsubst_fresh
    Hrn_origin_applied Hrn_call_empty Htail_fresh Htyped_origin_applied
    Hsigma_origin_eq Hexcl_roots_origin Himages_exclude)
    as (fcallee_frame & sigma_frame & nested_arg_roots_frame &
        Sigma_frame & R_frame & Htyped_frame & Hin_frame & Hname_frame &
        Hcaps_frame & Houtlives_frame & Hret_frame & Hexcl_nested_roots &
        Hnested_roots_subset).
  exists argsr, fcallee_frame, sigma_frame, nested_arg_roots_frame,
    Sigma_frame, R_frame.
  repeat split; try assumption.
Qed.

Lemma generic_direct_call_target_alpha_rename_subst_type_params_runtime_eval :
  forall env type_args used fdef fcall used' fname nested_type_args args
      raw_body synthetic_body s s' ret,
    raw_body = subst_type_params_expr type_args (fn_body fdef) ->
    generic_direct_call_target_expr raw_body =
      Some (fname, nested_type_args, args, synthetic_body) ->
    synthetic_body = ECallGeneric fname nested_type_args args ->
    store_safe_function_value_call_args env args ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    eval env s (subst_type_params_expr type_args (fn_body fcall)) s' ret ->
    exists argsr,
      store_safe_function_value_call_args env argsr /\
      eval env s (ECallGeneric fname nested_type_args argsr) s' ret.
Proof.
  intros env type_args used fdef fcall used' fname nested_type_args args
    raw_body synthetic_body s s' ret Hbody Htarget Hsynthetic Hsafe Hrename
    Heval.
  destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime
    env type_args used fdef fcall used' fname nested_type_args args raw_body
    synthetic_body Hbody Htarget Hsynthetic Hsafe Hrename)
    as [argsr [Hbody_runtime Hsafe_runtime]].
  exists argsr.
  split; [exact Hsafe_runtime |].
  rewrite <- Hbody_runtime.
  exact Heval.
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))) /\
    exists s_args vs,
      eval_args env s args s_args vs /\ s' = s_args.
Proof.
  intros env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef Hsafe_args Hsummary Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hsummary_store Heval_call Hunique Hin_fdef Hname_fdef
    Hcaps_fdef Htyped_args Houtlives.
  dependent destruction Heval_call.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  | Hlookup_fn : lookup_fn ?fname_call ?fns = Some ?f_runtime |- _ =>
      assert (f_runtime = fdef) as -> by
        (eapply lookup_fn_unique_by_name; [exact Hlookup_fn | exact Hin_fdef | exact Hname_fdef | exact Hunique])
  end.
  match goal with
  | H : eval_args _ _ _ ?s_args0 ?vs0 |- _ =>
      rename H into Heval_args;
      rename s_args0 into s_args;
      rename vs0 into vs
  end.
  match goal with
  | H : alpha_rename_fn_def (store_names s_args) fdef =
        (?fcall0, ?used0) |- _ =>
      rename H into Hrename;
      rename fcall0 into fcall;
      rename used0 into used'
  end.
  match goal with
  | H : eval _
        (bind_params (apply_type_params type_args (fn_params fcall)) vs s_args)
        (subst_type_params_expr type_args (fn_body fcall)) ?s_body0 ret |- _ =>
      rename H into Heval_body;
      rename s_body0 into s_body
  end.
  pose proof (typed_args_roots_params_of_tys_map_param_ty
    env Omega n R Sigma args
    (apply_lt_params sigma
      (apply_type_params type_args (fn_params fdef)))
    Sigma_args R_args arg_roots Htyped_args) as Htyped_args_param_tys.
  pose proof (runtime_tfn_signature_bridge_apply_lt_params
    sigma (apply_type_params type_args (fn_params fdef))
    (subst_type_params_ty type_args (fn_ret fdef))) as Hbridge.
  pose proof (store_safe_function_value_call_args_preservation_ready
    env args Hsafe_args) as Hready_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
    args Hready_args) as Hprov_args.
  destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
    env Omega n R Sigma args
    (apply_lt_params sigma
      (apply_type_params type_args (fn_params fdef)))
    Sigma_args R_args arg_roots s s_args vs Hsafe_args Htyped_args
    Heval_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store)
    as (Hstore_args & Hargs_values_sigma & Hpres_args & Hroots_args &
        Harg_roots_values & Hshadow_args & Hrn_args & Hnamed_args &
        Hkeys_args & Hsummary_args).
  destruct (generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named
    env Omega n R Sigma Sigma_args R_args arg_roots args type_args fdef fcall
    (map param_ty
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef))))
    (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
    s s_args vs used' Hsummary Hcaps_fdef Hbridge Hsafe_args
    Htyped_args_param_tys Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename)
    as (T_body & Sigma_out & R_body & roots_body & ret_roots &
        Hsummary_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Hresult_subset).
  pose (ps_runtime := apply_type_params type_args (fn_params fcall)).
  destruct (generic_direct_call_args_bind_type_params_runtime_package
    env Omega n R Sigma args type_args sigma fdef fcall used'
    s s_args vs Sigma_args R_args arg_roots Hsafe_args Heval_args
    Htyped_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hunique
    Hsummary_store Hrename)
    as (Hstore_bind & Hroots_bind & Hshadow_bind & Hrn_bind & Hcover_bind &
        Hnamed_bind & Hkeys_bind & Hsummary_bind & Hframe_start).
  fold ps_runtime in Hstore_bind, Hroots_bind, Hshadow_bind, Hrn_bind,
    Hcover_bind, Hnamed_bind, Hkeys_bind, Hsummary_bind, Hframe_start.
  assert (Hnodup : NoDup (ctx_names (params_ctx ps_runtime))).
  { subst ps_runtime.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  pose (body_env := global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fcall))).
  fold body_env in Hsummary_body.
  fold ps_runtime in Hsummary_body.
  rename Hsummary_body into Hsummary_body_env.
  assert (Hstore_bind_body_env :
    store_typed_prefix body_env (bind_params ps_runtime vs s_args)
      (sctx_of_ctx (params_ctx ps_runtime))).
  { subst body_env.
    eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind. }
  assert (Heval_body_body_env :
    eval body_env (bind_params ps_runtime vs s_args)
      (subst_type_params_expr type_args (fn_body fcall)) s_body ret).
  { subst body_env ps_runtime.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_body. }
  assert (Hsummary_bind_body_env :
    store_function_closure_targets_summary body_env
      (bind_params ps_runtime vs s_args)).
  { subst body_env.
    apply store_function_closure_targets_summary_global_env_with_local_bounds.
    exact Hsummary_bind. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
  destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret Hstore_bind_body_env
    Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind
    Hsummary_bind_body_env Heval_body_body_env Hunique_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
      [Hrootset_body [Hshadow_body [Hrn_body [Hnamed_body
        [Hkeys_body Hsummary_body_store]]]]]]]]]].
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_param_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret ps_runtime s_args
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env
    Hcover_bind Hframe_start)
    as [frame_final Hscope_body].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret_alpha Hparams_alpha]].
  assert (Hargs_values_fdef_type :
    eval_args_values_have_types env Omega s_args vs
      (apply_type_params type_args (fn_params fdef))).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_values_sigma. }
  assert (Hargs_values_fcall_type :
    eval_args_values_have_types env Omega s_args vs ps_runtime).
  { subst ps_runtime.
    eapply eval_args_values_have_types_params_alpha.
    - apply params_alpha_apply_type_compat. exact Hparams_alpha.
    - exact Hargs_values_fdef_type. }
  assert (Hfresh : params_fresh_in_store ps_runtime s_args).
  { subst ps_runtime.
    unfold params_fresh_in_store.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hframe_scope_start :
    store_frame_scope ps_runtime (sctx_of_ctx (params_ctx ps_runtime))
      (bind_params ps_runtime vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_values_fcall_type. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh (sctx_of_ctx (params_ctx ps_runtime)) s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named
    body_env (fn_outlives fcall) (fn_lifetimes fcall)
    (call_param_root_env ps_runtime arg_roots R_args)
    (sctx_of_ctx (params_ctx ps_runtime))
    (subst_type_params_expr type_args (fn_body fcall)) T_body Sigma_out
    R_body roots_body ret_roots Hsummary_body_env
    (bind_params ps_runtime vs s_args) s_body ret ps_runtime s_args
    Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
    Hkeys_bind Hsummary_bind_body_env Heval_body_body_env Hunique_body_env
    Hcover_bind Hframe_scope_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope_body Hframe_fresh_body]]]]].
  assert (Hsame_body :
    sctx_same_bindings (sctx_of_ctx (params_ctx ps_runtime)) Sigma_out).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots.
    eapply expr_root_shadow_store_safe_narrow_summary_typed.
    exact Hsummary_body_env. }
  assert (Hscope_body_args : store_param_scope ps_runtime s_body s_args).
  { eapply store_frame_scope_param_scope. exact Hframe_scope_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hv_ret_fcall :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fcall))).
  { eapply value_has_type_compatible.
    - exact Hv_body_env.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef :
    value_has_type env s_body ret
      (subst_type_params_ty type_args (fn_ret fdef))).
  { rewrite Hret_alpha. exact Hv_ret_fcall. }
  destruct (store_remove_params_cleanup_excludes
              ps_runtime s_body s_args R_body roots_body ret
              Hscope_body_args Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_roots Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params ps_runtime s_body) ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  assert (Hremoved_exact : store_remove_params ps_runtime s_body = s_args).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - exact Hscope_body_args.
    - exact Hframe_scope_body. }
  fold ps_runtime.
  rewrite Hremoved_exact.
  split.
  - constructor.
    + exact Hstore_args.
    + rewrite <- Hremoved_exact. exact Hv_final.
    + exact Hpres_args.
    + exact Hroots_args.
    + eapply direct_call_value_roots_within_store_subset; eassumption.
    + exact Hshadow_args.
    + exact Hrn_args.
    + exact Hnamed_args.
    + exact Hkeys_args.
    + exact Hsummary_args.
  - exists s_args, vs.
    split; [exact Heval_args | reflexivity].
Qed.

Lemma eval_generic_direct_call_store_safe_narrow_summary_package_prefix_named_expr :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    generic_direct_call_runtime_package env s s' ret Sigma_args R_args
      arg_roots
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros.
  destruct (eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_expr
    env Omega n R Sigma fname type_args args sigma Sigma_args R_args
    arg_roots s s' ret fdef) as [Hpkg _]; eauto.
Qed.


Lemma eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named :
  forall env Omega n R Sigma fname type_args args sigma Sigma_args R_args
      arg_roots s s' ret fdef,
    store_safe_function_value_call_args env args ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    store_typed_prefix env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_function_closure_targets_summary env s ->
    eval env s (ECallGeneric fname type_args args) s' ret ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma
        (apply_type_params type_args (fn_params fdef)))
      Sigma_args R_args arg_roots ->
    Forall (fun '(a, b) => outlives Omega a b)
      (apply_lt_outlives sigma (fn_outlives fdef)) ->
    value_has_type env s' ret
      (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef))).
Proof.
  intros.
  eapply eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_expr;
    eassumption.
Qed.

