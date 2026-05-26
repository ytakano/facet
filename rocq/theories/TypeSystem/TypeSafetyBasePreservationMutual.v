From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyBasePreservationAssign.
From Facet.TypeSystem Require Import TypeSafetyClosureCleanupFrame
  TypeSafetyHiddenFrameCleanupFacts.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma type_lookup_path_global_env_with_local_bounds :
  forall env bounds T path,
    type_lookup_path (global_env_with_local_bounds env bounds) T path =
    type_lookup_path env T path.
Proof.
  intros env bounds T path.
  revert env bounds T.
  induction path as [| field rest IH]; intros env bounds T; simpl; auto.
  destruct T as [u core]; simpl.
  destruct core; try reflexivity.
  change (lookup_struct s (global_env_with_local_bounds env bounds))
    with (lookup_struct s env).
  destruct (lookup_struct s env) as [sdef |] eqn:Hlookup; [| reflexivity].
  destruct (lookup_field field (struct_fields sdef)); [apply IH | reflexivity].
Qed.

Lemma value_has_type_global_env_with_local_bounds :
  forall env bounds s v T,
    value_has_type env s v T ->
    value_has_type (global_env_with_local_bounds env bounds) s v T
with struct_fields_have_type_global_env_with_local_bounds :
  forall env bounds s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    struct_fields_have_type (global_env_with_local_bounds env bounds)
      s lts args fields defs
with enum_values_have_type_global_env_with_local_bounds :
  forall env bounds s values tys,
    enum_values_have_type env s values tys ->
    enum_values_have_type (global_env_with_local_bounds env bounds)
      s values tys.
Proof.
  - intros env bounds s v T H.
    induction H;
      try solve
        [ econstructor; simpl in *; eauto;
          rewrite ?type_lookup_path_global_env_with_local_bounds; eauto ].
  - intros env bounds s lts args fields defs H.
    induction H; try solve [econstructor; eauto].
  - intros env bounds s values tys H.
    induction H; try solve [econstructor; eauto].
Qed.

Lemma value_has_type_clear_global_env_local_bounds :
  forall env bounds s v T,
    value_has_type (global_env_with_local_bounds env bounds) s v T ->
    value_has_type env s v T
with struct_fields_have_type_clear_global_env_local_bounds :
  forall env bounds s lts args fields defs,
    struct_fields_have_type (global_env_with_local_bounds env bounds)
      s lts args fields defs ->
    struct_fields_have_type env s lts args fields defs
with enum_values_have_type_clear_global_env_local_bounds :
  forall env bounds s values tys,
    enum_values_have_type (global_env_with_local_bounds env bounds)
      s values tys ->
    enum_values_have_type env s values tys.
Proof.
  - intros env bounds s v T H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq;
      try solve
        [ subst; econstructor; simpl in *; eauto;
          rewrite ?type_lookup_path_global_env_with_local_bounds in *; eauto ].
    all: try
      (subst; econstructor; simpl in *; eauto;
       rewrite ?type_lookup_path_global_env_with_local_bounds in *; eauto).
  - intros env bounds s lts args fields defs H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq; try solve [econstructor; eauto].
    all: try (subst; eapply SFHT_Cons; eauto;
      eapply value_has_type_clear_global_env_local_bounds; eauto).
  - intros env bounds s values tys H.
    remember (global_env_with_local_bounds env bounds) as env' eqn:Heq.
    revert env bounds Heq.
    induction H; intros env0 bounds Heq; try solve [econstructor; eauto].
    all: try (subst; eapply EVHT_Cons; eauto;
      eapply value_has_type_clear_global_env_local_bounds; eauto).
Qed.

Lemma eval_args_values_have_types_params_of_tys_enum_values :
  forall env Ω s values tys,
    eval_args_values_have_types env Ω s values (params_of_tys tys) ->
    enum_values_have_type env s values tys.
Proof.
  intros env Ω s values.
  induction values as [| v values IH]; intros tys Htyped;
    destruct tys as [| T tys]; simpl in Htyped.
  - constructor.
  - inversion Htyped.
  - inversion Htyped.
  - inversion Htyped; subst.
    constructor.
	    + eapply VHT_Compatible; eassumption.
	    + apply IH. assumption.
Qed.

Lemma ty_compatible_refl_exact :
  forall Ω T,
    ty_compatible Ω T T.
Proof.
  intros Ω [u core].
  apply TC_Core.
  - constructor.
  - reflexivity.
Qed.

Lemma enum_values_have_type_eval_args_values :
  forall env Ω s values tys ps,
    enum_values_have_type env s values tys ->
    map param_ty ps = tys ->
    eval_args_values_have_types env Ω s values ps.
Proof.
  intros env Ω s values tys ps Hvalues.
  revert ps.
  induction Hvalues as [| v values T tys Hv Hrest IH]; intros ps Htys;
    destruct ps as [| p ps]; simpl in Htys; try discriminate.
  - constructor.
  - inversion Htys; subst.
    eapply AHT_Cons with (T_actual := param_ty p).
    + exact Hv.
    + apply ty_compatible_refl_exact.
    + apply IH. reflexivity.
Qed.

Lemma eval_args_values_have_types_param_tys :
  forall env Ω s values ps1 ps2,
    eval_args_values_have_types env Ω s values ps1 ->
    map param_ty ps2 = map param_ty ps1 ->
    eval_args_values_have_types env Ω s values ps2.
Proof.
  intros env Ω s values ps1 ps2 Hargs.
  revert ps2.
  induction Hargs as [| v values p ps T_actual Hv Hcompat Hargs IH];
    intros ps2 Htys; destruct ps2 as [| p2 ps2]; simpl in Htys; try discriminate.
  - constructor.
  - inversion Htys; subst.
    econstructor.
    + exact Hv.
    + rewrite H0. exact Hcompat.
    + apply IH. exact H1.
Qed.

Lemma match_binder_params_opt_param_tys :
  forall binders tys ps,
    match_binder_params_opt binders tys = Some ps ->
    map param_ty ps = tys.
Proof.
  induction binders as [| x xs IH]; intros tys ps Hmatch;
    destruct tys as [| T Ts]; simpl in Hmatch; try discriminate.
  - inversion Hmatch. reflexivity.
  - destruct (match_binder_params_opt xs Ts) as [ps_tail |] eqn:Htail;
      try discriminate.
    inversion Hmatch; subst ps. simpl.
    rewrite (IH Ts ps_tail Htail). reflexivity.
Qed.

Lemma match_payload_params_opt_param_tys :
  forall binders lts args v ps,
    match_payload_params_opt binders lts args v = Some ps ->
    map param_ty ps =
      map (instantiate_enum_variant_field_ty lts args) (enum_variant_fields v).
Proof.
  intros binders lts args v ps Hmatch.
  unfold match_payload_params_opt in Hmatch.
  eapply match_binder_params_opt_param_tys. exact Hmatch.
Qed.

Lemma store_typed_params_fresh :
  forall env s Σ ps,
    store_typed env s Σ ->
    ctx_lookup_params_none_b ps Σ = true ->
    params_fresh_in_store ps s.
Proof.
  intros env s Σ ps Hstore Hnone x Hin Hstore_name.
  rewrite (store_typed_names env s Σ Hstore) in Hstore_name.
  eapply ctx_lookup_params_none_b_not_in_names; eassumption.
Qed.

Lemma store_names_bind_params_in_any :
  forall ps vs s x,
    In x (store_names (bind_params ps vs s)) ->
    In x (ctx_names (params_ctx ps)) \/ In x (store_names s).
Proof.
  induction ps as [| p ps IH]; intros vs s x Hin.
  - simpl in Hin. right. exact Hin.
  - destruct vs as [| v vs].
    + simpl in Hin. right. exact Hin.
    + simpl in Hin.
      destruct Hin as [Hin_head | Hin_tail].
      * left. simpl. left. exact Hin_head.
      * destruct (IH vs s x Hin_tail) as [Hin_params | Hin_store].
        -- left. simpl. right. exact Hin_params.
        -- right. exact Hin_store.
Qed.

Lemma bind_params_head_fresh_in_tail_any :
  forall s p ps vs,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    params_fresh_in_store (p :: ps) s ->
    ~ In (param_name p) (store_names (bind_params ps vs s)).
Proof.
  intros s p ps vs Hnodup Hfresh Hin.
  destruct (store_names_bind_params_in_any ps vs s (param_name p) Hin)
    as [Hin_params | Hin_store].
  - eapply params_ctx_names_nodup_head_not_tail; eassumption.
  - eapply params_fresh_in_store_head; eassumption.
Qed.

Lemma bind_params_ref_targets_preserved_fresh :
  forall env s ps vs,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    store_ref_targets_preserved env s (bind_params ps vs s).
Proof.
  intros env s ps.
  induction ps as [| p ps IH]; intros vs Hnodup Hfresh.
  - simpl. apply store_ref_targets_preserved_refl.
  - destruct vs as [| v vs].
    + simpl. apply store_ref_targets_preserved_refl.
    + simpl.
      eapply store_ref_targets_preserved_trans.
      * eapply IH.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
      * eapply store_add_fresh_ref_targets_preserved.
        apply store_lookup_not_in_names.
        eapply bind_params_head_fresh_in_tail_any; eassumption.
Qed.

Lemma store_typed_bind_params_same_ctx :
  forall env Ω s Σ values ps_store ps_ctx,
    store_typed env s Σ ->
    NoDup (ctx_names (params_ctx ps_store)) ->
    params_fresh_in_store ps_store s ->
    eval_args_values_have_types env Ω s values ps_ctx ->
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_ctx) ->
    map param_ty ps_store = map param_ty ps_ctx ->
    store_typed env (bind_params ps_store values s) (sctx_add_params ps_ctx Σ).
Proof.
  intros env Ω s Σ values ps_store ps_ctx Hstore Hnodup Hfresh Hargs.
  revert ps_store Hnodup Hfresh.
  induction Hargs as [| v values p ps T_actual Hv Hcompat Hargs IH];
    intros ps_store Hnodup Hfresh Hnames Htys.
  - destruct ps_store as [| p_store ps_store]; simpl in Hnames; try discriminate.
    simpl. exact Hstore.
  - destruct ps_store as [| p_store ps_store]; simpl in Hnames; try discriminate.
    simpl in Htys. inversion Hnames as [[Hname_eq Hnames_tail]].
    inversion Htys as [[Hty_eq Htys_tail]].
    assert (Hargs_store_tail :
      eval_args_values_have_types env Ω s values ps_store).
    { eapply eval_args_values_have_types_param_tys.
      - exact Hargs.
      - exact Htys_tail. }
    simpl.
    constructor.
    + simpl. split.
      * exact Hname_eq.
      * split.
        -- rewrite Hty_eq. apply ty_lifetime_equiv_refl.
        -- split.
           ++ apply binding_state_refines_refl.
           ++ eapply value_has_type_store_preserved.
              ** eapply VHT_Compatible.
                 --- exact Hv.
                 --- rewrite Hty_eq. exact Hcompat.
              ** eapply (bind_params_ref_targets_preserved env Ω s (v :: values)
                    (p_store :: ps_store)).
                 --- exact Hnodup.
                 --- exact Hfresh.
                 --- eapply eval_args_values_have_types_param_tys.
                     +++ exact (AHT_Cons env Ω s v values p ps T_actual
                           Hv Hcompat Hargs).
                     +++ exact Htys.
    + eapply store_typed_store_param_preserved.
      * eapply IH.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
        -- exact Hnames_tail.
        -- exact Htys_tail.
      * eapply store_add_fresh_ref_targets_preserved.
        apply store_lookup_not_in_names.
        eapply bind_params_head_fresh_in_tail.
        -- exact Hnodup.
        -- exact Hfresh.
        -- eapply eval_args_values_have_types_param_tys.
           ++ exact Hargs.
           ++ exact Htys_tail.
Qed.

Lemma store_typed_bind_match_payload_params :
  forall env (Ω : outlives_ctx) s Σ values ps_runtime ps_typed,
    store_typed env s Σ ->
    params_names_nodup_b ps_typed = true ->
    ctx_lookup_params_none_b ps_typed Σ = true ->
    enum_values_have_type env s values (map param_ty ps_typed) ->
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    map param_ty ps_runtime = map param_ty ps_typed ->
    store_typed env (bind_params ps_runtime values s)
      (sctx_add_params ps_typed Σ).
Proof.
  intros env Ω s Σ values ps_runtime ps_typed Hstore Hnodup Hnone
    Hvalues Hnames Htys.
  eapply store_typed_bind_params_same_ctx with (Ω := Ω).
  - exact Hstore.
  - rewrite Hnames.
    eapply params_names_nodup_b_sound. exact Hnodup.
  - unfold params_fresh_in_store in *.
    rewrite Hnames.
    eapply store_typed_params_fresh; eassumption.
  - eapply enum_values_have_type_eval_args_values.
    + exact Hvalues.
    + reflexivity.
  - exact Hnames.
  - exact Htys.
Qed.

Lemma store_typed_bind_match_payload_params_lifetime_aux :
  forall env s Σ values ps_runtime ps_typed,
    store_typed env s Σ ->
    enum_values_have_type env s values (map param_ty ps_typed) ->
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    Forall2 ty_lifetime_equiv
      (map param_ty ps_runtime) (map param_ty ps_typed) ->
    NoDup (ctx_names (params_ctx ps_runtime)) ->
    params_fresh_in_store ps_runtime s ->
    store_typed env (bind_params ps_runtime values s)
      (sctx_add_params ps_typed Σ).
Proof.
  intros env s Σ values ps_runtime ps_typed Hstore Hvalues.
  revert values ps_runtime Hvalues.
  induction ps_typed as [| p_typed ps_typed IH];
    intros values ps_runtime Hvalues Hnames Hequiv Hnodup Hfresh.
  - simpl in Hvalues.
    inversion Hvalues; subst values.
    destruct ps_runtime; simpl in Hnames; try discriminate.
    simpl. exact Hstore.
  - destruct values as [| v values]; simpl in Hvalues; inversion Hvalues;
      subst.
    destruct ps_runtime as [| p_runtime ps_runtime];
      simpl in Hnames, Hequiv; try discriminate.
    inversion Hnames as [[Hname_eq Hnames_tail]].
    inversion Hequiv as [| T_runtime T_typed tys_runtime tys_typed
      Hty_equiv Htys_equiv]; subst.
    simpl.
    constructor.
    + simpl.
      split.
      * exact Hname_eq.
      * split.
        -- exact Hty_equiv.
        -- split.
           ++ apply binding_state_refines_refl.
           ++ eapply value_has_type_store_preserved.
              ** eapply VHT_LifetimeEquiv.
                 --- exact H2.
                 --- apply ty_lifetime_equiv_sym. exact Hty_equiv.
              ** eapply (bind_params_ref_targets_preserved_fresh
                   env s (p_runtime :: ps_runtime) (v :: values)).
                 --- exact Hnodup.
                 --- exact Hfresh.
    + eapply store_typed_store_param_preserved.
      * eapply IH.
        -- exact H4.
        -- exact Hnames_tail.
        -- exact Htys_equiv.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
      * eapply store_add_fresh_ref_targets_preserved.
        apply store_lookup_not_in_names.
        eapply bind_params_head_fresh_in_tail_any; eassumption.
Qed.

Lemma store_typed_bind_match_payload_params_lifetime :
  forall env s Σ values ps_runtime ps_typed,
    store_typed env s Σ ->
    params_names_nodup_b ps_typed = true ->
    ctx_lookup_params_none_b ps_typed Σ = true ->
    enum_values_have_type env s values (map param_ty ps_typed) ->
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    Forall2 ty_lifetime_equiv
      (map param_ty ps_runtime) (map param_ty ps_typed) ->
    store_typed env (bind_params ps_runtime values s)
      (sctx_add_params ps_typed Σ).
Proof.
  intros env s Σ values ps_runtime ps_typed Hstore Hnodup Hnone Hvalues
    Hnames Hequiv.
  eapply store_typed_bind_match_payload_params_lifetime_aux.
  - exact Hstore.
  - exact Hvalues.
  - exact Hnames.
  - exact Hequiv.
  - rewrite Hnames.
    eapply params_names_nodup_b_sound. exact Hnodup.
  - unfold params_fresh_in_store in *.
    rewrite Hnames.
    eapply store_typed_params_fresh; eassumption.
Qed.

Lemma store_remove_match_payload_cleanup_value_typed_names :
  forall ps_runtime ps_typed env s_body frame R roots v T,
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    store_param_scope ps_runtime s_body frame ->
    store_roots_within R s_body ->
    value_roots_within roots v ->
    store_no_shadow s_body ->
    params_names_nodup_b ps_typed = true ->
    roots_exclude_params ps_typed roots ->
    root_env_excludes_params ps_typed R ->
    value_has_type env s_body v T ->
    exists locals,
      store_remove_params ps_runtime s_body = locals ++ frame /\
      value_has_type env (store_remove_params ps_runtime s_body) v T /\
      store_refs_exclude_params ps_runtime
        (store_remove_params ps_runtime s_body).
Proof.
  intros ps_runtime ps_typed env s_body frame R roots v T Hnames Hscope
    Hstore Hvalue_roots Hshadow Hnodup Hroots_excl Henv_excl Hvalue.
  eapply store_remove_params_cleanup_value_typed_excludes.
  - exact Hscope.
  - exact Hstore.
  - exact Hvalue_roots.
  - exact Hshadow.
  - rewrite Hnames.
    eapply params_names_nodup_b_sound. exact Hnodup.
  - unfold roots_exclude_params in *.
    rewrite Hnames. exact Hroots_excl.
  - unfold root_env_excludes_params in *.
    rewrite Hnames. exact Henv_excl.
  - exact Hvalue.
Qed.

Lemma store_typed_ctx_merge_many_left :
  forall env s Σ tail Γ,
    store_typed env s Σ ->
    ctx_merge_many (ctx_of_sctx Σ) (map ctx_of_sctx tail) = Some Γ ->
    store_typed env s (sctx_of_ctx Γ).
Proof.
  intros env s Σ tail.
  revert Σ.
  induction tail as [|Σh rest IH]; intros Σ Γ Hstore Hmerge.
  - simpl in Hmerge. inversion Hmerge; subst. exact Hstore.
  - simpl in Hmerge.
    destruct (ctx_merge (ctx_of_sctx Σ) (ctx_of_sctx Σh)) as [Σm |] eqn:Hhead;
      try discriminate.
    eapply IH.
    + eapply store_typed_ctx_merge_left. exact Hstore. exact Hhead.
    + exact Hmerge.
Qed.

Lemma usage_sub_left_nonempty :
  forall T Ts,
    usage_sub (ty_usage T) (usage_max_tys_nonempty T Ts).
Proof.
  intros T Ts.
  destruct T as [u c]; simpl.
  induction Ts as [|T rest IH]; simpl.
  - destruct u; constructor.
  - apply usage_sub_left_max.
Qed.

Lemma value_has_type_match_head_result :
  forall env s v T_head Ts_tail,
    value_has_type env s v T_head ->
    value_has_type env s v
      (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head)).
Proof.
  intros env s v [u c] Ts_tail Hv.
  eapply value_has_type_compatible with (Ω := []).
  - exact Hv.
  - apply TC_Core.
    + exact (usage_sub_left_nonempty (MkTy u c) Ts_tail).
    + reflexivity.
Qed.

Lemma usage_sub_trans :
  forall u1 u2 u3,
    usage_sub u1 u2 ->
    usage_sub u2 u3 ->
    usage_sub u1 u3.
Proof.
  intros u1 u2 u3 H12 H23.
  destruct H12; inversion H23; subst; constructor.
Qed.

Lemma usage_sub_tail_nonempty :
  forall T_head Ts T,
    In T Ts ->
    usage_sub (ty_usage T) (usage_max_tys_nonempty T_head Ts).
Proof.
  intros T_head Ts.
  revert T_head.
  induction Ts as [|T0 rest IH]; intros T_head T Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst T0. simpl.
      eapply usage_sub_trans.
      * apply usage_sub_left_nonempty.
      * apply usage_sub_right_max.
    + simpl.
      eapply usage_sub_trans.
      * eapply IH. exact Hin.
      * apply usage_sub_right_max.
Qed.

Lemma value_has_type_match_tail_result :
  forall env s v T_head Ts_tail T,
    In T Ts_tail ->
    ty_core T = ty_core T_head ->
    value_has_type env s v T ->
    value_has_type env s v
      (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head)).
Proof.
  intros env s v [uh ch] Ts_tail [u c] Hin Hcore Hv.
  simpl in Hcore. subst c.
  eapply value_has_type_compatible with (Ω := []).
  - exact Hv.
  - apply TC_Core.
    + exact (usage_sub_tail_nonempty (MkTy uh ch) Ts_tail (MkTy u ch) Hin).
    + reflexivity.
Qed.

Lemma store_typed_ctx_merge_many_selected :
  forall env s Σ0 tail Γ Σsel,
    store_typed env s Σsel ->
    sctx_same_bindings Σ0 Σsel ->
    Forall (sctx_same_bindings Σ0) tail ->
    In Σsel (Σ0 :: tail) ->
    ctx_merge_many (ctx_of_sctx Σ0) (map ctx_of_sctx tail) = Some Γ ->
    store_typed env s (sctx_of_ctx Γ).
Proof.
  intros env s Σ0 tail.
  revert Σ0.
  induction tail as [|Σh rest IH]; intros Σ0 Γ Σsel Hstore Hsame Hforall Hin Hmerge.
  - simpl in Hmerge. inversion Hmerge; subst.
    simpl in Hin. destruct Hin as [Heq | []]. subst. exact Hstore.
  - simpl in Hmerge.
    destruct (ctx_merge (ctx_of_sctx Σ0) (ctx_of_sctx Σh)) as [Σm |] eqn:Hhead;
      try discriminate.
    inversion Hforall as [|? ? Hsame_h Hforall_rest]; subst.
    simpl in Hin. destruct Hin as [Heq | [Heq | Hin_rest]].
    + subst. eapply store_typed_ctx_merge_many_left.
      * eapply store_typed_ctx_merge_left.
        -- exact Hstore.
        -- exact Hhead.
      * exact Hmerge.
    + subst. eapply store_typed_ctx_merge_many_left.
      * eapply store_typed_ctx_merge_right.
        -- exact Hstore.
        -- apply sctx_same_bindings_type_eq. exact Hsame_h.
        -- exact Hhead.
      * exact Hmerge.
    + eapply IH.
      * exact Hstore.
      * eapply sctx_same_bindings_trans.
        -- apply sctx_same_bindings_sym.
           eapply ctx_merge_same_bindings_left. exact Hhead.
        -- exact Hsame.
      * eapply Forall_impl.
        -- intros Σr Hsame_r.
           eapply sctx_same_bindings_trans.
           ++ apply sctx_same_bindings_sym.
              eapply ctx_merge_same_bindings_left. exact Hhead.
           ++ exact Hsame_r.
        -- exact Hforall_rest.
      * simpl. right. exact Hin_rest.
      * exact Hmerge.
Qed.

Lemma typed_match_tail_lookup :
  forall env Ω n lts args Σ branches variants expected_core Σs Ts name vdef e,
    typed_match_tail_env_structural env Ω n lts args Σ branches variants
      expected_core Σs Ts ->
    lookup_enum_variant name variants = Some vdef ->
    lookup_expr_branch name branches = Some e ->
    exists T Σv_payload Σv ps binders,
      lookup_expr_branch_binders name branches = Some binders /\
      match_payload_params_opt binders lts args vdef = Some ps /\
      typed_env_structural env Ω n (sctx_add_params ps Σ) e T Σv_payload /\
      Σv = sctx_remove_params ps Σv_payload /\
      ty_core T = expected_core /\
      In Σv Σs /\
      In T Ts.
Proof.
  intros env Ω n lts args Σ branches variants expected_core Σs Ts name vdef e Htail.
  induction Htail as
    [lts args Σ branches expected_core
    |Σ branches v rest e0 T0 Σv_payload Σv Σs Ts expected_core
       binders ps lts args Hfields_empty Hbinders_empty Hbinders Hparams
       Hnodup Hctx_none Hlookup Htyped Hparams_ok Hremove Hcore
       Htail IHtail];
    intros Hvariant Hbranch.
  - simpl in Hvariant. discriminate.
  - simpl in Hvariant.
    destruct (String.eqb name (enum_variant_name v)) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name.
      rewrite Hlookup in Hbranch. inversion Hbranch; subst e.
      inversion Hvariant; subst vdef.
      exists T0, Σv_payload, Σv, ps, binders.
      repeat split; simpl; auto.
      eapply match_payload_params_opt_infer_ok. exact Hparams.
    + eapply IHtail in Hvariant; [| exact Hbranch].
      destruct Hvariant as [T' [Σpayload' [Σ' [ps' [binders' Hrest]]]]].
      destruct Hrest as [Hbinders' [Hparams' [Htyped' [Hremove'
        [Hcore' [HinΣ HinT]]]]]].
      exists T', Σpayload', Σ', ps', binders'. repeat split; simpl; auto.
Qed.

Lemma typed_match_tail_lookup_no_payload :
  forall env Ω n lts args Σ branches variants expected_core Σs Ts
      name vdef binders,
    typed_match_tail_env_structural env Ω n lts args Σ branches variants
      expected_core Σs Ts ->
    lookup_enum_variant name variants = Some vdef ->
    lookup_expr_branch_binders name branches = Some binders ->
    enum_variant_fields vdef = [] /\ binders = [].
Proof.
  intros env Ω n lts args Σ branches variants expected_core Σs Ts
    name vdef binders Htail.
  induction Htail as
    [lts args Σ branches expected_core
    |Σ branches v rest e0 T0 Σv_payload Σv Σs Ts expected_core
       binders0 ps lts args Hfields_empty Hbinders_empty Hbinders
       Hparams Hnodup Hctx_none Hlookup Htyped Hparams_ok Hremove Hcore
       Htail IHtail];
    intros Hvariant Hbranch_binders.
  - simpl in Hvariant. discriminate.
  - simpl in Hvariant.
    destruct (String.eqb name (enum_variant_name v)) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name.
      inversion Hvariant; subst vdef.
      rewrite Hbinders in Hbranch_binders.
      inversion Hbranch_binders; subst binders.
      split; assumption.
    + eapply IHtail; eassumption.
Qed.

Lemma lookup_expr_branch_deterministic :
  forall name branches e1 e2,
    lookup_expr_branch name branches = Some e1 ->
    lookup_expr_branch name branches = Some e2 ->
    e1 = e2.
Proof.
  intros name branches e1 e2 H1 H2.
  rewrite H1 in H2. inversion H2. reflexivity.
Qed.

Lemma lookup_enum_variant_deterministic :
  forall name variants v1 v2,
    lookup_enum_variant name variants = Some v1 ->
    lookup_enum_variant name variants = Some v2 ->
    v1 = v2.
Proof.
  intros name variants.
  induction variants as [| v variants IH]; intros v1 v2 H1 H2; simpl in *.
  - discriminate.
  - destruct (String.eqb name (enum_variant_name v)).
    + inversion H1; inversion H2; subst. reflexivity.
    + eapply IH; eassumption.
Qed.

Lemma enum_variant_field_tys_lifetime_equiv :
  forall lts_actual lts_expected args_actual args_expected fields,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    Forall2 ty_lifetime_equiv
      (map (instantiate_enum_variant_field_ty lts_actual args_actual) fields)
      (map (instantiate_enum_variant_field_ty lts_expected args_expected) fields).
Proof.
  intros lts_actual lts_expected args_actual args_expected fields Hargs.
  induction fields as [| T fields IH]; simpl; constructor.
  - eapply instantiate_enum_variant_field_ty_lifetime_equiv. exact Hargs.
  - exact IH.
Qed.

Lemma enum_values_have_type_lifetime_equiv :
  forall env s values tys_actual tys_expected,
    enum_values_have_type env s values tys_actual ->
    Forall2 ty_lifetime_equiv tys_actual tys_expected ->
    enum_values_have_type env s values tys_expected.
Proof.
  intros env s values tys_actual tys_expected Hvalues Hequiv.
  revert tys_expected Hequiv.
  induction Hvalues as [| v values T tys Hv Hrest IH];
    intros tys_expected Hequiv; inversion Hequiv; subst.
  - constructor.
  - constructor.
    + eapply VHT_LifetimeEquiv; eassumption.
    + eapply IH. assumption.
Qed.

Lemma value_has_type_enum_values_lookup :
  forall env s enum_name variant_name lts_val args_val values T enum_typed
      lts args edef vdef,
    value_has_type env s (VEnum enum_name variant_name lts_val args_val values) T ->
    ty_core T = TEnum enum_typed lts args ->
    lookup_enum enum_typed env = Some edef ->
    lookup_enum_variant variant_name (enum_variants edef) = Some vdef ->
    enum_values_have_type env s values
      (map (instantiate_enum_variant_field_ty lts args)
        (enum_variant_fields vdef)).
Proof.
  intros env s enum_name variant_name lts_val args_val values T enum_typed
    lts args edef vdef Htyped.
  revert enum_typed lts args edef vdef.
  dependent induction Htyped; intros enum_typed lts0 args0 edef0 vdef0
    Hcore Hlookup_typed Hvariant_typed; try discriminate.
  - unfold instantiate_enum_ty in Hcore. simpl in Hcore.
    inversion Hcore; subst.
    destruct (lookup_enum_success_rootfacts env enum_name edef H) as [_ Hedef_name].
    subst enum_name.
    pose proof (lookup_enum_deterministic env (Program.enum_name edef) edef edef0
      H Hlookup_typed) as Heq.
    subst edef0.
    pose proof (lookup_enum_variant_deterministic variant_name
      (enum_variants edef) vdef vdef0 H0 Hvariant_typed) as Hvdef.
    subst vdef0. exact H1.
  - destruct T_expected as [ue ce], T_actual as [ua ca].
    simpl in Hcore. subst ce.
    match goal with
    | Hcompat : ty_compatible _ _ _ |- _ =>
        inversion Hcompat; subst; try discriminate
    end.
    eapply IHHtyped; eauto; reflexivity.
	  - destruct T_expected as [ue ce], T_actual as [ua ca].
	    simpl in Hcore. subst ce.
	    match goal with
	    | Hequiv : ty_lifetime_equiv _ _ |- _ =>
	        inversion Hequiv; subst; try discriminate
	    end.
	    eapply enum_values_have_type_lifetime_equiv.
	    + eapply IHHtyped; eauto; reflexivity.
	    + eapply enum_variant_field_tys_lifetime_equiv. eassumption.
Qed.

Lemma value_has_type_enum_variant_lookup :
  forall env s enum_name variant_name lts_val args_val values T enum_typed lts args edef,
    value_has_type env s (VEnum enum_name variant_name lts_val args_val values) T ->
    ty_core T = TEnum enum_typed lts args ->
    lookup_enum enum_typed env = Some edef ->
    exists vdef,
      enum_name = enum_typed /\
      lookup_enum_variant variant_name (enum_variants edef) = Some vdef.
Proof.
  intros env s enum_name variant_name lts_val args_val values T enum_typed lts args edef Htyped.
  revert enum_typed lts args edef.
  dependent induction Htyped; intros enum_typed lts0 args0 edef0 Hcore Hlookup_typed;
    try discriminate.
  - unfold instantiate_enum_ty in Hcore. simpl in Hcore.
    inversion Hcore; subst.
    destruct (lookup_enum_success_rootfacts env enum_name edef H) as [_ Hedef_name].
    subst enum_name.
    pose proof (lookup_enum_deterministic env (Program.enum_name edef) edef edef0
      H Hlookup_typed) as Heq.
    subst edef0.
    exists vdef. split; [reflexivity | eassumption].
  - destruct T_expected as [ue ce], T_actual as [ua ca].
    simpl in Hcore. subst ce.
    match goal with
    | Hcompat : ty_compatible _ _ _ |- _ => inversion Hcompat; subst; try discriminate
    end.
    eapply IHHtyped; eauto; reflexivity.
  - destruct T_expected as [ue ce], T_actual as [ua ca].
    simpl in Hcore. subst ce.
    match goal with
    | Hequiv : ty_lifetime_equiv _ _ |- _ => inversion Hequiv; subst; try discriminate
    end.
    eapply IHHtyped; eauto; reflexivity.
Qed.

Lemma store_entry_typed_global_env_with_local_bounds :
  forall env bounds s entry ce,
    store_entry_typed env s entry ce ->
    store_entry_typed (global_env_with_local_bounds env bounds) s entry ce.
Proof.
  unfold store_entry_typed.
  intros env bounds s entry ce H.
  destruct entry as [sx sT sv sst], ce as [[[cx cT] cst] cm]; simpl in *.
  destruct H as (Hx & HT & Hst & Hv).
  repeat split; auto.
  eapply value_has_type_global_env_with_local_bounds. exact Hv.
Qed.

Lemma store_typed_global_env_with_local_bounds :
  forall env bounds s Σ,
    store_typed env s Σ ->
    store_typed (global_env_with_local_bounds env bounds) s Σ.
Proof.
  unfold store_typed.
  intros env bounds s Σ H.
  eapply Forall2_impl; [| exact H].
  intros entry ce Hentry.
  eapply store_entry_typed_global_env_with_local_bounds. exact Hentry.
Qed.

Lemma eval_global_env_with_local_bounds :
  forall env bounds s e s' v,
    eval env s e s' v ->
    eval (global_env_with_local_bounds env bounds) s e s' v
with eval_args_global_env_with_local_bounds :
  forall env bounds s args s' vs,
    eval_args env s args s' vs ->
    eval_args (global_env_with_local_bounds env bounds) s args s' vs
with eval_struct_fields_global_env_with_local_bounds :
  forall env bounds s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    eval_struct_fields (global_env_with_local_bounds env bounds)
      s fields defs s' values.
Proof.
  - intros env bounds s e s' v Heval.
    induction Heval;
      try solve
        [ econstructor; simpl in *; eauto;
          rewrite ?type_lookup_path_global_env_with_local_bounds; eauto ].
  - intros env bounds s args s' vs Hargs.
    induction Hargs; try solve [econstructor; eauto].
  - intros env bounds s fields defs s' values Hfields.
    induction Hfields; try solve [econstructor; eauto].
Qed.


Theorem eval_preserves_typing_ready_mutual_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
        preservation_ready_expr e ->
        store_typed env s Σ ->
        typed_env_structural env Ω n Σ e T Σ' ->
        store_typed env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
        preservation_ready_args args ->
        store_typed env s Σ ->
        typed_args_env_structural env Ω n Σ args ps Σ' ->
        store_typed env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
        preservation_ready_fields fields ->
        store_typed env s Σ ->
        typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
        store_typed env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n Σ T Σ' _ Hstore Htyped.
    dependent destruction Htyped.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction; eassumption.
    + destruct (eval_var_move_preserves_typing env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction; eassumption.
    + assert (Hmove_pair :
        store_typed env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
    IHfields Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : preservation_ready_fields ?fields0,
      Htyped_fields : typed_fields_env_structural env Ω n lts args
        Σ ?fields0 (struct_fields sdef) Σ' |- _ =>
        destruct (IHfields Ω n lts args Σ Σ'
                    Hready_fields Hstore Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s' enum_name variant_name lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IHargs Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Htyped_lookup : lookup_enum enum_name env = Some ?edef_typed |- _ =>
        rewrite Hlookup in Htyped_lookup;
        inversion Htyped_lookup; subst edef_typed
    end.
    match goal with
    | Htyped_variant :
        lookup_enum_variant variant_name (enum_variants edef) =
          Some ?vdef_typed |- _ =>
        rewrite Hvariant in Htyped_variant;
        inversion Htyped_variant; subst vdef_typed
    end.
    match goal with
    | Hready_args : preservation_ready_args payloads,
      Htyped_args : typed_args_env_structural env Ω n Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args)
            (enum_variant_fields vdef))) Σ' |- _ =>
        destruct (IHargs Ω n Σ
                    (params_of_tys
                      (map (instantiate_enum_variant_field_ty lts args)
                        (enum_variant_fields vdef))) Σ'
                    Hready_args Hstore Htyped_args)
          as [Hstore' [Hvalues Hpres_args]]
    end.
    repeat split.
    + exact Hstore'.
    + eapply VHT_Enum; eauto.
      eapply eval_args_values_have_types_params_of_tys_enum_values.
      exact Hvalues.
    + exact Hpres_args.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready.
  - intros s s' e v Heval IH Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e Σ' |- _ =>
        destruct (IH Ω n Σ T_e Σ' Hready_e Hstore Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s p x path rk Heval_place Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hstore0 : store_typed env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [T_eval [Hlookup [Hvalue [Htype_eval Heq_eval]]]]]];
          destruct (eval_borrow_shared_preserves_typing
                      env Ω n Σ0 s p T_place x path se v_target T_eval
                      Hstore0 Hplace Heval_place Hlookup Htype_eval
                      Heq_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hstore0 : store_typed env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [T_eval [Hlookup [Hvalue [Htype_eval Heq_eval]]]]]];
          destruct (eval_borrow_unique_preserves_typing
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target T_eval Hstore0 Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Heq_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s fname fdef Hlookup Hcaps Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n Σ T Σ'
      Hready _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_then : preservation_ready_expr e2,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHthen Ω n Σ1 T2 Σ2
                    Hready_then Hstore1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_else : preservation_ready_expr e3,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Htyped_else : typed_env_structural env Ω n ?Σ1 e3 ?T3 ?Σ3,
      Hcore : ty_core ?T2 = ty_core ?T3,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHelse Ω n Σ1 T3 Σ3
                    Hready_else Hstore1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq; eassumption);
        split;
	        [ eapply store_typed_ctx_merge_right; eassumption
	        | split;
	          [ eapply value_has_type_if_right_result; eassumption
	          | eapply store_ref_targets_preserved_trans; eassumption ] ]
	    end.
  - intros s s_scrut s_branch s' scrut branches enum_name variant_name
      lts_val args_val values edef_runtime vdef_runtime binders ps_payload
      e_branch v
      Heval_scrut IHscrut Hlookup_enum_runtime Hlookup_variant_runtime
      Hlookup_binders Hpayload_runtime Hvalues_len Hlookup_branch_eval
      Heval_branch IHbranch Hremove_params
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHscrut Ω n Σ _ _ ltac:(eassumption) Hstore ltac:(eassumption))
      as [Hstore_scrut [Hv_scrut Hpres_scrut]].
    assert (Hready_branch : preservation_ready_expr e_branch)
      by (eapply lookup_match_branch_preservation_ready; eassumption).
	    unfold lookup_match_branch in Hlookup_branch_eval.
	    match goal with
	    | Hscrut_core : ty_core ?T_scrut = TEnum ?enum_typed ?lts ?args,
	      Hlookup_typed : lookup_enum ?enum_typed env = Some ?edef_typed,
	      Hvariants : enum_variants ?edef_typed = ?v_head :: ?v_tail0 |- _ =>
        destruct (value_has_type_enum_variant_lookup env s_scrut enum_name variant_name
          lts_val args_val values T_scrut enum_typed lts args edef_typed
          Hv_scrut Hscrut_core Hlookup_typed)
          as [vdef_typed_runtime [Henum_name Hvariant_runtime]];
        subst enum_name;
        rewrite Hvariants in Hvariant_runtime;
        simpl in Hvariant_runtime;
        destruct (String.eqb variant_name (enum_variant_name v_head)) eqn:Hvariant_head
	    end.
    + apply String.eqb_eq in Hvariant_head. subst variant_name.
      assert (Hbranch_eq : e_branch = e_head).
      {
        match goal with
        | Hhead_lookup : lookup_expr_branch (enum_variant_name v_head) branches = Some e_head |- _ =>
            eapply lookup_expr_branch_deterministic;
            [ exact Hlookup_branch_eval | exact Hhead_lookup ]
        end.
	      }
	      subst e_branch.
	      assert (Hfields_runtime : enum_variant_fields vdef_runtime = []).
	      { assert (Hedef_same : edef_runtime = edef) by congruence.
	        subst edef_runtime.
	        rewrite H6 in Hlookup_variant_runtime. simpl in Hlookup_variant_runtime.
	        rewrite String.eqb_refl in Hlookup_variant_runtime.
	        inversion Hlookup_variant_runtime; subst. exact H7. }
	      assert (Hbinders_nil : binders = []).
	      { rewrite Hlookup_binders in H9. inversion H9. reflexivity. }
	      assert (Hpayload_nil : ps_payload = []).
	      { unfold match_payload_params_opt in Hpayload_runtime.
	        unfold TypingRules.match_payload_params_opt in Hpayload_runtime.
	        rewrite Hfields_runtime in Hpayload_runtime.
	        rewrite Hbinders_nil in Hpayload_runtime.
	        simpl in Hpayload_runtime. inversion Hpayload_runtime. reflexivity. }
	      assert (Hps_head_nil : ps_head = []).
	      { unfold match_payload_params in H10.
	        unfold instantiate_enum_variant_field_tys in H10.
	        rewrite H7 in H10. simpl in H10.
	        inversion H10. reflexivity. }
	      assert (Hvalues_nil : values = []).
	      { rewrite Hpayload_nil in Hvalues_len.
	        destruct values as [| value values']; simpl in Hvalues_len;
	          [reflexivity | discriminate]. }
	      assert (Hstore_payload :
	        store_typed env (bind_params ps_payload values s_scrut)
	          (sctx_add_params ps_head Σ1)).
	      { rewrite Hpayload_nil, Hps_head_nil, Hvalues_nil. simpl.
	        exact Hstore_scrut. }
	      destruct (IHbranch Ω n (sctx_add_params ps_head Σ1) T_head
	                Σ_head_payload Hready_branch Hstore_payload Htyped2)
	        as [Hstore_branch [Hv_branch Hpres_branch]].
	      split.
	      * subst s'. rewrite Hpayload_nil. simpl.
	        rewrite Hps_head_nil in H17. simpl in H17.
	        eapply store_typed_ctx_merge_many_left.
	        -- exact Hstore_branch.
	        -- exact H17.
	      * split.
	        -- rewrite Hremove_params, Hpayload_nil. simpl.
	           eapply value_has_type_match_head_result. exact Hv_branch.
	        -- rewrite Hremove_params, Hpayload_nil. simpl.
	           rewrite Hpayload_nil, Hvalues_nil in Hpres_branch. simpl in Hpres_branch.
	           eapply store_ref_targets_preserved_trans.
	           ++ exact Hpres_scrut.
	           ++ exact Hpres_branch.
	    + assert (Hvdef_runtime_tail : vdef_runtime = vdef_typed_runtime).
	      { assert (Hedef_same : edef_runtime = edef) by congruence.
	        subst edef_runtime.
	        rewrite H6 in Hlookup_variant_runtime. simpl in Hlookup_variant_runtime.
	        rewrite Hvariant_head in Hlookup_variant_runtime.
	        congruence. }
	      subst vdef_typed_runtime.
	      destruct (typed_match_tail_lookup env Ω n lts args Σ1 branches v_tail
		            (ty_core T_head) Σ_tail Ts_tail variant_name vdef_runtime e_branch
		            H16 Hvariant_runtime Hlookup_branch_eval)
	          as [T_branch [Σ_branch_payload [Σ_branch [ps_branch
	             [binders_branch Htail_branch]]]]];
	          destruct Htail_branch as [Hbinders_branch [Hparams_branch
	            [Htyped_branch [Hremove_branch [Hcore_branch [HinΣ HinT]]]]]].
	      destruct (typed_match_tail_lookup_no_payload env Ω n lts args Σ1
	          branches v_tail (ty_core T_head) Σ_tail Ts_tail
	          variant_name vdef_runtime binders_branch H16 Hvariant_runtime
	          Hbinders_branch) as [Hfields_runtime_tail Hbinders_branch_nil].
	      assert (Hbinders_nil : binders = []).
	      { rewrite Hbinders_branch_nil in Hbinders_branch.
	        rewrite Hlookup_binders in Hbinders_branch.
	        inversion Hbinders_branch. reflexivity. }
	      assert (Hpayload_nil : ps_payload = []).
	      { unfold match_payload_params_opt in Hpayload_runtime.
	        unfold TypingRules.match_payload_params_opt in Hpayload_runtime.
	        rewrite Hfields_runtime_tail in Hpayload_runtime.
	        rewrite Hbinders_nil in Hpayload_runtime.
	        simpl in Hpayload_runtime. inversion Hpayload_runtime. reflexivity. }
	      assert (Hps_branch_nil : ps_branch = []).
	      { unfold match_payload_params_opt in Hparams_branch.
	        unfold TypingRules.match_payload_params_opt in Hparams_branch.
	        rewrite Hfields_runtime_tail in Hparams_branch.
	        rewrite Hbinders_branch_nil in Hparams_branch.
	        simpl in Hparams_branch. inversion Hparams_branch. reflexivity. }
	      assert (Hvalues_nil : values = []).
	      { rewrite Hpayload_nil in Hvalues_len.
	        destruct values as [| value values']; simpl in Hvalues_len;
	          [reflexivity | discriminate]. }
	      assert (Hstore_payload :
	        store_typed env (bind_params ps_payload values s_scrut)
	          (sctx_add_params ps_branch Σ1)).
	      { rewrite Hpayload_nil, Hps_branch_nil, Hvalues_nil. simpl.
	        exact Hstore_scrut. }
	      destruct (IHbranch Ω n (sctx_add_params ps_branch Σ1) T_branch
	                  Σ_branch_payload Hready_branch Hstore_payload Htyped_branch)
	        as [Hstore_branch [Hv_branch Hpres_branch]].
	      assert (Hps_head_nil_tail : ps_head = []).
	      { unfold match_payload_params in H10.
	        unfold instantiate_enum_variant_field_tys in H10.
	        rewrite H7 in H10. simpl in H10.
	        inversion H10. reflexivity. }
	      pose (Σ_head := sctx_remove_params ps_head Σ_head_payload).
	      fold Σ_head in H17.
	      assert (Hsame_head_tail : Forall (sctx_same_bindings Σ_head) Σ_tail).
	      {
	        assert (Hsame_head : sctx_same_bindings Σ1 Σ_head).
	        { subst Σ_head. rewrite Hps_head_nil_tail. simpl.
	          pose proof Htyped2 as Htyped2_nil.
	          rewrite Hps_head_nil_tail in Htyped2_nil. simpl in Htyped2_nil.
	          eapply typed_env_structural_same_bindings. exact Htyped2_nil. }
        assert (Hsame_tail : Forall (sctx_same_bindings Σ1) Σ_tail)
          by (eapply typed_match_tail_env_structural_same_bindings; eassumption).
        eapply Forall_impl.
        - intros Σt Hsame_t.
          eapply sctx_same_bindings_trans.
          + apply sctx_same_bindings_sym. exact Hsame_head.
          + exact Hsame_t.
        - exact Hsame_tail.
      }
	      assert (Hsame_head_branch : sctx_same_bindings Σ_head Σ_branch).
	      {
	        assert (Hsame_head : sctx_same_bindings Σ1 Σ_head).
	        { subst Σ_head. rewrite Hps_head_nil_tail. simpl.
	          pose proof Htyped2 as Htyped2_nil.
	          rewrite Hps_head_nil_tail in Htyped2_nil. simpl in Htyped2_nil.
	          eapply typed_env_structural_same_bindings. exact Htyped2_nil. }
	        assert (Hsame_branch : sctx_same_bindings Σ1 Σ_branch).
	        { rewrite Hremove_branch, Hps_branch_nil. simpl.
	          pose proof Htyped_branch as Htyped_branch_nil.
	          rewrite Hps_branch_nil in Htyped_branch_nil.
	          simpl in Htyped_branch_nil.
	          eapply typed_env_structural_same_bindings.
	          exact Htyped_branch_nil. }
        eapply sctx_same_bindings_trans.
        - apply sctx_same_bindings_sym. exact Hsame_head.
        - exact Hsame_branch.
      }
	      split.
	      * rewrite Hremove_params, Hpayload_nil. simpl.
	        eapply store_typed_ctx_merge_many_selected.
	        -- rewrite Hremove_branch, Hps_branch_nil. simpl.
	           exact Hstore_branch.
        -- exact Hsame_head_branch.
        -- exact Hsame_head_tail.
        -- simpl. right. exact HinΣ.
        -- match goal with
           | Hmerge : ctx_merge_many (ctx_of_sctx Σ_head) (map ctx_of_sctx Σ_tail) = Some Γ_out |- _ =>
               exact Hmerge
           end.
	      * split.
	        -- rewrite Hremove_params, Hpayload_nil. simpl.
	           eapply value_has_type_match_tail_result.
	           ++ exact HinT.
	           ++ exact Hcore_branch.
	           ++ exact Hv_branch.
	        -- rewrite Hremove_params, Hpayload_nil. simpl.
	           rewrite Hpayload_nil, Hvalues_nil in Hpres_branch.
	           simpl in Hpres_branch.
	           eapply store_ref_targets_preserved_trans.
	           ++ exact Hpres_scrut.
	           ++ exact Hpres_branch.
		  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
		      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n Σ T Σ'
		      Hready _ _.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n Σ
	      T Σ' Hready _ _.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args fname captured fdef fcall vs ret
	      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s Ω n Σ ps Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n Σ ps Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Hready_rest : preservation_ready_args es,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_env_structural env Ω n ?Σ1 es ?ps_rest Σ' |- _ =>
        destruct (IHe Ω n Σ T_e Σ1 Hready_e Hstore Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (IHrest Ω n Σ1 ps_rest Σ' Hready_rest Hstore1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args Σ Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args Σ Σ' Hready Hstore Htyped.
    pose proof (preservation_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Hready; subst.
    simpl in Hlookup_expr; try discriminate.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_structural env Ω n Σ ?e_field ?T_field ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_env_structural env Ω n lts args
        ?Σ1 ?fields0 rest Σ' |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst;
        destruct (IHfield Ω n Σ T_field Σ1 Hready_field Hstore Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (IHrest Ω n lts args Σ1 Σ' Hready Hstore1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 Σ0 T0 Σ0'
      Hready Hstore Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 Σ0 ps0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 Σ0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

Theorem typed_fn_env_structural_big_step_safe_ready_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  forall env f s s' v,
    typed_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpres env f s s' v Htyped_fn Hready Hstore Heval.
  unfold typed_fn_env_structural in Htyped_fn.
  destruct Htyped_fn as
    (T_body & Γ_out & Htyped & Hcompat & _).
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env : store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env. eapply store_typed_global_env_with_local_bounds. exact Hstore. }
  assert (Heval_body_env : eval body_env s (fn_body f) s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  destruct (proj1 Hpres
      body_env s (fn_body f) s' v Heval_body_env
      (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out)
      Hready Hstore_body_env Htyped)
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - subst body_env.
    eapply value_has_type_clear_global_env_local_bounds. exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem checked_fn_env_structural_big_step_safe_ready_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  forall env f s s' v,
    checked_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpres env f s s' v Hchecked Hready Hstore Heval.
  eapply typed_fn_env_structural_big_step_safe_ready_with_preservation_core.
  - exact Hpres.
  - exact (proj1 Hchecked).
  - exact Hready.
  - exact Hstore.
  - exact Heval.
Qed.
