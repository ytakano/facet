From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace
  TypeSafetyLocalFacts TypeSafetyRootNamed TypeSafetyBasePreservation.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_typed_prefix_ctx_merge_many_left :
  forall env s Σ tail Γ,
    store_typed_prefix env s Σ ->
    ctx_merge_many (ctx_of_sctx Σ) (map ctx_of_sctx tail) = Some Γ ->
    store_typed_prefix env s (sctx_of_ctx Γ).
Proof.
  intros env s Σ tail.
  revert Σ.
  induction tail as [|Σh rest IH]; intros Σ Γ Hstore Hmerge.
  - simpl in Hmerge. inversion Hmerge; subst. exact Hstore.
  - simpl in Hmerge.
    destruct (ctx_merge (ctx_of_sctx Σ) (ctx_of_sctx Σh)) as [Σm |] eqn:Hhead;
      try discriminate.
    eapply IH.
    + eapply store_typed_prefix_ctx_merge_left. exact Hstore. exact Hhead.
    + exact Hmerge.
Qed.

Lemma store_typed_prefix_ctx_merge_many_selected :
  forall env s Σ0 tail Γ Σsel,
    store_typed_prefix env s Σsel ->
    sctx_same_bindings Σ0 Σsel ->
    Forall (sctx_same_bindings Σ0) tail ->
    In Σsel (Σ0 :: tail) ->
    ctx_merge_many (ctx_of_sctx Σ0) (map ctx_of_sctx tail) = Some Γ ->
    store_typed_prefix env s (sctx_of_ctx Γ).
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
    + subst. eapply store_typed_prefix_ctx_merge_many_left.
      * eapply store_typed_prefix_ctx_merge_left.
        -- exact Hstore.
        -- exact Hhead.
      * exact Hmerge.
    + subst. eapply store_typed_prefix_ctx_merge_many_left.
      * eapply store_typed_prefix_ctx_merge_right.
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

Lemma store_typed_prefix_bind_params_same_ctx :
  forall env Ω s Σ values ps_store ps_ctx,
    store_typed_prefix env s Σ ->
    NoDup (ctx_names (params_ctx ps_store)) ->
    params_fresh_in_store ps_store s ->
    eval_args_values_have_types env Ω s values ps_ctx ->
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_ctx) ->
    map param_ty ps_store = map param_ty ps_ctx ->
    store_typed_prefix env (bind_params ps_store values s)
      (sctx_add_params ps_ctx Σ).
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
    assert (Hnodup_head : NoDup (ctx_names (params_ctx (p :: ps_store)))).
    { simpl in *. rewrite <- Hname_eq. exact Hnodup. }
    assert (Hfresh_head : params_fresh_in_store (p :: ps_store) s).
    { unfold params_fresh_in_store in *.
      intros x Hin. simpl in Hin. rewrite <- Hname_eq in Hin.
      eapply Hfresh. exact Hin. }
    assert (Hargs_store_tail :
      eval_args_values_have_types env Ω s values ps_store).
    { eapply eval_args_values_have_types_param_tys.
      - exact Hargs.
      - exact Htys_tail. }
    simpl.
    rewrite Hname_eq, Hty_eq.
    eapply store_typed_prefix_add_compatible.
    + eapply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
      * exact Hnames_tail.
      * exact Htys_tail.
    + eapply value_has_type_store_preserved.
      * exact Hv.
      * eapply bind_params_ref_targets_preserved.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
        -- exact Hargs_store_tail.
    + exact Hcompat.
    + eapply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail.
      * exact Hnodup_head.
      * exact Hfresh_head.
      * exact Hargs_store_tail.
Qed.

Lemma store_typed_prefix_bind_match_payload_params :
  forall env (Ω : outlives_ctx) s Σ values ps_runtime ps_typed,
    store_typed_prefix env s Σ ->
    params_names_nodup_b ps_typed = true ->
    ctx_lookup_params_none_b ps_typed Σ = true ->
    params_fresh_in_store ps_runtime s ->
    enum_values_have_type env s values (map param_ty ps_typed) ->
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    map param_ty ps_runtime = map param_ty ps_typed ->
    store_typed_prefix env (bind_params ps_runtime values s)
      (sctx_add_params ps_typed Σ).
Proof.
  intros env Ω s Σ values ps_runtime ps_typed Hstore Hnodup _ Hfresh
    Hvalues Hnames Htys.
  eapply store_typed_prefix_bind_params_same_ctx with (Ω := Ω).
  - exact Hstore.
  - rewrite Hnames.
    eapply params_names_nodup_b_sound. exact Hnodup.
  - exact Hfresh.
  - eapply enum_values_have_type_eval_args_values.
    + exact Hvalues.
    + reflexivity.
  - exact Hnames.
  - exact Htys.
Qed.

Lemma store_typed_prefix_add_lifetime :
  forall env s Σ x T_store T_ctx m v,
    store_typed_prefix env s Σ ->
    value_has_type env s v T_store ->
    ty_lifetime_equiv T_store T_ctx ->
    store_ref_targets_preserved env s (store_add x T_store v s) ->
    store_typed_prefix env (store_add x T_store v s) (sctx_add x T_ctx m Σ).
Proof.
  intros env s Σ x T_store T_ctx m v Htyped Hv Heq Hpres.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  unfold store_typed_prefix, store_add, sctx_add.
  exists (MkStoreEntry x T_store v (binding_state_of_bool false) :: entries),
    frame.
  split.
  - simpl. subst s. reflexivity.
  - constructor.
    + simpl.
      repeat split; try reflexivity.
      * exact Heq.
      * eapply value_has_type_store_preserved; eassumption.
    + eapply store_typed_store_param_preserved; eassumption.
Qed.

Lemma store_typed_prefix_bind_match_payload_params_lifetime_aux :
  forall env s Σ values ps_runtime ps_typed,
    store_typed_prefix env s Σ ->
    enum_values_have_type env s values (map param_ty ps_typed) ->
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    Forall2 ty_lifetime_equiv
      (map param_ty ps_runtime) (map param_ty ps_typed) ->
    NoDup (ctx_names (params_ctx ps_runtime)) ->
    params_fresh_in_store ps_runtime s ->
    store_typed_prefix env (bind_params ps_runtime values s)
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
    rewrite Hname_eq.
    eapply store_typed_prefix_add_lifetime.
    + eapply IH.
      * exact H4.
      * exact Hnames_tail.
      * exact Htys_equiv.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + eapply value_has_type_store_preserved.
      * eapply VHT_LifetimeEquiv.
        -- exact H2.
        -- apply ty_lifetime_equiv_sym. exact Hty_equiv.
      * eapply bind_params_ref_targets_preserved_fresh.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
    + exact Hty_equiv.
    + eapply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      rewrite <- Hname_eq.
      eapply bind_params_head_fresh_in_tail_any; eassumption.
Qed.

Lemma store_typed_prefix_bind_match_payload_params_lifetime :
  forall env s Σ values ps_runtime ps_typed,
    store_typed_prefix env s Σ ->
    params_names_nodup_b ps_typed = true ->
    params_fresh_in_store ps_runtime s ->
    enum_values_have_type env s values (map param_ty ps_typed) ->
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    Forall2 ty_lifetime_equiv
      (map param_ty ps_runtime) (map param_ty ps_typed) ->
    store_typed_prefix env (bind_params ps_runtime values s)
      (sctx_add_params ps_typed Σ).
Proof.
  intros env s Σ values ps_runtime ps_typed Hstore Hnodup Hfresh Hvalues
    Hnames Hequiv.
  eapply store_typed_prefix_bind_match_payload_params_lifetime_aux.
  - exact Hstore.
  - exact Hvalues.
  - exact Hnames.
  - exact Hequiv.
  - rewrite Hnames.
    eapply params_names_nodup_b_sound. exact Hnodup.
  - exact Hfresh.
Qed.

Theorem eval_preserves_typing_ready_prefix_mutual_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
        preservation_ready_expr e ->
        store_typed_prefix env s Σ ->
        typed_env_structural env Ω n Σ e T Σ' ->
        store_typed_prefix env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
        preservation_ready_args args ->
        store_typed_prefix env s Σ ->
        typed_args_env_structural env Ω n Σ args ps Σ' ->
        store_typed_prefix env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
        preservation_ready_fields fields ->
        store_typed_prefix env s Σ ->
        typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
        store_typed_prefix env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
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
    + destruct (eval_var_copy_preserves_typing_prefix env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction_prefix; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction_prefix; eassumption.
    + destruct (eval_var_move_preserves_typing_prefix env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing_prefix
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction_prefix; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction_prefix; eassumption.
    + assert (Hmove_pair :
        store_typed_prefix env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing_prefix; eassumption. }
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
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing_prefix
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
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing_prefix
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
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing_prefix
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
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing_prefix
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
      | Hstore0 : store_typed_prefix env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [T_eval [Hlookup [Hvalue [Htype_eval Heq_eval]]]]]];
          destruct (eval_borrow_shared_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x path se v_target T_eval
                      Hstore0 Hplace Heval_place Hlookup Htype_eval
                      Heq_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hstore0 : store_typed_prefix env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [T_eval [Hlookup [Hvalue [Htype_eval Heq_eval]]]]]];
          destruct (eval_borrow_unique_preserves_typing_prefix
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
    inversion Hready; subst.
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
        [ eapply store_typed_prefix_ctx_merge_left; eassumption
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
        [ eapply store_typed_prefix_ctx_merge_right; eassumption
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
      assert (Hbinders_head_nil : binders_head = []).
      { eapply lookup_expr_branch_binders_preservation_ready_empty;
          eassumption. }
      assert (Hbinders_nil : binders = []).
      { eapply lookup_expr_branch_binders_preservation_ready_empty;
          eassumption. }
      assert (Hpayload_nil : ps_payload = []).
      { unfold match_payload_params_opt in Hpayload_runtime.
        unfold TypingRules.match_payload_params_opt in Hpayload_runtime.
        rewrite Hbinders_nil in Hpayload_runtime.
        destruct (enum_variant_fields vdef_runtime) as [| field fields];
          simpl in Hpayload_runtime; try discriminate.
        inversion Hpayload_runtime. reflexivity. }
      assert (Hps_head_nil : ps_head = []).
      { unfold match_payload_params in H8.
        unfold instantiate_enum_variant_field_tys in H8.
        rewrite Hbinders_head_nil in H8.
        destruct (map (instantiate_enum_variant_field_ty lts args)
          (enum_variant_fields v_head)) as [| field fields];
          try discriminate.
        inversion H8. reflexivity. }
      assert (Hvalues_nil : values = []).
      { rewrite Hpayload_nil in Hvalues_len.
        destruct values as [| value values']; simpl in Hvalues_len;
          [reflexivity | discriminate]. }
      assert (Hstore_payload :
        store_typed_prefix env (bind_params ps_payload values s_scrut)
          (sctx_add_params ps_head Σ1)).
      { rewrite Hpayload_nil, Hps_head_nil, Hvalues_nil. simpl.
        exact Hstore_scrut. }
      destruct (IHbranch Ω n (sctx_add_params ps_head Σ1) T_head
                Σ_head_payload Hready_branch Hstore_payload Htyped2)
        as [Hstore_branch [Hv_branch Hpres_branch]].
      split.
      * subst s'. rewrite Hpayload_nil. simpl.
        rewrite Hps_head_nil in H15. simpl in H15.
        eapply store_typed_prefix_ctx_merge_many_left.
        -- exact Hstore_branch.
        -- exact H15.
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
                H14 Hvariant_runtime Hlookup_branch_eval)
        as [T_branch [Σ_branch_payload [Σ_branch [ps_branch
          [binders_branch Htail_branch]]]]];
      destruct Htail_branch as [Hbinders_branch Htail_branch].
      destruct Htail_branch as [Hparams_branch Htail_branch].
      destruct Htail_branch as [Hnodup_branch_params Htail_branch].
      destruct Htail_branch as [Hctx_none_branch Htail_branch].
      destruct Htail_branch as [Htyped_branch Htail_branch].
      destruct Htail_branch as [Hparams_ok_branch Htail_branch].
      destruct Htail_branch as [Hremove_branch Htail_branch].
      destruct Htail_branch as [Hcore_branch Htail_branch].
      destruct Htail_branch as [HinΣ HinT].
      pose proof (typed_match_tail_lookup_no_payload env Ω n lts args Σ1
        branches v_tail (ty_core T_head) Σ_tail Ts_tail
        variant_name vdef_runtime binders_branch
        ltac:(match goal with
          | Hready_branches : preservation_ready_match_branches branches |- _ =>
              exact Hready_branches
          end)
        H14 Hvariant_runtime Hbinders_branch) as Hbinders_branch_nil.
      assert (Hbinders_nil : binders = []).
      { rewrite Hbinders_branch_nil in Hbinders_branch.
        rewrite Hlookup_binders in Hbinders_branch.
        inversion Hbinders_branch. reflexivity. }
      assert (Hpayload_nil : ps_payload = []).
      { unfold match_payload_params_opt in Hpayload_runtime.
        unfold TypingRules.match_payload_params_opt in Hpayload_runtime.
        rewrite Hbinders_nil in Hpayload_runtime.
        destruct (enum_variant_fields vdef_runtime) as [| field fields];
          simpl in Hpayload_runtime; try discriminate.
        inversion Hpayload_runtime. reflexivity. }
      assert (Hps_branch_nil : ps_branch = []).
      { unfold match_payload_params_opt in Hparams_branch.
        unfold TypingRules.match_payload_params_opt in Hparams_branch.
        rewrite Hbinders_branch_nil in Hparams_branch.
        destruct (enum_variant_fields vdef_runtime) as [| field fields];
          simpl in Hparams_branch; try discriminate.
        inversion Hparams_branch. reflexivity. }
      assert (Hvalues_nil : values = []).
      { rewrite Hpayload_nil in Hvalues_len.
        destruct values as [| value values']; simpl in Hvalues_len;
          [reflexivity | discriminate]. }
      assert (Hstore_payload :
        store_typed_prefix env (bind_params ps_payload values s_scrut)
          (sctx_add_params ps_branch Σ1)).
      { rewrite Hpayload_nil, Hps_branch_nil, Hvalues_nil. simpl.
        exact Hstore_scrut. }
      destruct (IHbranch Ω n (sctx_add_params ps_branch Σ1) T_branch
                  Σ_branch_payload Hready_branch Hstore_payload Htyped_branch)
        as [Hstore_branch [Hv_branch Hpres_branch]].
      assert (Hbinders_head_nil_tail : binders_head = []).
      { eapply lookup_expr_branch_binders_preservation_ready_empty;
          eassumption. }
      assert (Hps_head_nil_tail : ps_head = []).
      { unfold match_payload_params in H8.
        unfold instantiate_enum_variant_field_tys in H8.
        rewrite Hbinders_head_nil_tail in H8.
        destruct (map (instantiate_enum_variant_field_ty lts args)
          (enum_variant_fields v_head)) as [| field fields];
          try discriminate.
        inversion H8. reflexivity. }
      pose (Σ_head := sctx_remove_params ps_head Σ_head_payload).
      fold Σ_head in H15.
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
        eapply store_typed_prefix_ctx_merge_many_selected.
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
