From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace
  TypeSafetyLocalFacts TypeSafetyRootNamed TypeSafetyBasePreservation
  TypeSafetyPrefixPreservation.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma typed_match_tail_roots_lookup :
  forall env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss name vdef e,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    lookup_enum_variant name variants = Some vdef ->
    lookup_expr_branch name branches = Some e ->
    exists T Σv_payload Rv_payload Σv Rv roots ps binders R_payload,
      R_payload = root_env_add_params_roots_same ps roots_scrut R /\
      params_names_nodup_b ps = true /\
      ctx_lookup_params_none_b ps Σ = true /\
      root_env_lookup_params_none_b ps R = true /\
      lookup_expr_branch_binders name branches = Some binders /\
      match_payload_params_opt binders lts args vdef = Some ps /\
      typed_env_roots env Ω n R_payload (sctx_add_params ps Σ) e T
        Σv_payload Rv_payload roots /\
      params_ok_sctx_b env ps Σv_payload = true /\
      EnvStructuralRules.roots_exclude_params ps roots /\
      Rv = root_env_remove_match_params ps Rv_payload /\
      EnvStructuralRules.root_env_excludes_params ps Rv /\
      Σv = sctx_remove_params ps Σv_payload /\
      ty_core T = expected_core /\
      root_env_equiv Rv R_out /\
      In Σv Σs /\
      In T Ts.
Proof.
  intros env Ω n lts args R roots_scrut Σ branches variants expected_core
    R_out Σs Ts rootss name vdef e Htail.
  induction Htail as
    [lts args R roots_scrut Σ branches expected_core R_out
    |R R_payload Rv_payload Rv Σ branches v rest e0 T
       Σv_payload Σv R_out roots Σs Ts rootss expected_core
       binders ps lts args roots_scrut
       Hbinders Hparams Hnodup Hctx_none Hroot_none Hlookup Hpayload
       Htyped Hparams_ok Hroots_excl Hremove Henv_excl Hctx_remove
       Hcore Hequiv Htail IHtail];
    intros Hvariant Hbranch.
  - simpl in Hvariant. discriminate.
  - simpl in Hvariant.
    destruct (String.eqb name (enum_variant_name v)) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name.
      rewrite Hlookup in Hbranch. inversion Hbranch; subst e.
      inversion Hvariant; subst vdef.
      exists T, Σv_payload, Rv_payload, Σv, Rv, roots, ps, binders, R_payload.
      repeat split; simpl; auto.
      eapply match_payload_params_opt_infer_ok. exact Hparams.
    + eapply IHtail in Hvariant; [| exact Hbranch].
      destruct Hvariant as
        [T' [Σpayload' [Rv_payload' [Σ' [Rv' [roots' [ps' Hrest]]]]]]].
      destruct Hrest as [binders' [Rpayload' Hrest]].
      destruct Hrest as [HRpayload' [Hnodup' [Hctx_none' [Hroot_none' [Hbinders'
        [Hparams' [Htyped' [Hparams_ok' [Hroots_excl' [Hremove'
        [Henv_excl' [Hctx_remove' [Hcore' [Hequiv'
        [HinΣ HinT]]]]]]]]]]]]]]].
      exists T', Σpayload', Rv_payload', Σ', Rv', roots', ps', binders',
        Rpayload'.
      repeat split; simpl; auto.
Qed.

Theorem eval_preserves_typing_roots_ready_mutual_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed env s' Σ' /\
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
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed env s' Σ' /\
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
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  assert (Htyping : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_typed env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_typed env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_typed env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction; eassumption.
    + destruct (eval_var_move_preserves_typing env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hstore _ _ _ Htyped.
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
      Ω n R Σ T Σ' R' roots Hready Hstore _ _ _ Htyped.
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
      IHfields Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : provenance_ready_fields ?fields0,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ ?fields0
        (struct_fields sdef) Σ' R' roots |- _ =>
        destruct (IHfields Ω n lts args R Σ Σ' R' roots
                    Hready_fields Hstore Hroots Hnodup Hrn Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s' enum_name variant_name lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IHargs Ω n R Σ T Σ' R' roots
      Hready Hstore Hroots Hnodup Hrn Htyped.
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
    | Hready_args : provenance_ready_args payloads,
      Htyped_args : typed_args_roots env Ω n R Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args)
            (enum_variant_fields vdef))) Σ' R' ?payload_roots |- _ =>
        destruct (IHargs Ω n R Σ
                    (params_of_tys
                      (map (instantiate_enum_variant_field_ty lts args)
                        (enum_variant_fields vdef))) Σ' R' payload_roots
                    Hready_args Hstore Hroots Hnodup Hrn Htyped_args)
          as [Hstore' [Hvalues Hpres_args]]
    end.
    repeat split.
    + exact Hstore'.
    + eapply VHT_Enum; eauto.
      eapply eval_args_values_have_types_params_of_tys_enum_values.
      exact Hvalues.
    + exact Hpres_args.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
        ?R1_body ?roots1_body,
      Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
      Hfresh : root_env_lookup x ?R1_body = None,
      Htyped2 : typed_env_roots env Ω n
        (root_env_add x ?roots1_body ?R1_body)
        (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
        ?R2_body ?roots2_body,
      Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
      Hexcl_roots : roots_exclude x ?roots2_body,
      Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
      Hready1 : provenance_ready_expr e1,
      Hready2 : provenance_ready_expr e2 |- _ =>
        let Hpres1 := fresh "Hpres1" in
        let Hpres2 := fresh "Hpres2" in
        assert (Hpres1 :
          store_typed env s Σ ->
          typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
          eval env s e1 s1 v1 ->
          store_typed env s1 Σ1_body /\
          value_has_type env s1 v1 T1_body /\
          store_ref_targets_preserved env s s1);
        [ intros Hstore0 _ Heval0;
          exact (IH1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hstore0 Hroots Hnodup Hrn Htyped1)
        | destruct (proj1 eval_preserves_roots_ready_mutual env s e1
            s1 v1 Heval1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hroots Hnodup Hrn Htyped1)
          as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]];
          assert (Hfresh_store : store_lookup x s1 = None)
            by (eapply store_roots_within_lookup_none; eassumption);
          assert (Hadd_roots :
            store_roots_within (root_env_add x roots1_body R1_body)
              (store_add x T_ann v1 s1))
            by (eapply store_add_roots_within; eassumption);
          assert (Hadd_nodup :
            store_no_shadow (store_add x T_ann v1 s1))
            by (apply store_no_shadow_add; assumption);
          assert (Hadd_rn :
            root_env_no_shadow (root_env_add x roots1_body R1_body))
            by (apply root_env_no_shadow_add; assumption);
          assert (Hpres2 :
            store_typed env (store_add x T_ann v1 s1)
              (sctx_add x T_ann m Σ1_body) ->
            typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
              e2 T2_body Σ2_body ->
            eval env (store_add x T_ann v1 s1) e2 s2 v2 ->
            store_typed env s2 Σ2_body /\
            value_has_type env s2 v2 T2_body /\
            store_ref_targets_preserved env
              (store_add x T_ann v1 s1) s2);
          [ intros Hstore0 _ Heval0;
            exact (IH2 Ω n (root_env_add x roots1_body R1_body)
              (sctx_add x T_ann m Σ1_body) T2_body Σ2_body R2_body
              roots2_body Hready2 Hstore0 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
          | eapply eval_let_roots_preserves_typing;
            eassumption ] ]
    end.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        destruct (IH Ω n R Σ T_e Σ' R' roots_e Hready_e
                    Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
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
      IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup
      Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
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
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
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
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
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
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [T_eval [Hlookup [Hvalue [Htype_eval Heq_eval]]]]]];
          destruct (eval_borrow_shared_preserves_typing
                      env Ω n Σ0 s p T_place x path se v_target T_eval
                      Hstore Hplace Heval_place Hlookup Htype_eval
                      Heq_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [T_eval [Hlookup [Hvalue [Htype_eval Heq_eval]]]]]];
          destruct (eval_borrow_unique_preserves_typing
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target T_eval Hstore Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Heq_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready Hstore Hroots
      Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Heval_r; subst.
    dependent destruction Htyped.
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H4 H2)
        as [Hx Hpath].
      subst x path.
      destruct (store_typed_lookup env s_r Σ x1 se Hstore Hlookup)
        as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_static [st_static [HΣstatic [_ Htype_path]]]].
      rewrite HΣstatic in HΣ.
      inversion HΣ; subst T_static st_static.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H5 H2)
        as [Hx Hpath].
      subst x path.
      destruct (store_typed_lookup env s_r Σ x1 se Hstore Hlookup)
        as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_static [st_static [HΣstatic [_ Htype_path]]]].
      rewrite HΣstatic in HΣ.
      inversion HΣ; subst T_static st_static.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
      Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool true) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2
                    Hready_then Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
      | Hready_cond : provenance_ready_expr e1,
        Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
        Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
        Hready_else : provenance_ready_expr e3,
        Htyped_else : typed_env_roots env Ω n ?R1 Σ1 e3 ?T3 ?Σ3 ?R3 ?roots3,
        Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool false) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3
                    Hready_else Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq;
            [ eapply typed_env_roots_structural; exact Htyped_then
            | eapply typed_env_roots_structural; exact Htyped_else ]);
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
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHscrut Ω n R Σ T_scrut Σ1 R1 roots_scrut
                Hready Hstore Hroots Hnodup Hrn Htyped1)
      as [Hstore_scrut [Hv_scrut Hpres_scrut]].
    destruct (proj1 eval_preserves_roots_ready_mutual env s scrut s_scrut
                (VEnum enum_name variant_name lts_val args_val values)
                Heval_scrut Ω n R Σ T_scrut Σ1 R1 roots_scrut Hready
                Hroots Hnodup Hrn Htyped1)
      as [Hroots_scrut [Hv_roots_scrut [Hnodup_scrut Hrn_scrut]]].
    assert (Hready_branch : provenance_ready_expr e_branch).
    { unfold lookup_match_branch in Hlookup_branch_eval.
      eapply provenance_ready_match_branches_lookup; eassumption. }
    unfold lookup_match_branch in Hlookup_branch_eval.
    assert (Hlookup_branch :
      lookup_expr_branch variant_name branches = Some e_branch).
    { rewrite lookup_expr_branch_lookup_expr_field. exact Hlookup_branch_eval. }
    destruct (value_has_type_enum_variant_lookup env s_scrut enum_name
                variant_name lts_val args_val values T_scrut enum_name0 lts
                args edef Hv_scrut H0 H1)
      as [vdef_typed_runtime [Henum_name Hvariant_runtime]].
    subst enum_name.
    rewrite H6 in Hvariant_runtime.
    simpl in Hvariant_runtime.
    destruct (String.eqb variant_name (enum_variant_name v_head))
      eqn:Hvariant_head.
    + apply String.eqb_eq in Hvariant_head. subst variant_name.
      assert (Hbranch_eq : e_branch = e_head).
      {
	        eapply lookup_expr_branch_deterministic;
	          [ exact Hlookup_branch | exact H12 ].
      }
      subst e_branch.
      assert (Hvdef_runtime_head : vdef_runtime = v_head).
      { assert (Hedef_same : edef_runtime = edef) by congruence.
        subst edef_runtime.
        rewrite H6 in Hlookup_variant_runtime. simpl in Hlookup_variant_runtime.
        rewrite String.eqb_refl in Hlookup_variant_runtime.
        inversion Hlookup_variant_runtime. reflexivity. }
      subst vdef_runtime.
      assert (Hbinders_same : binders_head = binders).
      { rewrite Hlookup_binders in H7. inversion H7. reflexivity. }
      assert (Hparams_head :
        match_payload_params_opt binders_head lts args v_head =
          Some ps_head).
      { eapply match_payload_params_opt_infer_ok. exact H8. }
      destruct (value_has_type_enum_args_lifetime_equiv env s_scrut enum_name0
                  (enum_variant_name v_head) lts_val args_val values
                  T_scrut enum_name0 lts args edef Hv_scrut H0 H1)
        as [_ Hargs_equiv].
      destruct (match_payload_params_opt_lifetime_equiv binders binders_head
                  lts_val lts args_val args v_head ps_payload ps_head
                  (eq_sym Hbinders_same) Hargs_equiv Hpayload_runtime
                  Hparams_head)
        as [Hnames_payload Htys_payload].
      assert (Hvalues_typed_head :
        enum_values_have_type env s_scrut values (map param_ty ps_head)).
      { rewrite (match_payload_params_opt_param_tys binders_head lts args
          v_head ps_head Hparams_head).
        eapply (value_has_type_enum_values_lookup env s_scrut enum_name0
          (enum_variant_name v_head) lts_val args_val values T_scrut
          enum_name0 lts args edef v_head).
        - exact Hv_scrut.
        - exact H0.
        - exact H1.
        - rewrite H6. simpl. rewrite String.eqb_refl. reflexivity. }
      pose proof (value_roots_within_enum_payloads roots_scrut enum_name0
        (enum_variant_name v_head) lts_val args_val values Hv_roots_scrut)
        as Hvalues_roots.
      assert (Hstore_payload :
        store_typed env (bind_params ps_payload values s_scrut)
          (sctx_add_params ps_head Σ1)).
      { eapply store_typed_bind_match_payload_params_lifetime.
        - exact Hstore_scrut.
        - exact H9.
        - exact H10.
        - exact Hvalues_typed_head.
        - exact Hnames_payload.
        - exact Htys_payload. }
      assert (Hroots_payload :
        store_roots_within
          (root_env_add_params_roots_same ps_head roots_scrut R1)
          (bind_params ps_payload values s_scrut)).
      { eapply store_roots_within_bind_params_roots_same_names.
        - exact Hnames_payload.
        - exact H9.
        - exact H11.
        - exact Hroots_scrut.
        - exact Hvalues_roots.
        - exact Hvalues_len. }
      assert (Hnodup_payload :
        store_no_shadow (bind_params ps_payload values s_scrut)).
      { eapply bind_params_store_no_shadow_names.
        - eapply params_names_nodup_b_sound.
          eapply (params_names_nodup_b_names ps_head ps_payload).
          + symmetry. exact Hnames_payload.
          + exact H9.
        - eapply store_roots_within_params_fresh_in_store.
          + eapply (root_env_lookup_params_none_b_names ps_head ps_payload).
            * symmetry. exact Hnames_payload.
            * exact H11.
          + exact Hroots_scrut.
        - exact Hvalues_len.
        - exact Hnodup_scrut. }
      assert (Hrn_payload :
        root_env_no_shadow
          (root_env_add_params_roots_same ps_head roots_scrut R1)).
      { eapply root_env_add_params_roots_same_no_shadow; eauto. }
      destruct (IHbranch Ω n
                  (root_env_add_params_roots_same ps_head roots_scrut R1)
                  (sctx_add_params ps_head Σ1)
                  T_head Σ_head_payload R_head_payload roots_head
                  Hready_branch Hstore_payload Hroots_payload Hnodup_payload
                  Hrn_payload Htyped2)
        as [Hstore_branch [Hv_branch Hpres_branch]].
      destruct (proj1 eval_preserves_roots_ready_mutual env
                  (bind_params ps_payload values s_scrut) e_head s_branch v
                  Heval_branch Ω n
                  (root_env_add_params_roots_same ps_head roots_scrut R1)
                  (sctx_add_params ps_head Σ1)
                  T_head Σ_head_payload R_head_payload roots_head
                  Hready_branch Hroots_payload Hnodup_payload Hrn_payload
                  Htyped2)
        as [Hroots_branch_store [Hv_roots_branch
             [Hnodup_branch_store Hrn_branch_store]]].
      assert (Hscope_payload_start :
        store_param_scope ps_payload
          (bind_params ps_payload values s_scrut) s_scrut).
      { eapply store_param_scope_bind_params_length. exact Hvalues_len. }
      assert (Hcover_payload :
        root_env_covers_params ps_payload
          (root_env_add_params_roots_same ps_head roots_scrut R1)).
      { eapply root_env_covers_params_add_params_roots_same_names.
        - exact Hnames_payload.
        - exact H9. }
      destruct (proj1 eval_preserves_param_scope_roots_ready_mutual env
                  (bind_params ps_payload values s_scrut) e_head s_branch v
                  Heval_branch Ω n
                  (root_env_add_params_roots_same ps_head roots_scrut R1)
                  (sctx_add_params ps_head Σ1)
                  T_head Σ_head_payload R_head_payload roots_head
                  ps_payload s_scrut Hready_branch Htyped2
                  Hcover_payload Hscope_payload_start)
        as [frame_branch Hscope_branch].
      destruct (store_remove_match_payload_cleanup_store_typed_names
                  ps_payload ps_head env s_branch frame_branch
                  (root_env_remove_match_params ps_head R_head_payload)
                  roots_head v T_head Σ_head_payload Hnames_payload
                  Hscope_branch)
        as [locals_branch [Hremoved_branch
             [Hv_removed [Hstore_refs_excl Hstore_removed]]]];
        [ eapply store_roots_within_remove_match_params_names;
          [ exact Hnames_payload
          | exact Hroots_branch_store
          | eapply params_names_nodup_b_sound; exact H9
          | exact Hnodup_branch_store ]
        | exact Hv_roots_branch
        | exact Hnodup_branch_store
        | exact H9
        | exact H15
        | exact H17
        | exact Hv_branch
        | exact Hstore_branch | ].
      split.
      * rewrite Hremove_params.
        eapply store_typed_ctx_merge_many_left.
        -- exact Hstore_removed.
        -- exact H20.
      * split.
        -- rewrite Hremove_params.
           eapply value_has_type_match_head_result. exact Hv_removed.
        -- rewrite Hremove_params.
           eapply store_ref_targets_preserved_trans.
           ++ exact Hpres_scrut.
           ++ eapply store_ref_targets_preserved_remove_params_after_absent.
              ** eapply store_ref_targets_preserved_trans.
                 --- eapply bind_params_ref_targets_preserved_fresh.
                     +++ eapply params_names_nodup_b_sound.
                         eapply (params_names_nodup_b_names
                           ps_head ps_payload).
                         *** symmetry. exact Hnames_payload.
                         *** exact H9.
                     +++ eapply store_roots_within_params_fresh_in_store.
                         *** eapply (root_env_lookup_params_none_b_names
                               ps_head ps_payload).
                             ---- symmetry. exact Hnames_payload.
                             ---- exact H11.
                         *** exact Hroots_scrut.
                 --- exact Hpres_branch.
              ** eapply store_roots_within_params_fresh_in_store.
                 --- eapply (root_env_lookup_params_none_b_names
                       ps_head ps_payload).
                     +++ symmetry. exact Hnames_payload.
                     +++ exact H11.
                 --- exact Hroots_scrut.
    + assert (Hvdef_runtime_tail : vdef_runtime = vdef_typed_runtime).
      { assert (Hedef_same : edef_runtime = edef) by congruence.
        subst edef_runtime.
        rewrite H6 in Hlookup_variant_runtime. simpl in Hlookup_variant_runtime.
        rewrite Hvariant_head in Hlookup_variant_runtime.
        congruence. }
      subst vdef_typed_runtime.
      destruct (typed_match_tail_roots_lookup env Ω n lts args R1
                  roots_scrut Σ1 branches v_tail
                  (ty_core T_head)
                  (root_env_remove_match_params ps_head R_head_payload)
                  Σ_tail Ts_tail roots_tail
                  variant_name vdef_runtime e_branch H19
                  Hvariant_runtime Hlookup_branch)
        as [T_branch [Σ_branch_payload [Rv_payload [Σ_branch [R_branch
             [roots_branch [ps_branch [binders_branch [R_payload Htail_branch]]]]]]]]].
      destruct Htail_branch as [HRpayload [Hnodup_branch_params
        [Hctx_none_branch [Hroot_none_branch [Hbinders_branch [Hparams_branch
        [Htyped_branch [Hparams_ok_branch [Hroots_excl_branch [Hremove_branch
        [Henv_excl_branch [Hctx_remove_branch [Hcore_branch
        [Hequiv_branch [HinΣ HinT]]]]]]]]]]]]]]].
      assert (Hbinders_same : binders_branch = binders).
      { rewrite Hlookup_binders in Hbinders_branch.
        inversion Hbinders_branch. reflexivity. }
      destruct (value_has_type_enum_args_lifetime_equiv env s_scrut enum_name0
                  variant_name lts_val args_val values T_scrut enum_name0
                  lts args edef Hv_scrut H0 H1)
        as [_ Hargs_equiv].
      destruct (match_payload_params_opt_lifetime_equiv binders binders_branch
                  lts_val lts args_val args vdef_runtime ps_payload ps_branch
                  (eq_sym Hbinders_same) Hargs_equiv Hpayload_runtime
                  Hparams_branch)
        as [Hnames_payload Htys_payload].
      assert (Hvalues_typed_branch :
        enum_values_have_type env s_scrut values (map param_ty ps_branch)).
      { rewrite (match_payload_params_opt_param_tys binders_branch lts args
          vdef_runtime ps_branch Hparams_branch).
        assert (Hvariant_runtime_full :
          lookup_enum_variant variant_name (enum_variants edef) =
            Some vdef_runtime).
        { rewrite H6. simpl. rewrite Hvariant_head. exact Hvariant_runtime. }
        eapply (value_has_type_enum_values_lookup env s_scrut enum_name0
          variant_name lts_val args_val values T_scrut enum_name0 lts args
          edef vdef_runtime).
        - exact Hv_scrut.
        - exact H0.
        - exact H1.
        - exact Hvariant_runtime_full. }
      pose proof (value_roots_within_enum_payloads roots_scrut enum_name0
        variant_name lts_val args_val values Hv_roots_scrut) as Hvalues_roots.
      assert (Hstore_payload :
        store_typed env (bind_params ps_payload values s_scrut)
          (sctx_add_params ps_branch Σ1)).
      { eapply store_typed_bind_match_payload_params_lifetime.
        - exact Hstore_scrut.
        - exact Hnodup_branch_params.
        - exact Hctx_none_branch.
        - exact Hvalues_typed_branch.
        - exact Hnames_payload.
        - exact Htys_payload. }
      assert (Hroots_payload :
        store_roots_within R_payload (bind_params ps_payload values s_scrut)).
      { subst R_payload.
        eapply store_roots_within_bind_params_roots_same_names.
        - exact Hnames_payload.
        - exact Hnodup_branch_params.
        - exact Hroot_none_branch.
        - exact Hroots_scrut.
        - exact Hvalues_roots.
        - exact Hvalues_len. }
      assert (Hnodup_payload :
        store_no_shadow (bind_params ps_payload values s_scrut)).
      { eapply bind_params_store_no_shadow_names.
        - eapply params_names_nodup_b_sound.
          eapply (params_names_nodup_b_names ps_branch ps_payload).
          + symmetry. exact Hnames_payload.
          + exact Hnodup_branch_params.
        - eapply store_roots_within_params_fresh_in_store.
          + eapply (root_env_lookup_params_none_b_names ps_branch ps_payload).
            * symmetry. exact Hnames_payload.
            * exact Hroot_none_branch.
          + exact Hroots_scrut.
        - exact Hvalues_len.
        - exact Hnodup_scrut. }
      assert (Hrn_payload : root_env_no_shadow R_payload).
      { subst R_payload.
        eapply root_env_add_params_roots_same_no_shadow; eauto. }
      destruct (IHbranch Ω n R_payload (sctx_add_params ps_branch Σ1)
                  T_branch Σ_branch_payload Rv_payload
                  roots_branch Hready_branch Hstore_payload Hroots_payload
                  Hnodup_payload Hrn_payload Htyped_branch)
        as [Hstore_branch [Hv_branch Hpres_branch]].
      destruct (proj1 eval_preserves_roots_ready_mutual env
                  (bind_params ps_payload values s_scrut) e_branch s_branch v
                  Heval_branch Ω n R_payload (sctx_add_params ps_branch Σ1)
                  T_branch Σ_branch_payload Rv_payload roots_branch
                  Hready_branch Hroots_payload Hnodup_payload Hrn_payload
                  Htyped_branch)
        as [Hroots_branch_store [Hv_roots_branch
             [Hnodup_branch_store Hrn_branch_store]]].
      assert (Hscope_payload_start :
        store_param_scope ps_payload
          (bind_params ps_payload values s_scrut) s_scrut).
      { eapply store_param_scope_bind_params_length. exact Hvalues_len. }
      assert (Hcover_payload : root_env_covers_params ps_payload R_payload).
      { subst R_payload.
        eapply root_env_covers_params_add_params_roots_same_names.
        - exact Hnames_payload.
        - exact Hnodup_branch_params. }
      destruct (proj1 eval_preserves_param_scope_roots_ready_mutual env
                  (bind_params ps_payload values s_scrut) e_branch s_branch v
                  Heval_branch Ω n R_payload (sctx_add_params ps_branch Σ1)
                  T_branch Σ_branch_payload Rv_payload roots_branch
                  ps_payload s_scrut Hready_branch Htyped_branch
                  Hcover_payload Hscope_payload_start)
        as [frame_branch Hscope_branch].
      destruct (store_remove_match_payload_cleanup_store_typed_names
                  ps_payload ps_branch env s_branch frame_branch R_branch
                  roots_branch v T_branch Σ_branch_payload Hnames_payload
                  Hscope_branch)
        as [locals_branch [Hremoved_branch
             [Hv_removed [Hstore_refs_excl Hstore_removed]]]];
        [ rewrite Hremove_branch;
          eapply store_roots_within_remove_match_params_names;
          [ exact Hnames_payload
          | exact Hroots_branch_store
          | eapply params_names_nodup_b_sound; exact Hnodup_branch_params
          | exact Hnodup_branch_store ]
        | exact Hv_roots_branch
        | exact Hnodup_branch_store
        | exact Hnodup_branch_params
        | exact Hroots_excl_branch
        | exact Henv_excl_branch
        | exact Hv_branch
        | exact Hstore_branch
        | rewrite <- Hctx_remove_branch in Hstore_removed ].
      pose (Σ_head := sctx_remove_params ps_head Σ_head_payload).
      fold Σ_head in H20.
      assert (Hsame_head_tail : Forall (sctx_same_bindings Σ_head) Σ_tail).
      {
        assert (Hsame_head : sctx_same_bindings Σ1 Σ_head).
        { subst Σ_head.
          eapply sctx_same_bindings_remove_added_params.
          eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped2. }
        assert (Hsame_tail : Forall (sctx_same_bindings Σ1) Σ_tail)
          by (eapply typed_match_tail_env_structural_same_bindings;
              eapply typed_match_tail_roots_structural; eassumption).
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
        { subst Σ_head.
          eapply sctx_same_bindings_remove_added_params.
          eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped2. }
        assert (Hsame_branch : sctx_same_bindings Σ1 Σ_branch).
        { rewrite Hctx_remove_branch.
          eapply sctx_same_bindings_remove_added_params.
          eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped_branch. }
        eapply sctx_same_bindings_trans.
        - apply sctx_same_bindings_sym. exact Hsame_head.
        - exact Hsame_branch.
      }
      split.
      * rewrite Hremove_params.
        eapply store_typed_ctx_merge_many_selected.
        -- exact Hstore_removed.
        -- exact Hsame_head_branch.
        -- exact Hsame_head_tail.
        -- simpl. right. exact HinΣ.
        -- exact H20.
      * split.
        -- rewrite Hremove_params.
           eapply value_has_type_match_tail_result.
           ++ exact HinT.
           ++ exact Hcore_branch.
           ++ exact Hv_removed.
        -- rewrite Hremove_params.
           eapply store_ref_targets_preserved_trans.
           ++ exact Hpres_scrut.
           ++ eapply store_ref_targets_preserved_remove_params_after_absent.
              ** eapply store_ref_targets_preserved_trans.
                 --- eapply bind_params_ref_targets_preserved_fresh.
                     +++ eapply params_names_nodup_b_sound.
                         eapply (params_names_nodup_b_names
                           ps_branch ps_payload).
                         *** symmetry. exact Hnames_payload.
                         *** exact Hnodup_branch_params.
                     +++ eapply store_roots_within_params_fresh_in_store.
                         *** eapply (root_env_lookup_params_none_b_names
                               ps_branch ps_payload).
                             ---- symmetry. exact Hnames_payload.
                             ---- exact Hroot_none_branch.
                         *** exact Hroots_scrut.
                 --- exact Hpres_branch.
              ** eapply store_roots_within_params_fresh_in_store.
                 --- eapply (root_env_lookup_params_none_b_names
                       ps_branch ps_payload).
                     +++ symmetry. exact Hnames_payload.
                     +++ exact Hroot_none_branch.
                 --- exact Hroots_scrut.
		  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
		      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
		      roots Hready _ _ _ _ _.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args0 vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ
	      T Σ' R' roots Hready _ _ _ _ _.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
	      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ ps Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ ps Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?ps_rest
        Σ' R' ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_e Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hroots Hnodup Hrn Htyped_e)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n R1 Σ1 ps_rest Σ' R' roots_rest
                    Hready_rest Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
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
  - intros s Ω n lts args R Σ Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args R Σ Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1
        ?R1 ?roots_field,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_roots env Ω n lts args ?R1 ?Σ1
        ?fields0 rest Σ' R' ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hstore Hroots Hnodup Hrn Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hroots Hnodup Hrn Htyped_field)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n lts args R1 Σ1 Σ' R' roots_rest
                    Hready Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
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
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
      Hready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 (Htyping env0) s0 e0 s0' v0 Heval
                Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hstore Hroots Hnodup Hrn Htyped)
      as [Hstore' [Hv Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual env0 s0 e0 s0' v0
                Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0'
        R0' roots0 Hready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 (Htyping env0)) s0 args0 s0' vs0 Heval
                  Ω0 n0 R0 Σ0 ps0 Σ0' R0' roots0
                  Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0' R0'
                  roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 Hready Hstore Hroots Hnodup Hrn
        Htyped.
      destruct (proj2 (proj2 (Htyping env0)) s0 fields0 defs0 s0'
                  values0 Heval Ω0 n0 lts0 args0 R0 Σ0 Σ0' R0'
                  roots0 Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 R0
                  Σ0 Σ0' R0' roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.
