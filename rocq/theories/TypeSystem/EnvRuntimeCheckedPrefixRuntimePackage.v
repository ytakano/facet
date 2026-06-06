From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeDirectCallStoreSafeFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma value_roots_within_nil_weaken :
  forall roots v,
    value_roots_within [] v ->
    value_roots_within roots v.
Proof.
  intros roots v Hwithin.
  eapply value_roots_within_store_subset.
  - exact Hwithin.
  - unfold root_set_stores_subset. intros z Hin. inversion Hin.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_checked_runtime_package :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary_checked
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed env s' Σ' /\
      value_has_type env s' ret T /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Heval Hunique.
  - eapply expr_root_shadow_store_safe_narrow_summary_runtime_package;
      eassumption.
  - destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package
      env Omega n R Σ e T Σ' R' roots ret_roots H s s' ret
      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store Heval Hunique)
      as [Hstore' [Hv [Hroots' [_ [_ [Hshadow' [Hrn' [Hnamed' [Hkeys'
        Hsummary']]]]]]]]].
    repeat split; try eassumption.
    + eapply value_has_type_runtime_rootless_empty_roots.
      * exact Hv.
      * eapply capture_ref_free_ty_b_runtime_rootless. exact H0.
    + apply root_set_store_roots_named_nil.
  - inversion Heval; subst.
    + match goal with
      | Hplace : expr_as_place (EBorrow RShared p) = Some _ |- _ =>
          simpl in Hplace; discriminate
      end.
    + match goal with
      | Hborrow : eval env s (EBorrow RShared p) _ _ |- _ =>
          inversion Hborrow; subst; clear Hborrow
      end.
      inversion H; subst; try congruence;
        try solve [
          match goal with
          | Hplace_eval : eval_place ?st_eval _ _ _,
            Hvalue_eval : value_lookup_path _ _ = Some ret |- _ =>
              assert (Hv_target : value_has_type env st_eval ret T) by
                (eapply eval_place_runtime_target_value_has_type; eassumption);
              repeat split; try eassumption;
              [ eapply value_has_type_runtime_rootless_empty_roots;
                [ exact Hv_target
                | eapply capture_ref_free_ty_b_runtime_rootless; exact H0 ]
              | apply root_set_store_roots_named_nil ]
          end ].
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EStruct name lts args []) T Σ' R' roots H)
      as Htyped_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s (EStruct name lts args []) s' ret Heval
      Omega n R Σ T Σ' R' roots
      (ProvReady_Struct name lts args [] ProvReadyFields_Nil)
      Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    destruct (proj1 eval_preserves_root_names_ready_mutual
      env s (EStruct name lts args []) s' ret Heval
      Omega n R Σ T Σ' R' roots
      (ProvReady_Struct name lts args [] ProvReadyFields_Nil)
      Hstore Hroots Hshadow Hrn Hnamed Htyped_roots) as [Hnamed' _].
    pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
      env s (EStruct name lts args []) s' ret Heval
      Omega n R Σ T Σ' R' roots
      (ProvReady_Struct name lts args [] ProvReadyFields_Nil)
      Hstore Hroots Hshadow Hrn Hkeys Htyped_roots) as Hkeys'.
    assert (Hs_eq : s' = s).
    { inversion Heval; subst.
      eapply eval_struct_fields_empty_exprs_store_eq; eassumption. }
    subst s'.
    repeat split; try eassumption;
      try apply root_set_store_roots_named_nil;
      try (eapply value_has_type_runtime_rootless_empty_roots;
        [ exact Hv
        | eapply capture_ref_free_ty_b_runtime_rootless; exact H0 ]);
      try (eapply store_typed_function_closure_targets_summary; eassumption).
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]].
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_roots_named_add_env_store_add; eassumption).
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H6.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hremain_names :
      forall z,
        In z (store_names s2) ->
        z <> x ->
        In z (store_names (store_remove x s2)))
      by (intros z Hin Hneq; apply store_names_remove_keeps_other; assumption).
    assert (Hnamed_removed :
      root_env_store_roots_named (root_env_remove x R2) s2).
    { eapply root_env_store_roots_named_remove_env; eassumption. }
    assert (Hnamed_final :
      root_env_store_roots_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_roots_named_store_remove_excluding.
      - intros y roots Hlookup.
        apply H6 with (y := y) (roots := roots); [exact Hlookup|].
        intros Heq. subst y.
        rewrite root_env_lookup_remove_eq_no_shadow in Hlookup by exact Hrn2.
        discriminate.
      - exact Hnamed_removed.
      - exact Hremain_names. }
    assert (Hkeys_final :
      root_env_store_keys_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_keys_named_remove_env_store_remove; eassumption. }
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_runtime_rootless_store_any.
      * exact Hv2.
      * eapply capture_ref_free_ty_b_runtime_rootless. exact H4.
    + exact Hroots_removed.
    + eapply value_has_type_runtime_rootless_empty_roots.
      * exact Hv2.
      * eapply capture_ref_free_ty_b_runtime_rootless. exact H4.
    + apply root_set_store_roots_named_nil.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hroots1_runtime [Hv1_roots_empty [_
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]].
    assert (Hv1_roots : value_roots_within roots1 v1)
      by (eapply value_roots_within_nil_weaken; exact Hv1_roots_empty).
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H1. }
    assert (Hstore_add :
      store_typed env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H1.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hctx_roots : root_env_ctx_roots_named R Σ)
      by (eapply root_env_store_roots_named_to_ctx; eassumption).
    assert (Hroots1_ctx : root_set_ctx_roots_named roots1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega n)
        as [Htyped_named _].
      destruct (Htyped_named R Σ e1 T1 Σ1 R1 roots1 H Hrn Hctx_roots)
        as [_ Hroots_ctx].
      exact Hroots_ctx. }
    assert (Hroots1_named_store : root_set_store_roots_named roots1 s1).
    { eapply root_set_ctx_roots_named_store_typed; eassumption. }
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_roots_named_add_env_store_add; eassumption. }
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H8.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hremain_names :
      forall z, In z (store_names s2) -> z <> x ->
        In z (store_names (store_remove x s2)))
      by (intros z Hin Hneq; apply store_names_remove_keeps_other; assumption).
    assert (Hnamed_removed :
      root_env_store_roots_named (root_env_remove x R2) s2).
    { eapply root_env_store_roots_named_remove_env; eassumption. }
    assert (Hnamed_final :
      root_env_store_roots_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_roots_named_store_remove_excluding.
      - intros y roots Hlookup.
        apply H8 with (y := y) (roots := roots); [exact Hlookup|].
        intros Heq. subst y.
        rewrite root_env_lookup_remove_eq_no_shadow in Hlookup by exact Hrn2.
        discriminate.
      - exact Hnamed_removed.
      - exact Hremain_names. }
    assert (Hkeys_final :
      root_env_store_keys_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_keys_named_remove_env_store_remove; eassumption. }
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_runtime_rootless_store_any.
      * exact Hv2.
      * eapply capture_ref_free_ty_b_runtime_rootless. exact H6.
    + exact Hroots_removed.
    + eapply value_has_type_runtime_rootless_empty_roots.
      * exact Hv2.
      * eapply capture_ref_free_ty_b_runtime_rootless. exact H6.
    + apply root_set_store_roots_named_nil.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
  - dependent destruction Heval.

Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_ctx :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
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
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret T /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hctx_roots Hctx_keys Hsummary_store Heval Hunique.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package_prefix_start;
        eassumption.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package_prefix_start;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    dependent destruction H6.
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
    | Hbody_eval : eval env
        (bind_params (apply_type_params type_args (fn_params fcall)) vs
          (captured ++ s_args))
        (subst_type_params_expr type_args (fn_body fcall)) s_body ret |- _ =>
        rename Hbody_eval into Heval_body
    end.
    match goal with
    | Htyped_callee_call : typed_env_roots_shadow_safe _ _ _ _ _
        (EVar x) (MkTy _ (TTypeForall _ _ _)) _ _ _ |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          _ _ _ _ H3 Htyped_callee_call) as Hcore
    end.
    assert (Harity_call : Datatypes.length type_args = type_params).
    { eapply H5. rewrite Hcore. reflexivity. }
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 H6) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x)
      Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
    destruct (typed_env_roots_shadow_safe_evar_store_named
      env Omega n R Σ x (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 s H6 Hnamed Hkeys)
      as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
    pose proof (proj1 preservation_ready_eval_store_names_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      (PRE_Var x)) as Hcallee_names.
    assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
    { eapply root_env_store_roots_named_store_names_eq; eassumption. }
    assert (Hcallee_roots_named_fn :
        root_set_store_roots_named roots_callee0 s_fn).
    { eapply root_set_store_roots_named_store_names_eq; eassumption. }
    assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
    { eapply root_env_store_keys_named_store_names_eq; eassumption. }
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TTypeForall type_params bounds body_ty)) Hv_callee)
      as Hcaptured_nil.
    subst captured.
    simpl in Hrename, Heval_body.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary_store Heval_callee Hlookup)
      as Hcallee_summary.
    pose proof (store_function_closure_targets_summary_eval_var
      env s s_fn x (VClosure fname []) Hsummary_store Heval_callee)
      as Hsummary_fn.
    pose proof (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
      env args s_fn s_args vs H Hsummary_fn Heval_args) as Hsummary_args.
    destruct (value_has_type_empty_closure_ttypeforall_tfn_components_closed
      env s_fn fname fdef u type_params bounds body_ty param_tys ret_inner
      type_args H0 Hv_callee Hlookup Hunique H7)
      as [Htype_params [Hlifetimes [Hcaps_fdef Hbridge]]].
    assert (Harity_fdef : Datatypes.length type_args = fn_type_params fdef).
    { rewrite Htype_params. exact Harity_call. }
    pose proof (lookup_fn_in fname (env_fns env) fdef Hlookup) as Hin_fdef.
    pose proof
      (check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound
        inst_fuel env type_args H2 fdef Hin_fdef Harity_fdef)
      as Hnarrow_fdef.
    pose proof (typed_args_roots_shadow_safe_roots
      env Omega n R1 Σ1 args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots H9) as Htyped_args_roots.
    pose proof (preservation_ready_args_implies_provenance_ready_closure
      args (store_safe_function_value_call_args_preservation_ready env args H))
      as Hprov_args.
    assert (Hcallee_route :
        callee_body_root_shadow_provenance_ready_at_result_subset env
          (fn_subst_type_params type_args fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R')
          (root_sets_union arg_roots)).
    { eapply (generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_instantiated_narrow_tfn_with_result_subset_prefix_named
        env Omega n R1 Σ1 Σ' R' arg_roots args type_args fdef fcall
        (map (subst_type_params_ty type_args) param_tys)
        (subst_type_params_ty type_args ret_inner) s_fn s_args vs used').
      - exact Hcallee_summary.
      - exact Hnarrow_fdef.
      - exact Hcaps_fdef.
      - exact Hbridge.
      - exact H.
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
    destruct (eval_call_expr_generic_ttypeforall_tfn_components_preserve_typing_with_callee_summary_route_prefix_start
      env s s_fn s_args s_body (EVar x) type_args args fname [] fdef fcall vs ret used'
      Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      type_params bounds body_ty param_tys ret_inner
      H0 (store_safe_function_value_call_args_preservation_ready env args H)
      (ProvReady_Var x)
      Hstore
      Hroots Hshadow Hrn H6 H7 H9 Hunique Hcallee_route)
      as [Hstore_prefix' [Hv [Hpres' [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    pose proof (eval_call_expr_generic_ttypeforall_tfn_components_final_store_eq_route_prefix_start
      env s s_fn s_args s_body (EVar x) type_args args fname [] fdef fcall vs ret used'
      Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      type_params bounds body_ty param_tys ret_inner
      H0 (store_safe_function_value_call_args_preservation_ready env args H)
      (ProvReady_Var x)
      Hstore
      Hroots Hshadow Hrn H6 H7 H9 Hunique Hcallee_route) as Heq_final.
    destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
      env s_fn args s_args vs Heval_args Omega n R1 Σ1
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots Hprov_args Hstore_fn Hroots_fn Hshadow_fn Hrn_fn
      Htyped_args_roots) as [Hstore_args _].
    destruct (store_safe_function_value_call_args_typed_roots_store_named
      env Omega n R1 Σ1 args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots s_fn s_args vs H Htyped_args_roots Heval_args
      Hnamed_fn Hkeys_fn) as [Hnamed_args [Harg_roots_named Hkeys_args]].
    assert (Hcallee_roots_named_args :
        root_set_store_roots_named roots_callee0 s_args).
    { pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
        env s_fn args s_args vs Heval_args
        (store_safe_function_value_call_args_preservation_ready env args H))
        as Hargs_names.
      eapply root_set_store_roots_named_store_names_eq; eassumption. }
    assert (Hrootset_named_args :
        root_set_store_roots_named
          (root_set_union roots_callee0 (root_sets_union arg_roots)) s_args).
    { apply root_set_store_roots_named_union.
      - exact Hcallee_roots_named_args.
      - apply root_sets_store_roots_named_union. exact Harg_roots_named. }
    rewrite <- Heq_final in Hsummary_args.
    repeat split.
    + rewrite Heq_final. exact Hstore_args.
    + exact Hv.
    + exact Hroots'.
    + exact Hvroots.
    + rewrite Heq_final. exact Hrootset_named_args.
    + exact Hshadow'.
    + exact Hrn'.
    + rewrite Heq_final. exact Hnamed_args.
    + rewrite Heq_final. exact Hkeys_args.
    + exact Hsummary_args.
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hctx_roots Hctx_keys Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]].
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_roots_named_add_env_store_add; eassumption).
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    pose proof (expr_root_shadow_store_safe_narrow_summary_typed
      env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 Hsummary1)
      as Htyped_shadow1.
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ e1 T1 Σ1 R1 roots1 Htyped_shadow1)
      as Htyped_roots1.
    destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
      R Σ e1 T1 Σ1 R1 roots1 Htyped_roots1 Hrn Hctx_roots)
      as [Hctx_roots1 Hrootset1_ctx].
    pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
      env Omega n) R Σ e1 T1 Σ1 R1 roots1 Htyped_shadow1
      Hrn Hctx_keys) as Hctx_keys1.
    assert (Hadd_ctx_roots :
      root_env_ctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1))
      by (apply root_env_ctx_roots_named_add_binding; assumption).
    assert (Hadd_ctx_keys :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1))
      by (apply root_env_sctx_keys_named_add_binding; assumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hadd_ctx_roots Hadd_ctx_keys Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H6.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed_prefix env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_prefix_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hsummary_let :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ELet m x T_hidden e1 e2) T2 (sctx_remove x Sigma2)
        (root_env_remove x R2) roots2 ret_roots).
    { eapply ERSSN_Let; eassumption. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
      env Omega n R Σ (ELet m x T_hidden e1 e2) T2
      (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
      (store_remove x s2) Hsummary_let Hrn Hctx_roots Hctx_keys
      Hstore_final Hrn_final) as [Hnamed_final [Hrootset_final Hkeys_final]].
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hv2.
      * eapply value_roots_exclude_root; eassumption.
    + exact Hroots_removed.
    + exact Hvalue_roots.
    + exact Hrootset_final.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
  - pose proof (typed_env_roots_structural env Omega n R Σ (EBorrow rk p)
      T Σ' R' roots (typed_env_roots_shadow_safe_roots env Omega n R Σ
        (EBorrow rk p) T Σ' R' roots H)) as Hstruct.
    destruct (proj1 eval_preserves_typing_ready_prefix_mutual_core
      env s (EBorrow rk p) s' ret Heval
      Omega n Σ T Σ' ltac:(eapply PRE_Borrow; exact H0) Hstore Hstruct)
      as [Hstore_final [Hvalue _]].
    inversion Heval; subst.
    match goal with
    | Heval_place : eval_place ?s_eval p ?x_eval ?path_eval |- _ =>
        destruct (eval_place_matches_place_path s_eval p x_eval path_eval
          x path Heval_place H0) as [Hx_eval Hpath_eval];
        subst x_eval path_eval
    end.
    assert (Hvalue_roots : value_roots_within roots (VRef x path)).
    { eapply singleton_store_root_ref_roots_within.
      - exact H1.
      - reflexivity. }
    assert (Hrootset_named : root_set_store_roots_named roots s').
    { unfold root_set_store_roots_named. intros z Hin.
      assert (Hz : z = x).
      { destruct (singleton_store_root_some_equiv roots x H1 (RStore z))
          as [Hto _].
        specialize (Hto Hin). simpl in Hto.
        destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
      subst z.
      eapply value_has_type_vref_store_name. exact Hvalue. }
    inversion H; subst; try congruence;
      repeat split; try exact Hstore_final; try exact Hvalue;
      try exact Hroots; try exact Hvalue_roots; try exact Hrootset_named;
      try exact Hshadow; try exact Hrn; try exact Hnamed; try exact Hkeys;
      try exact Hsummary_store.

  - induction H1 as [p Hdirect | p x_parent Hchain IHchain Hwrite_parent Htarget_parent Hmut_parent].
    * destruct Hdirect as [q [qx [qpath [Hp Hqpath]]]]. subst p.
    inversion Heval; subst.
    inversion H; subst; try congruence.
    + inversion H6; subst. inversion H8; subst.
      assert (HTeq : T = T0).
      { eapply typed_place_env_structural_functional.
        - eapply TPES_Deref. exact H7.
        - exact H4. }
      subst T0.
      destruct (eval_place_direct_runtime_target_has_type_prefix
        env Σ' s' q (MkTy u (TRef la RUnique T))
        qx qpath r rpath Hstore H7 Hqpath H9)
        as [se_parent [v_parent [T_parent
          [Hlookup_parent [Hvalue_parent [Htype_parent
            [Hequiv_parent Hparent_value]]]]]]].
      rewrite H11 in Hlookup_parent.
      inversion Hlookup_parent; subst se_parent.
      rewrite H13 in Hvalue_parent.
      inversion Hvalue_parent; subst v_parent.
      assert (Hparent_ref :
        value_has_type env s' (VRef x0 path)
          (MkTy u (TRef la RUnique T))).
      { eapply VHT_LifetimeEquiv.
        - exact Hparent_value.
        - exact Hequiv_parent. }
      destruct (value_has_type_unique_ref_target_lifetime_equiv
        env s' x0 path (MkTy u (TRef la RUnique T)) u la T
        Hparent_ref (ty_lifetime_equiv_refl _))
        as [se_target [v_target [T_target
          [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]].
      assert (Hvalue :
        value_has_type env s' (VRef x0 path)
          (MkTy UAffine (TRef (LVar n) RUnique T))).
      { eapply VHT_LifetimeEquiv with
          (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target)).
        - eapply VHT_Ref; eassumption.
        - constructor. exact Hequiv_target. }
      destruct (eval_place_resolved_write_target_ref_runtime_root
        R' s' (PDeref q) x0 path roots x Hroots H8 H2 H3)
        as [Hxroot Hvalue_roots].
      subst x0.
      assert (Hrootset_named : root_set_store_roots_named roots s').
      { unfold root_set_store_roots_named. intros z Hin.
        assert (Hz : z = x).
        { destruct (singleton_store_root_some_equiv roots x H3 (RStore z))
            as [Hto _].
          specialize (Hto Hin). simpl in Hto.
          destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
        subst z. eapply value_has_type_vref_store_name. exact Hvalue. }
      repeat split; try exact Hstore; try exact Hvalue; try exact Hroots;
        try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
        try exact Hrn; try exact Hnamed; try exact Hkeys; try exact Hsummary_store;
        eauto.
    + inversion H6; subst. inversion H8; subst.
      assert (HTeq : T = T0).
      { eapply typed_place_env_structural_functional.
        - eapply TPES_Deref. exact H11.
        - exact H4. }
      subst T0.
      destruct (eval_place_direct_runtime_target_has_type_prefix
        env Σ' s' q (MkTy u (TRef la RUnique T))
        qx qpath r rpath Hstore H11 Hqpath H12)
        as [se_parent [v_parent [T_parent
          [Hlookup_parent [Hvalue_parent [Htype_parent
            [Hequiv_parent Hparent_value]]]]]]].
      rewrite H14 in Hlookup_parent.
      inversion Hlookup_parent; subst se_parent.
      rewrite H16 in Hvalue_parent.
      inversion Hvalue_parent; subst v_parent.
      assert (Hparent_ref :
        value_has_type env s' (VRef x0 path)
          (MkTy u (TRef la RUnique T))).
      { eapply VHT_LifetimeEquiv.
        - exact Hparent_value.
        - exact Hequiv_parent. }
      destruct (value_has_type_unique_ref_target_lifetime_equiv
        env s' x0 path (MkTy u (TRef la RUnique T)) u la T
        Hparent_ref (ty_lifetime_equiv_refl _))
        as [se_target [v_target [T_target
          [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]].
      assert (Hvalue :
        value_has_type env s' (VRef x0 path)
          (MkTy UAffine (TRef (LVar n) RUnique T))).
      { eapply VHT_LifetimeEquiv with
          (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target)).
        - eapply VHT_Ref; eassumption.
        - constructor. exact Hequiv_target. }
      destruct (eval_place_resolved_write_target_ref_runtime_root
        R' s' (PDeref q) x0 path roots x Hroots H8 H2 H3)
        as [Hxroot Hvalue_roots].
      subst x0.
      assert (Hrootset_named : root_set_store_roots_named roots s').
      { unfold root_set_store_roots_named. intros z Hin.
        assert (Hz : z = x).
        { destruct (singleton_store_root_some_equiv roots x H3 (RStore z))
            as [Hto _].
          specialize (Hto Hin). simpl in Hto.
          destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
        subst z. eapply value_has_type_vref_store_name. exact Hvalue. }
      repeat split; try exact Hstore; try exact Hvalue; try exact Hroots;
        try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
        try exact Hrn; try exact Hnamed; try exact Hkeys; try exact Hsummary_store;
        eauto.
      + inversion H6; subst. inversion H8; subst.
        assert (HTeq : T = T0).
        { eapply typed_place_env_structural_functional.
          - eapply TPES_Deref. exact H9.
          - exact H4. }
        subst T0.
        destruct (eval_place_direct_runtime_target_has_type_prefix
          env Σ' s' q (MkTy u (TRef la RUnique T))
          qx qpath r rpath Hstore H9 Hqpath H10)
          as [se_parent [v_parent [T_parent
            [Hlookup_parent [Hvalue_parent [Htype_parent
              [Hequiv_parent Hparent_value]]]]]]].
        rewrite H12 in Hlookup_parent.
        inversion Hlookup_parent; subst se_parent.
        rewrite H14 in Hvalue_parent.
        inversion Hvalue_parent; subst v_parent.
        assert (Hparent_ref :
          value_has_type env s' (VRef x0 path)
            (MkTy u (TRef la RUnique T))).
        { eapply VHT_LifetimeEquiv.
          - exact Hparent_value.
          - exact Hequiv_parent. }
        destruct (value_has_type_unique_ref_target_lifetime_equiv
          env s' x0 path (MkTy u (TRef la RUnique T)) u la T
          Hparent_ref (ty_lifetime_equiv_refl _))
          as [se_target [v_target [T_target
            [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]].
        assert (Hvalue :
          value_has_type env s' (VRef x0 path)
            (MkTy UAffine (TRef (LVar n) RUnique T))).
        { eapply VHT_LifetimeEquiv with
            (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target)).
          - eapply VHT_Ref; eassumption.
          - constructor. exact Hequiv_target. }
        destruct (eval_place_resolved_write_target_ref_runtime_root
          R' s' (PDeref q) x0 path [RStore x1] x Hroots H8 H2 H3)
          as [Hxroot Hvalue_roots].
        subst x0.
        assert (Hrootset_named : root_set_store_roots_named [RStore x1] s').
        { unfold root_set_store_roots_named. intros z Hin.
          assert (Hz : z = x).
          { destruct (singleton_store_root_some_equiv [RStore x1] x H3 (RStore z))
              as [Hto _].
            specialize (Hto Hin). simpl in Hto.
            destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
          subst z. eapply value_has_type_vref_store_name. exact Hvalue. }
        repeat split; try exact Hstore; try exact Hvalue; try exact Hroots;
          try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
          try exact Hrn; try exact Hnamed; try exact Hkeys; try exact Hsummary_store;
          eauto.
    * inversion Heval; subst.
      inversion H; subst; try congruence.
      all: inversion H8; subst; inversion H6; subst; inversion H4; subst.
      all: match goal with
      | Hparent_unique : typed_place_env_structural ?genv ?Sigma ?parent
          (MkTy ?u (TRef ?la RUnique ?T_unique)),
        Hparent_typed : typed_place_env_structural ?genv ?Sigma ?parent
          (MkTy ?u0 (TRef ?la0 ?rk ?T_result)),
        Hwritep : writable_place_env_structural ?genv ?Sigma ?parent,
        Hchainp : place_resolved_write_writable_chain ?genv ?Rcur ?Sigma ?parent,
        Htargetp : place_resolved_write_target ?Rcur ?parent = Some ?x_parent0,
        Hmutp : sctx_lookup_mut ?x_parent0 ?Sigma = Some MMutable,
        Hstorep : store_typed_prefix ?genv ?st ?Sigma,
        Hrootsp : store_roots_within ?Rcur ?st,
        Hwhole_eval : eval_place ?st (PDeref ?parent) ?xref ?refpath,
        Heval_parent : eval_place ?st ?parent ?r ?rpath,
        Hlookup_parent_eval : store_lookup ?r ?st = Some ?se_r,
        Hvalue_parent_eval : value_lookup_path (se_val ?se_r) ?rpath =
          Some (VRef ?xref ?refpath),
        Hwhole_target : place_resolved_write_target ?Rcur (PDeref ?parent) =
          Some ?x_final,
        Hsingle : singleton_store_root ?roots0 = Some ?x_final |- _ =>
          destruct (eval_place_resolved_writable_chain_runtime_target_exists_prefix
            genv Rcur Sigma st parent (MkTy u (TRef la RUnique T_unique))
            x_parent0 r rpath Hstorep Hparent_unique Hwritep Hrootsp
            Hchainp Htargetp Hmutp Heval_parent)
            as [se_parent [v_parent [T_parent_eval
              [Hr_eq [Hlookup_parent [Hvalue_parent
                [Htype_parent [Hequiv_parent Hv_parent]]]]]]]];
          subst r;
          rewrite Hlookup_parent in Hlookup_parent_eval;
          inversion Hlookup_parent_eval; subst se_r;
          rewrite Hvalue_parent in Hvalue_parent_eval;
          inversion Hvalue_parent_eval; subst v_parent;
          destruct (value_has_type_unique_ref_target_lifetime_equiv
            genv st xref refpath T_parent_eval u la T_unique
            Hv_parent Hequiv_parent)
            as [se_target [v_target [T_target
              [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]];
          assert (Hequiv_result : ty_lifetime_equiv T_target T_result);
          [ eapply ty_lifetime_equiv_trans;
            [ exact Hequiv_target
            | eapply typed_place_env_structural_unique_ref_target_lifetime_equiv;
              [ exact Hparent_unique | exact Hparent_typed ] ]
          | ];
          assert (Hvalue :
            value_has_type genv st (VRef xref refpath)
              (MkTy UAffine (TRef (LVar n) RUnique T_result)));
          [ eapply VHT_LifetimeEquiv with
              (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target));
            [ eapply VHT_Ref; eassumption
            | constructor; exact Hequiv_result ]
          | ];
          destruct (eval_place_resolved_write_target_ref_runtime_root
            Rcur st (PDeref parent) xref refpath roots0 x_final
            Hrootsp Hwhole_eval Hwhole_target Hsingle)
            as [Hxroot Hvalue_roots];
          subst xref;
          assert (Hrootset_named : root_set_store_roots_named roots0 st);
          [ unfold root_set_store_roots_named; intros z Hin;
            assert (Hz : z = x_final);
            [ destruct (singleton_store_root_some_equiv roots0 x_final Hsingle (RStore z))
                as [Hto _];
              specialize (Hto Hin); simpl in Hto;
              destruct Hto as [Hz | []]; inversion Hz; reflexivity
            | subst z; eapply value_has_type_vref_store_name; exact Hvalue ]
          | repeat split; try exact Hstorep; try exact Hvalue; try exact Hrootsp;
            try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
            try exact Hrn; try exact Hnamed; try exact Hkeys;
            try exact Hsummary_store; eauto ]
      end.
  - inversion Heval; subst.
    inversion H; subst; try congruence;
      repeat split; try exact Hstore; try constructor; try exact Hroots;
      try exact Hshadow; try exact Hrn; try exact Hnamed; try exact Hkeys;
      try exact Hsummary_store; eauto.
    unfold root_set_store_roots_named. intros z Hin. contradiction.
  - assert (Hempty_shape : Σ' = Σ /\ R' = R /\ roots = []).
    { inversion H1; subst; try congruence.
      match goal with
      | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          dependent destruction Hfields
      end.
      repeat split; reflexivity. }
    destruct Hempty_shape as [HSigma [HR Hroots_nil]].
    subst Σ' R' roots.
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EStruct name lts args []) T Σ R [] H1)
      as Htyped_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EStruct name lts args []) s' ret Heval
      Omega n R Σ T Σ R []
      (ProvReady_Struct name lts args [] ProvReadyFields_Nil)
      Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    assert (Hs_eq : s' = s).
    { inversion Heval; subst.
      eapply eval_struct_fields_empty_exprs_store_eq; eassumption. }
    subst s'.
    repeat split; try eassumption;
      try apply root_set_store_roots_named_nil;
      try (eapply store_typed_prefix_function_closure_targets_summary; eassumption).
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EAssign p (ELit lit)) T Σ' R' roots H)
      as Htyped_roots.
    assert (Hready : provenance_ready_expr (EAssign p (ELit lit))).
    { apply ProvReady_Assign. apply ProvReady_Lit. }
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EAssign p (ELit lit)) s' ret Heval
      Omega n R Σ T Σ' R' roots Hready Hstore Hroots Hshadow Hrn
      Htyped_roots)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    assert (Hsummary' : store_function_closure_targets_summary env s').
    { inversion Heval; subst.
      all: match goal with
        | Hlit : eval _ _ (ELit _) _ _ |- _ => inversion Hlit; subst
        end.
      all: eauto using
        store_function_closure_targets_summary_store_update_val_value,
        store_function_closure_targets_summary_store_update_path_value,
        eval_lit_value_function_closure_targets_summary. }
    assert (Hnarrow : expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EAssign p (ELit lit)) T Σ' R' roots roots).
    { apply ERSSN_AssignLit. exact H. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
      env Omega n R Σ (EAssign p (ELit lit)) T Σ' R' roots roots s'
      Hnarrow Hrn Hctx_roots Hctx_keys Hstore' Hrn')
      as [Hnamed' [Hrootset_named Hkeys']].
    repeat split; try eassumption.
  - let solve_assign_generic_direct_runtime_prefix_named := ltac:(
      inversion H10; subst; try congruence;
      match goal with
      | Hrhs : typed_env_roots_shadow_safe _ _ _ _ _
          (ECallGeneric _ _ []) _ _ _ _ |- _ =>
          destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
            _ _ _ _ _ _ _ _ _ _ _ _ Hrhs)
            as (fcall_static & sigma_call & arg_roots_call & Hin_call &
                Hname_call & Hcaps_call & Harity_call & Hbounds_call &
                Htyped_args_call & Houtlives_call & Hret_call & Hroots_call)
      end;
      assert (Hstatic_eq : fcall_static = fcallee)
        by (eapply Hunique; eauto);
      subst fcall_static;
      dependent destruction Htyped_args_call;
      match goal with
      | Hcall_eval : eval _ _ (ECallGeneric _ _ []) _ _ |- _ =>
          inversion Hcall_eval; subst; clear Hcall_eval
      end;
      match goal with
      | Hargs_eval : eval_args _ _ [] _ _ |- _ =>
          inversion Hargs_eval; subst; clear Hargs_eval
      end;
      match goal with
      | Hlookup_fn : lookup_fn ?nm ?fns = Some ?f_eval,
        Hin_callee : In fcallee ?fns,
        Hname_callee : fn_name fcallee = ?nm |- _ =>
          assert (Heval_callee_eq : f_eval = fcallee);
          [ eapply lookup_fn_unique_by_name;
            [ exact Hlookup_fn | exact Hin_callee | exact Hname_callee | exact Hunique ]
          | subst f_eval ]
      end;
      match goal with
      | Hrename : alpha_rename_fn_def (store_names ?s_base) fcallee = (?fcall, ?used') |- _ =>
          destruct (alpha_rename_fn_def_subst_empty_struct_body
            (store_names s_base) fcallee fcall used' type_args sname lts tys H3 H5 Hrename)
            as [Hparams_call Hbody_call]
      end;
      match goal with
      | Heval_body : eval env
          (bind_params (apply_type_params type_args (fn_params ?fcall)) [] ?s_base)
          (subst_type_params_expr type_args (fn_body ?fcall)) _ _ |- _ =>
          rewrite Hparams_call in Heval_body; simpl in Heval_body;
          rewrite Hbody_call in Heval_body;
          inversion Heval_body; subst; try discriminate; clear Heval_body
      end;
      rewrite Hparams_call in *; simpl in *;
      match goal with
      | Hfields_eval : eval_struct_fields env ?s_base [] _ ?s_body_local ?values |- _ =>
          pose proof (eval_struct_fields_empty_exprs_store_eq
            env s_base _ s_body_local values Hfields_eval) as Hbody_store_eq;
          pose proof (eval_struct_fields_empty_exprs_values_nil
            env s_base _ s_body_local values Hfields_eval) as Hbody_values_eq;
          subst values; subst s_body_local
      end;
      simpl in *;
      repeat match goal with
      | H : store_remove_params [] ?s_base = ?s_rhs |- _ =>
          change (store_remove_params [] s_base) with s_base in H; subst s_rhs
      end;
      repeat match goal with
      | H : Some (_, _) = Some (_, _) |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
      | H : eval_place _ (PVar _) _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
      | H : store_update_path ?x [] ?v ?s_base = Some ?s_final |- _ =>
          rewrite store_update_path_nil_update_val in H
      end;
      match goal with
      | Hupdate : store_update_val ?x_assign (VStruct sname []) ?s_base = Some s' |- _ =>
          assert (Hv_body : value_has_type env s_base (VStruct sname []) T_body)
      end;
      [ pose proof Hsummary as Hsummary_struct;
        rewrite H5 in Hsummary_struct;
        eapply empty_struct_value_has_type_from_narrow_summary;
        exact Hsummary_struct
      | ];
      match goal with
      | Hv_body : value_has_type env ?s_base (VStruct sname []) T_body |- _ =>
          assert (Hv_ret : value_has_type env s_base (VStruct sname [])
            (apply_lt_ty sigma_call (subst_type_params_ty type_args (fn_ret fcallee))))
      end;
      [ apply value_has_type_apply_lt_ty;
        eapply value_has_type_compatible;
        [ exact Hv_body
        | apply ty_compatible_b_sound with (Ω := fn_outlives fcallee); exact H7 ]
      | ];
      match goal with
      | Hcall_typed : typed_env_roots_shadow_safe _ _ _ ?R_call ?Sigma_call
          (ECallGeneric _ _ []) _ ?Sigma_out ?R_out ?roots_out |- _ =>
          assert (Hcall_outputs : Sigma_out = Sigma_call /\ R_out = R_call /\ roots_out = [])
      end;
      [ match goal with
        | Hcall_typed : typed_env_roots_shadow_safe _ _ _ _ _
            (ECallGeneric _ _ []) _ _ _ _ |- _ =>
            destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
              _ _ _ _ _ _ _ _ _ _ _ _ Hcall_typed)
              as (_f & _sigma & _arg_roots & _Hin & _Hname & _Hcaps & _Harity &
                  _Hbounds & Hargs_typed & _Houtlives & _Hret & _Hroots);
            dependent destruction Hargs_typed;
            simpl; repeat split; reflexivity
        end
      | ];
      destruct Hcall_outputs as [HSigma [HRout Hroots_out]]; subst; simpl in *;
      match goal with
      | Hupdate_val : store_update_val ?x_assign (VStruct sname []) ?s_base = Some s' |- _ =>
          match goal with
          | Hplace : typed_place_env_structural _ _ (PVar _) ?T_place |- _ =>
              inversion Hplace; subst;
              assert (Hv_assign : value_has_type env s_base (VStruct sname []) T_place);
              [ eapply value_has_type_compatible;
                [ exact Hv_ret
                | match goal with
                  | Hcompat_assign : ty_compatible_b Omega _ T_place = true |- _ =>
                      apply ty_compatible_b_sound with (Ω := Omega); exact Hcompat_assign
                  end ]
              | ]
          end;
          assert (Hpres_update : store_ref_targets_preserved env s_base s');
          [ eapply store_update_val_ref_targets_preserved_prefix;
            [ eassumption | eassumption | exact Hv_assign | exact Hupdate_val ]
          | ];
          assert (Hstore_final : store_typed_prefix env s' Σ);
          [ eapply store_typed_prefix_update_val;
            [ eassumption | exact Hpres_update | eassumption | exact Hv_assign
            | exact Hupdate_val ]
          | ];
          match goal with
          | Hlookup_roots : root_env_lookup ?x_lookup ?R_base = Some ?roots_old_assign |- _ =>
              assert (Hroots_final : store_roots_within
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base) s');
              [ eapply store_update_val_roots_within_union;
                [ eassumption | eassumption | exact Hlookup_roots
                | constructor; constructor | exact Hupdate_val ]
              | ];
              assert (Hshadow_final : store_no_shadow s')
                by (eapply store_no_shadow_update_val; [ eassumption | exact Hupdate_val ]);
              assert (Hrn_final : root_env_no_shadow
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base))
                by (eapply root_env_no_shadow_update; eassumption);
              assert (Hnamed_val : root_env_store_roots_named R_base s')
                by (eapply root_env_store_roots_named_store_update_val;
                    [ exact Hupdate_val | eassumption ]);
              assert (Hrootset_named : root_set_store_roots_named [] s')
                by (unfold root_set_store_roots_named; intros z Hz; contradiction);
              assert (Hnamed_final : root_env_store_roots_named
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base) s');
              [ eapply root_env_store_roots_named_update_env_named;
                [ eassumption | exact Hnamed_val | ];
                apply root_set_store_roots_named_union;
                [ unfold root_set_store_roots_named;
                  intros z Hz;
                  unfold root_env_store_roots_named in Hnamed_val;
                  eapply Hnamed_val; [ exact Hlookup_roots | exact Hz ]
                | unfold root_set_store_roots_named; intros z Hz; contradiction ]
              | ];
              assert (Hkeys_val : root_env_store_keys_named R_base s');
              [ match goal with
                | Hkeys_base : root_env_store_keys_named R_base s_base |- _ =>
                    eapply root_env_keys_named_weaken;
                    [ exact Hkeys_base | ];
                    intros y Hy;
                    rewrite (store_update_val_names _ _ _ _ Hupdate_val); exact Hy
                end
              | ];
              assert (Hkeys_final : root_env_store_keys_named
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base) s')
                by (apply root_env_keys_named_update; exact Hkeys_val)
          end;
          assert (Hsummary_final : store_function_closure_targets_summary env s');
          [ eapply store_function_closure_targets_summary_store_update_val_value
              with (x := x_assign) (v := VStruct sname []);
            [ eassumption | simpl; exact I | exact Hupdate_val ]
          | ];
          repeat split;
            try exact Hstore_final; try constructor; try exact Hroots_final;
            try exact Hrootset_named; try exact Hshadow_final; try exact Hrn_final;
            try exact Hnamed_final; try exact Hkeys_final; try exact Hsummary_final
      end
    ) in
    inversion Heval; subst; try discriminate;
    solve_assign_generic_direct_runtime_prefix_named.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) T Σ' R' roots H) as Htyped_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EVar x) s' ret Heval Omega n R Σ T Σ' R' roots
      (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    assert (Hnarrow : expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EVar x) T Σ' R' roots roots).
    { eapply ERSSN_VarNonFunction; eassumption. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
      env Omega n R Σ (EVar x) T Σ' R' roots roots s'
      Hnarrow Hrn Hctx_roots Hctx_keys Hstore' Hrn')
      as [Hnamed' [Hrootset_named Hkeys']].
    pose proof (store_function_closure_targets_summary_eval_var
      env s s' x ret Hsummary_store Heval) as Hsummary'.
    repeat split; try eassumption.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots H) as Htyped_roots.
    assert (Hready : provenance_ready_expr (EDrop (EPlace p))).
    { apply ProvReady_Drop. eapply ProvReady_Place_Direct. exact H0. }
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EDrop (EPlace p)) s' ret Heval Omega n R Σ T Σ' R' roots
      Hready Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    assert (Hnarrow : expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots roots).
    { eapply ERSSN_DropPlaceDirect; eassumption. }
    destruct (expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx
      env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots roots s'
      Hnarrow Hrn Hctx_roots Hctx_keys Hstore' Hrn')
      as [Hnamed' [Hrootset_named Hkeys']].
    pose proof (store_function_closure_targets_summary_eval_drop_place_direct
      env s s' p ret Hsummary_store Heval) as Hsummary'.
    repeat split; try eassumption.
Qed.



Lemma expr_root_shadow_store_safe_narrow_summary_eunit_subst_runtime_package_prefix_named :
  forall env Omega n R Sigma T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma EUnit
      T Sigma' R' roots ->
    forall s s' ret,
      store_typed_prefix env s (subst_type_params_ctx type_args Sigma) ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s EUnit s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' (subst_type_params_ctx type_args Sigma') /\
      value_has_type env s' ret (subst_type_params_ty type_args T) /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Sigma T Sigma' R' roots type_args Htyped
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Heval Hunique.
  pose proof (typed_env_roots_shadow_safe_eunit_subst_type_params_ctx
    env Omega n R Sigma T Sigma' R' roots type_args Htyped)
    as Htyped_subst.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R (subst_type_params_ctx type_args Sigma) EUnit
    (subst_type_params_ty type_args T)
    (subst_type_params_ctx type_args Sigma') R' roots Htyped_subst)
    as Htyped_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s EUnit s' ret Heval Omega n R
    (subst_type_params_ctx type_args Sigma)
    (subst_type_params_ty type_args T)
    (subst_type_params_ctx type_args Sigma') R' roots
    ProvReady_Unit Hstore Hroots Hshadow Hrn Htyped_roots)
    as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots
      [Hshadow' Hrn']]]]]].
  inversion Htyped; subst; try discriminate.
  inversion Heval; subst.
  repeat split; try eassumption; try constructor.
  - unfold root_set_store_roots_named. intros z Hin. contradiction.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_elit_subst_runtime_package_prefix_named :
  forall env Omega n R Sigma lit T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma (ELit lit)
      T Sigma' R' roots ->
    forall s s' ret,
      store_typed_prefix env s (subst_type_params_ctx type_args Sigma) ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (ELit lit) s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' (subst_type_params_ctx type_args Sigma') /\
      value_has_type env s' ret (subst_type_params_ty type_args T) /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Sigma lit T Sigma' R' roots type_args Htyped
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Heval Hunique.
  pose proof (typed_env_roots_shadow_safe_elit_subst_type_params_ctx
    env Omega n R Sigma lit T Sigma' R' roots type_args Htyped)
    as Htyped_subst.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R (subst_type_params_ctx type_args Sigma) (ELit lit)
    (subst_type_params_ty type_args T)
    (subst_type_params_ctx type_args Sigma') R' roots Htyped_subst)
    as Htyped_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (ELit lit) s' ret Heval Omega n R
    (subst_type_params_ctx type_args Sigma)
    (subst_type_params_ty type_args T)
    (subst_type_params_ctx type_args Sigma') R' roots
    (ProvReady_Lit lit) Hstore Hroots Hshadow Hrn Htyped_roots)
    as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots
      [Hshadow' Hrn']]]]]].
  inversion Htyped; subst; try discriminate;
    inversion Heval; subst;
    repeat split; try eassumption; try constructor;
    try (unfold root_set_store_roots_named; intros z Hin; contradiction).
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_evar_subst_runtime_package_prefix_named :
  forall env Omega n R Sigma x T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      T Sigma' R' roots ->
    forall s s' ret,
      store_typed_prefix env s (subst_type_params_ctx type_args Sigma) ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s (EVar x) s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' (subst_type_params_ctx type_args Sigma') /\
      value_has_type env s' ret (subst_type_params_ty type_args T) /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Sigma x T Sigma' R' roots type_args Htyped
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Hsummary_store
    Heval Hunique.
  pose proof (typed_env_roots_shadow_safe_evar_subst_type_params_ctx
    env Omega n R Sigma x T Sigma' R' roots type_args Htyped)
    as Htyped_subst.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R (subst_type_params_ctx type_args Sigma) (EVar x)
    (subst_type_params_ty type_args T)
    (subst_type_params_ctx type_args Sigma') R' roots Htyped_subst)
    as Htyped_roots.
  destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
    env s (EVar x) s' ret Heval Omega n R
    (subst_type_params_ctx type_args Sigma)
    (subst_type_params_ty type_args T)
    (subst_type_params_ctx type_args Sigma') R' roots
    (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_roots)
    as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots
      [Hshadow' Hrn']]]]]].
  pose proof (proj1 preservation_ready_eval_store_names_mutual
    env s (EVar x) s' ret Heval (PRE_Var x)) as Hnames.
  assert (Hrootset_named_start : root_set_store_roots_named roots s).
  { unfold root_set_store_roots_named. intros z Hin.
    inversion Htyped; subst; try discriminate;
      unfold root_env_store_roots_named in Hnamed; eapply Hnamed; eassumption. }
  assert (Hrootset_named : root_set_store_roots_named roots s').
  { eapply root_set_store_roots_named_store_names_eq; eassumption. }
  assert (Hnamed' : root_env_store_roots_named R' s').
  { inversion Htyped; subst; try discriminate;
      eapply root_env_store_roots_named_store_names_eq; eassumption. }
  assert (Hkeys' : root_env_store_keys_named R' s').
  { inversion Htyped; subst; try discriminate;
      eapply root_env_store_keys_named_store_names_eq; eassumption. }
  pose proof (store_function_closure_targets_summary_eval_var
    env s s' x ret Hsummary_store Heval) as Hsummary'.
  repeat split; try eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      store_function_closure_targets_summary env s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' ret T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots ret /\
      root_set_store_roots_named roots s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      root_env_store_roots_named R' s' /\
      root_env_store_keys_named R' s' /\
      store_function_closure_targets_summary env s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Hsummary_store Heval Hunique.
  - dependent destruction H2.
    + eapply expr_root_shadow_store_safe_narrow_tfn_function_value_call_preserves_runtime_package_prefix_named;
        eassumption.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + match goal with
      | Htyped_callee : typed_env_roots_shadow_safe _ _ _ _ _ (EVar x)
          ?T_typed ?Σ_typed ?R_typed ?roots_typed |- _ =>
          pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
            env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
            T_typed Σ_typed R_typed roots_typed H0 Htyped_callee) as Hcore;
          destruct H1 as
            [Tshape params_shape ret_shape Hshape
            | Tshape m_shape bounds_shape body_shape params_shape ret_shape
                Hshape Hbody_shape];
          rewrite Hcore in Hshape; simpl in Hshape;
          first [discriminate | inversion Hshape; subst; simpl in Hbody_shape; discriminate]
      end.
    + eapply expr_root_shadow_store_safe_narrow_tforall_tfn_function_value_call_preserves_runtime_package_prefix_named;
        eassumption.
    + pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
        env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee0
        H0 H3) as Hcore.
      destruct H1 as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape].
      * rewrite Hcore in Hshape; simpl in Hshape; discriminate.
      * rewrite Hcore in Hshape; simpl in Hshape.
        inversion Hshape; subst.
        simpl in Hbody_shape. rewrite H4 in Hbody_shape. discriminate.
  - dependent destruction Heval.
    dependent destruction H6.
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
    | Hbody_eval : eval env
        (bind_params (apply_type_params type_args (fn_params fcall)) vs
          (captured ++ s_args))
        (subst_type_params_expr type_args (fn_body fcall)) s_body ret |- _ =>
        rename Hbody_eval into Heval_body
    end.
    match goal with
    | Htyped_callee_call : typed_env_roots_shadow_safe _ _ _ _ _
        (EVar x) (MkTy _ (TTypeForall _ _ _)) _ _ _ |- _ =>
        pose proof (typed_env_roots_shadow_safe_evar_core_eq_base
          env Omega n R Σ x T_callee Σ_callee R_callee roots_callee
          _ _ _ _ H3 Htyped_callee_call) as Hcore
    end.
    assert (Harity_call : Datatypes.length type_args = type_params).
    { eapply H5. rewrite Hcore. reflexivity. }
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 H6) as Htyped_callee_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      Omega n R Σ (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 (ProvReady_Var x)
      Hstore Hroots Hshadow Hrn
      Htyped_callee_roots) as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
    destruct (typed_env_roots_shadow_safe_evar_store_named
      env Omega n R Σ x (MkTy u (TTypeForall type_params bounds body_ty))
      Σ1 R1 roots_callee0 s H6 Hnamed Hkeys)
      as [Hnamed_fn_s [Hcallee_roots_named_s Hkeys_fn_s]].
    pose proof (proj1 preservation_ready_eval_store_names_mutual
      env s (EVar x) s_fn (VClosure fname captured) Heval_callee
      (PRE_Var x)) as Hcallee_names.
    assert (Hnamed_fn : root_env_store_roots_named R1 s_fn).
    { eapply root_env_store_roots_named_store_names_eq; eassumption. }
    assert (Hcallee_roots_named_fn :
        root_set_store_roots_named roots_callee0 s_fn).
    { eapply root_set_store_roots_named_store_names_eq; eassumption. }
    assert (Hkeys_fn : root_env_store_keys_named R1 s_fn).
    { eapply root_env_store_keys_named_store_names_eq; eassumption. }
    pose proof (value_has_type_closure_captured_nil env s_fn fname captured
      (MkTy u (TTypeForall type_params bounds body_ty)) Hv_callee)
      as Hcaptured_nil.
    subst captured.
    simpl in Hrename, Heval_body.
    pose proof (eval_var_empty_closure_target_summary_of_store_function_closure_targets_summary
      env s s_fn x fname fdef Hsummary_store Heval_callee Hlookup)
      as Hcallee_summary.
    pose proof (store_function_closure_targets_summary_eval_var
      env s s_fn x (VClosure fname []) Hsummary_store Heval_callee)
      as Hsummary_fn.
    pose proof (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
      env args s_fn s_args vs H Hsummary_fn Heval_args) as Hsummary_args.
    destruct (value_has_type_empty_closure_ttypeforall_tfn_components_closed
      env s_fn fname fdef u type_params bounds body_ty param_tys ret_inner
      type_args H0 Hv_callee Hlookup Hunique H7)
      as [Htype_params [Hlifetimes [Hcaps_fdef Hbridge]]].
    assert (Harity_fdef : Datatypes.length type_args = fn_type_params fdef).
    { rewrite Htype_params. exact Harity_call. }
    pose proof (lookup_fn_in fname (env_fns env) fdef Hlookup) as Hin_fdef.
    pose proof
      (check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound
        inst_fuel env type_args H2 fdef Hin_fdef Harity_fdef)
      as Hnarrow_fdef.
    pose proof (typed_args_roots_shadow_safe_roots
      env Omega n R1 Σ1 args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots H9) as Htyped_args_roots.
    pose proof (preservation_ready_args_implies_provenance_ready_closure
      args (store_safe_function_value_call_args_preservation_ready env args H))
      as Hprov_args.
    assert (Hcallee_route :
        callee_body_root_shadow_provenance_ready_at_result_subset env
          (fn_subst_type_params type_args fcall)
          (call_param_root_env
            (apply_type_params type_args (fn_params fcall)) arg_roots R')
          (root_sets_union arg_roots)).
    { eapply (generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_instantiated_narrow_tfn_with_result_subset_prefix_named
        env Omega n R1 Σ1 Σ' R' arg_roots args type_args fdef fcall
        (map (subst_type_params_ty type_args) param_tys)
        (subst_type_params_ty type_args ret_inner) s_fn s_args vs used').
      - exact Hcallee_summary.
      - exact Hnarrow_fdef.
      - exact Hcaps_fdef.
      - exact Hbridge.
      - exact H.
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
    destruct (eval_call_expr_generic_ttypeforall_tfn_components_preserve_typing_with_callee_summary_route_prefix_start
      env s s_fn s_args s_body (EVar x) type_args args fname [] fdef fcall vs ret used'
      Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      type_params bounds body_ty param_tys ret_inner
      H0 (store_safe_function_value_call_args_preservation_ready env args H)
      (ProvReady_Var x)
      Hstore
      Hroots Hshadow Hrn H6 H7 H9 Hunique Hcallee_route)
      as [Hstore_prefix' [Hv [Hpres' [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    pose proof (eval_call_expr_generic_ttypeforall_tfn_components_final_store_eq_route_prefix_start
      env s s_fn s_args s_body (EVar x) type_args args fname [] fdef fcall vs ret used'
      Heval_callee Hlookup Heval_args Hrename Heval_body
      Omega n R Σ Σ1 R1 Σ' R' roots_callee0 arg_roots u
      type_params bounds body_ty param_tys ret_inner
      H0 (store_safe_function_value_call_args_preservation_ready env args H)
      (ProvReady_Var x)
      Hstore
      Hroots Hshadow Hrn H6 H7 H9 Hunique Hcallee_route) as Heq_final.
    destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
      env s_fn args s_args vs Heval_args Omega n R1 Σ1
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots Hprov_args Hstore_fn Hroots_fn Hshadow_fn Hrn_fn
      Htyped_args_roots) as [Hstore_args _].
    destruct (store_safe_function_value_call_args_typed_roots_store_named
      env Omega n R1 Σ1 args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      Σ' R' arg_roots s_fn s_args vs H Htyped_args_roots Heval_args
      Hnamed_fn Hkeys_fn) as [Hnamed_args [Harg_roots_named Hkeys_args]].
    assert (Hcallee_roots_named_args :
        root_set_store_roots_named roots_callee0 s_args).
    { pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
        env s_fn args s_args vs Heval_args
        (store_safe_function_value_call_args_preservation_ready env args H))
        as Hargs_names.
      eapply root_set_store_roots_named_store_names_eq; eassumption. }
    assert (Hrootset_named_args :
        root_set_store_roots_named
          (root_set_union roots_callee0 (root_sets_union arg_roots)) s_args).
    { apply root_set_store_roots_named_union.
      - exact Hcallee_roots_named_args.
      - apply root_sets_store_roots_named_union. exact Harg_roots_named. }
    rewrite <- Heq_final in Hsummary_args.
    repeat split.
    + rewrite Heq_final. exact Hstore_args.
    + exact Hv.
    + exact Hpres'.
    + exact Hroots'.
    + exact Hvroots.
    + rewrite Heq_final. exact Hrootset_named_args.
    + exact Hshadow'.
    + exact Hrn'.
    + rewrite Heq_final. exact Hnamed_args.
    + rewrite Heq_final. exact Hkeys_args.
    + exact Hsummary_args.
  - dependent destruction Heval.
    destruct (IHHsummary1 s s1 v1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
      Hsummary_store Heval1 Hunique)
      as [Hstore1 [Hv1 [Hpres1 [Hroots1_runtime [Hv1_roots [Hroots1_named
        [Hshadow1 [Hrn1 [Hnamed1 [Hkeys1 Hsummary1_store]]]]]]]]]].
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hv1_hidden : value_has_type env s1 v1 T_hidden).
    { eapply VHT_Compatible.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H. }
    assert (Hstore_add :
      store_typed_prefix env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_prefix_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1)).
    { eapply root_env_store_roots_named_add_env_store_add; eassumption. }
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    assert (Hsummary_add :
      store_function_closure_targets_summary env
        (store_add x T_hidden v1 s1)).
    { eapply store_function_closure_targets_summary_add_non_function;
        eassumption. }
    destruct (IHHsummary2 (store_add x T_hidden v1 s1) s2 v2
      Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
      Hsummary_add Heval2 Hunique)
      as [Hstore2 [Hv2 [Hpres2 [Hroots2_runtime [Hvalue_roots [Hroots2_named
        [Hshadow2 [Hrn2 [Hnamed2 [Hkeys2 Hsummary2_store]]]]]]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H6.
      - exact Hremove_names. }
    assert (Hstore_final :
      store_typed_prefix env (store_remove x s2) (sctx_remove x Sigma2))
      by (eapply store_typed_prefix_remove_excluding_root; eassumption).
    assert (Hrn_final : root_env_no_shadow (root_env_remove x R2))
      by (apply root_env_no_shadow_remove; exact Hrn2).
    assert (Hsummary_let :
      expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
        (ELet m x T_hidden e1 e2) T2 (sctx_remove x Sigma2)
        (root_env_remove x R2) roots2 ret_roots).
    { eapply ERSSN_Let; eassumption. }
    assert (Hremain_names :
      forall z,
        In z (store_names s2) ->
        z <> x ->
        In z (store_names (store_remove x s2)))
      by (intros z Hin Hneq; apply store_names_remove_keeps_other; assumption).
    assert (Hnamed_removed :
      root_env_store_roots_named (root_env_remove x R2) s2).
    { eapply root_env_store_roots_named_remove_env; eassumption. }
    assert (Hnamed_final :
      root_env_store_roots_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_roots_named_store_remove_excluding.
      - intros y roots Hlookup.
        apply H6 with (y := y) (roots := roots); [exact Hlookup|].
        intros Heq. subst y.
        rewrite root_env_lookup_remove_eq_no_shadow in Hlookup by exact Hrn2.
        discriminate.
      - exact Hnamed_removed.
      - exact Hremain_names. }
    assert (Hrootset_final :
      root_set_store_roots_named roots2 (store_remove x s2)).
    { eapply root_set_store_roots_named_store_remove_excluding.
      - exact H5.
      - exact Hroots2_named.
      - exact Hremain_names. }
    assert (Hkeys_final :
      root_env_store_keys_named (root_env_remove x R2) (store_remove x s2)).
    { eapply root_env_store_keys_named_remove_env_store_remove; eassumption. }
    assert (Hpres_add_body :
      store_ref_targets_preserved env s1 s2).
    { eapply store_ref_targets_preserved_trans; eassumption. }
    assert (Hpres_removed_from_s1 :
      store_ref_targets_preserved env s1 (store_remove x s2)).
    { eapply store_ref_targets_preserved_remove_after_absent_root;
        eassumption. }
    assert (Hpres_final :
      store_ref_targets_preserved env s (store_remove x s2)).
    { eapply store_ref_targets_preserved_trans; eassumption. }
    repeat split.
    + exact Hstore_final.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hv2.
      * eapply value_roots_exclude_root; eassumption.
    + exact Hpres_final.
    + exact Hroots_removed.
    + exact Hvalue_roots.
    + exact Hrootset_final.
    + apply store_no_shadow_remove. exact Hshadow2.
    + exact Hrn_final.
    + exact Hnamed_final.
    + exact Hkeys_final.
    + apply store_function_closure_targets_summary_store_remove.
      exact Hsummary2_store.
  - dependent destruction Heval.
  - pose proof (typed_env_roots_structural env Omega n R Σ (EBorrow rk p)
      T Σ' R' roots (typed_env_roots_shadow_safe_roots env Omega n R Σ
        (EBorrow rk p) T Σ' R' roots H)) as Hstruct.
    destruct (proj1 eval_preserves_typing_ready_prefix_mutual_core
      env s (EBorrow rk p) s' ret Heval
      Omega n Σ T Σ' ltac:(eapply PRE_Borrow; exact H0) Hstore Hstruct)
      as [Hstore_final [Hvalue Hpres]].
    inversion Heval; subst.
    match goal with
    | Heval_place : eval_place ?s_eval p ?x_eval ?path_eval |- _ =>
        destruct (eval_place_matches_place_path s_eval p x_eval path_eval
          x path Heval_place H0) as [Hx_eval Hpath_eval];
        subst x_eval path_eval
    end.
    assert (Hvalue_roots : value_roots_within roots (VRef x path)).
    { eapply singleton_store_root_ref_roots_within.
      - exact H1.
      - reflexivity. }
    assert (Hrootset_named : root_set_store_roots_named roots s').
    { unfold root_set_store_roots_named. intros z Hin.
      assert (Hz : z = x).
      { destruct (singleton_store_root_some_equiv roots x H1 (RStore z))
          as [Hto _].
        specialize (Hto Hin). simpl in Hto.
        destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
      subst z.
      eapply value_has_type_vref_store_name. exact Hvalue. }
    inversion H; subst; try congruence;
      repeat split; try exact Hstore_final; try exact Hvalue; try exact Hpres;
      try exact Hroots; try exact Hvalue_roots; try exact Hrootset_named;
      try exact Hshadow; try exact Hrn; try exact Hnamed; try exact Hkeys;
      try exact Hsummary_store.

  - induction H1 as [p Hdirect | p x_parent Hchain IHchain Hwrite_parent Htarget_parent Hmut_parent].
    * destruct Hdirect as [q [qx [qpath [Hp Hqpath]]]]. subst p.
    inversion Heval; subst.
    inversion H; subst; try congruence.
    + inversion H6; subst. inversion H8; subst.
      assert (HTeq : T = T0).
      { eapply typed_place_env_structural_functional.
        - eapply TPES_Deref. exact H7.
        - exact H4. }
      subst T0.
      destruct (eval_place_direct_runtime_target_has_type_prefix
        env Σ' s' q (MkTy u (TRef la RUnique T))
        qx qpath r rpath Hstore H7 Hqpath H9)
        as [se_parent [v_parent [T_parent
          [Hlookup_parent [Hvalue_parent [Htype_parent
            [Hequiv_parent Hparent_value]]]]]]].
      rewrite H11 in Hlookup_parent.
      inversion Hlookup_parent; subst se_parent.
      rewrite H13 in Hvalue_parent.
      inversion Hvalue_parent; subst v_parent.
      assert (Hparent_ref :
        value_has_type env s' (VRef x0 path)
          (MkTy u (TRef la RUnique T))).
      { eapply VHT_LifetimeEquiv.
        - exact Hparent_value.
        - exact Hequiv_parent. }
      destruct (value_has_type_unique_ref_target_lifetime_equiv
        env s' x0 path (MkTy u (TRef la RUnique T)) u la T
        Hparent_ref (ty_lifetime_equiv_refl _))
        as [se_target [v_target [T_target
          [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]].
      assert (Hvalue :
        value_has_type env s' (VRef x0 path)
          (MkTy UAffine (TRef (LVar n) RUnique T))).
      { eapply VHT_LifetimeEquiv with
          (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target)).
        - eapply VHT_Ref; eassumption.
        - constructor. exact Hequiv_target. }
      destruct (eval_place_resolved_write_target_ref_runtime_root
        R' s' (PDeref q) x0 path roots x Hroots H8 H2 H3)
        as [Hxroot Hvalue_roots].
      subst x0.
      assert (Hrootset_named : root_set_store_roots_named roots s').
      { unfold root_set_store_roots_named. intros z Hin.
        assert (Hz : z = x).
        { destruct (singleton_store_root_some_equiv roots x H3 (RStore z))
            as [Hto _].
          specialize (Hto Hin). simpl in Hto.
          destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
        subst z. eapply value_has_type_vref_store_name. exact Hvalue. }
      repeat split; try exact Hstore; try exact Hvalue;
        try apply store_ref_targets_preserved_refl; try exact Hroots;
        try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
        try exact Hrn; try exact Hnamed; try exact Hkeys; try exact Hsummary_store;
        eauto.
    + inversion H6; subst. inversion H8; subst.
      assert (HTeq : T = T0).
      { eapply typed_place_env_structural_functional.
        - eapply TPES_Deref. exact H11.
        - exact H4. }
      subst T0.
      destruct (eval_place_direct_runtime_target_has_type_prefix
        env Σ' s' q (MkTy u (TRef la RUnique T))
        qx qpath r rpath Hstore H11 Hqpath H12)
        as [se_parent [v_parent [T_parent
          [Hlookup_parent [Hvalue_parent [Htype_parent
            [Hequiv_parent Hparent_value]]]]]]].
      rewrite H14 in Hlookup_parent.
      inversion Hlookup_parent; subst se_parent.
      rewrite H16 in Hvalue_parent.
      inversion Hvalue_parent; subst v_parent.
      assert (Hparent_ref :
        value_has_type env s' (VRef x0 path)
          (MkTy u (TRef la RUnique T))).
      { eapply VHT_LifetimeEquiv.
        - exact Hparent_value.
        - exact Hequiv_parent. }
      destruct (value_has_type_unique_ref_target_lifetime_equiv
        env s' x0 path (MkTy u (TRef la RUnique T)) u la T
        Hparent_ref (ty_lifetime_equiv_refl _))
        as [se_target [v_target [T_target
          [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]].
      assert (Hvalue :
        value_has_type env s' (VRef x0 path)
          (MkTy UAffine (TRef (LVar n) RUnique T))).
      { eapply VHT_LifetimeEquiv with
          (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target)).
        - eapply VHT_Ref; eassumption.
        - constructor. exact Hequiv_target. }
      destruct (eval_place_resolved_write_target_ref_runtime_root
        R' s' (PDeref q) x0 path roots x Hroots H8 H2 H3)
        as [Hxroot Hvalue_roots].
      subst x0.
      assert (Hrootset_named : root_set_store_roots_named roots s').
      { unfold root_set_store_roots_named. intros z Hin.
        assert (Hz : z = x).
        { destruct (singleton_store_root_some_equiv roots x H3 (RStore z))
            as [Hto _].
          specialize (Hto Hin). simpl in Hto.
          destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
        subst z. eapply value_has_type_vref_store_name. exact Hvalue. }
      repeat split; try exact Hstore; try exact Hvalue;
        try apply store_ref_targets_preserved_refl; try exact Hroots;
        try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
        try exact Hrn; try exact Hnamed; try exact Hkeys; try exact Hsummary_store;
        eauto.
      + inversion H6; subst. inversion H8; subst.
        assert (HTeq : T = T0).
        { eapply typed_place_env_structural_functional.
          - eapply TPES_Deref. exact H9.
          - exact H4. }
        subst T0.
        destruct (eval_place_direct_runtime_target_has_type_prefix
          env Σ' s' q (MkTy u (TRef la RUnique T))
          qx qpath r rpath Hstore H9 Hqpath H10)
          as [se_parent [v_parent [T_parent
            [Hlookup_parent [Hvalue_parent [Htype_parent
              [Hequiv_parent Hparent_value]]]]]]].
        rewrite H12 in Hlookup_parent.
        inversion Hlookup_parent; subst se_parent.
        rewrite H14 in Hvalue_parent.
        inversion Hvalue_parent; subst v_parent.
        assert (Hparent_ref :
          value_has_type env s' (VRef x0 path)
            (MkTy u (TRef la RUnique T))).
        { eapply VHT_LifetimeEquiv.
          - exact Hparent_value.
          - exact Hequiv_parent. }
        destruct (value_has_type_unique_ref_target_lifetime_equiv
          env s' x0 path (MkTy u (TRef la RUnique T)) u la T
          Hparent_ref (ty_lifetime_equiv_refl _))
          as [se_target [v_target [T_target
            [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]].
        assert (Hvalue :
          value_has_type env s' (VRef x0 path)
            (MkTy UAffine (TRef (LVar n) RUnique T))).
        { eapply VHT_LifetimeEquiv with
            (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target)).
          - eapply VHT_Ref; eassumption.
          - constructor. exact Hequiv_target. }
        destruct (eval_place_resolved_write_target_ref_runtime_root
          R' s' (PDeref q) x0 path [RStore x1] x Hroots H8 H2 H3)
          as [Hxroot Hvalue_roots].
        subst x0.
        assert (Hrootset_named : root_set_store_roots_named [RStore x1] s').
        { unfold root_set_store_roots_named. intros z Hin.
          assert (Hz : z = x).
          { destruct (singleton_store_root_some_equiv [RStore x1] x H3 (RStore z))
              as [Hto _].
            specialize (Hto Hin). simpl in Hto.
            destruct Hto as [Hz | []]. inversion Hz. reflexivity. }
          subst z. eapply value_has_type_vref_store_name. exact Hvalue. }
        repeat split; try exact Hstore; try exact Hvalue;
          try apply store_ref_targets_preserved_refl; try exact Hroots;
          try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
          try exact Hrn; try exact Hnamed; try exact Hkeys; try exact Hsummary_store;
          eauto.
    * inversion Heval; subst.
      inversion H; subst; try congruence.
      all: inversion H8; subst; inversion H6; subst; inversion H4; subst.
      all: match goal with
      | Hparent_unique : typed_place_env_structural ?genv ?Sigma ?parent
          (MkTy ?u (TRef ?la RUnique ?T_unique)),
        Hparent_typed : typed_place_env_structural ?genv ?Sigma ?parent
          (MkTy ?u0 (TRef ?la0 ?rk ?T_result)),
        Hwritep : writable_place_env_structural ?genv ?Sigma ?parent,
        Hchainp : place_resolved_write_writable_chain ?genv ?Rcur ?Sigma ?parent,
        Htargetp : place_resolved_write_target ?Rcur ?parent = Some ?x_parent0,
        Hmutp : sctx_lookup_mut ?x_parent0 ?Sigma = Some MMutable,
        Hstorep : store_typed_prefix ?genv ?st ?Sigma,
        Hrootsp : store_roots_within ?Rcur ?st,
        Hwhole_eval : eval_place ?st (PDeref ?parent) ?xref ?refpath,
        Heval_parent : eval_place ?st ?parent ?r ?rpath,
        Hlookup_parent_eval : store_lookup ?r ?st = Some ?se_r,
        Hvalue_parent_eval : value_lookup_path (se_val ?se_r) ?rpath =
          Some (VRef ?xref ?refpath),
        Hwhole_target : place_resolved_write_target ?Rcur (PDeref ?parent) =
          Some ?x_final,
        Hsingle : singleton_store_root ?roots0 = Some ?x_final |- _ =>
          destruct (eval_place_resolved_writable_chain_runtime_target_exists_prefix
            genv Rcur Sigma st parent (MkTy u (TRef la RUnique T_unique))
            x_parent0 r rpath Hstorep Hparent_unique Hwritep Hrootsp
            Hchainp Htargetp Hmutp Heval_parent)
            as [se_parent [v_parent [T_parent_eval
              [Hr_eq [Hlookup_parent [Hvalue_parent
                [Htype_parent [Hequiv_parent Hv_parent]]]]]]]];
          subst r;
          rewrite Hlookup_parent in Hlookup_parent_eval;
          inversion Hlookup_parent_eval; subst se_r;
          rewrite Hvalue_parent in Hvalue_parent_eval;
          inversion Hvalue_parent_eval; subst v_parent;
          destruct (value_has_type_unique_ref_target_lifetime_equiv
            genv st xref refpath T_parent_eval u la T_unique
            Hv_parent Hequiv_parent)
            as [se_target [v_target [T_target
              [Hlookup_target [Hvalue_target [Htype_target Hequiv_target]]]]]];
          assert (Hequiv_result : ty_lifetime_equiv T_target T_result);
          [ eapply ty_lifetime_equiv_trans;
            [ exact Hequiv_target
            | eapply typed_place_env_structural_unique_ref_target_lifetime_equiv;
              [ exact Hparent_unique | exact Hparent_typed ] ]
          | ];
          assert (Hvalue :
            value_has_type genv st (VRef xref refpath)
              (MkTy UAffine (TRef (LVar n) RUnique T_result)));
          [ eapply VHT_LifetimeEquiv with
              (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_target));
            [ eapply VHT_Ref; eassumption
            | constructor; exact Hequiv_result ]
          | ];
          destruct (eval_place_resolved_write_target_ref_runtime_root
            Rcur st (PDeref parent) xref refpath roots0 x_final
            Hrootsp Hwhole_eval Hwhole_target Hsingle)
            as [Hxroot Hvalue_roots];
          subst xref;
          assert (Hrootset_named : root_set_store_roots_named roots0 st);
          [ unfold root_set_store_roots_named; intros z Hin;
            assert (Hz : z = x_final);
            [ destruct (singleton_store_root_some_equiv roots0 x_final Hsingle (RStore z))
                as [Hto _];
              specialize (Hto Hin); simpl in Hto;
              destruct Hto as [Hz | []]; inversion Hz; reflexivity
            | subst z; eapply value_has_type_vref_store_name; exact Hvalue ]
          | repeat split; try exact Hstorep; try exact Hvalue;
            try apply store_ref_targets_preserved_refl; try exact Hrootsp;
            try exact Hvalue_roots; try exact Hrootset_named; try exact Hshadow;
            try exact Hrn; try exact Hnamed; try exact Hkeys;
            try exact Hsummary_store; eauto ]
      end.
  - inversion Heval; subst.
    inversion H; subst; try congruence;
      repeat split; try exact Hstore; try constructor;
      try apply store_ref_targets_preserved_refl; try exact Hroots;
      try exact Hshadow; try exact Hrn; try exact Hnamed; try exact Hkeys;
      try exact Hsummary_store; eauto.
    unfold root_set_store_roots_named. intros z Hin. contradiction.
  - assert (Hempty_shape : Σ' = Σ /\ R' = R /\ roots = []).
    { inversion H1; subst; try congruence.
      match goal with
      | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          dependent destruction Hfields
      end.
      repeat split; reflexivity. }
    destruct Hempty_shape as [HSigma [HR Hroots_nil]].
    subst Σ' R' roots.
    pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EStruct name lts args []) T Σ R [] H1)
      as Htyped_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EStruct name lts args []) s' ret Heval
      Omega n R Σ T Σ R []
      (ProvReady_Struct name lts args [] ProvReadyFields_Nil)
      Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    assert (Hs_eq : s' = s).
    { inversion Heval; subst.
      eapply eval_struct_fields_empty_exprs_store_eq; eassumption. }
    subst s'.
    repeat split; try eassumption;
      try apply store_ref_targets_preserved_refl;
      try apply root_set_store_roots_named_nil;
      try (eapply store_typed_prefix_function_closure_targets_summary; eassumption).
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EAssign p (ELit lit)) T Σ' R' roots H)
      as Htyped_roots.
    assert (Hready : provenance_ready_expr (EAssign p (ELit lit))).
    { apply ProvReady_Assign. apply ProvReady_Lit. }
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EAssign p (ELit lit)) s' ret Heval
      Omega n R Σ T Σ' R' roots Hready Hstore Hroots Hshadow Hrn
      Htyped_roots)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    assert (Hsummary' : store_function_closure_targets_summary env s').
    { inversion Heval; subst.
      all: match goal with
        | Hlit : eval _ _ (ELit _) _ _ |- _ => inversion Hlit; subst
        end.
      all: eauto using
        store_function_closure_targets_summary_store_update_val_value,
        store_function_closure_targets_summary_store_update_path_value,
        eval_lit_value_function_closure_targets_summary. }
    assert (Hrootset_named : root_set_store_roots_named roots s').
    { inversion H; subst; try congruence; unfold root_set_store_roots_named;
        intros z Hin; contradiction. }
    assert (Hnamed' : root_env_store_roots_named R' s').
    { inversion H; subst; try congruence;
        match goal with
        | Hlit_typed : typed_env_roots_shadow_safe _ _ _ _ _ (ELit lit) _ _ _ _ |- _ =>
            inversion Hlit_typed; subst
        end;
        inversion Heval; subst;
        match goal with
        | Hlit : eval _ _ (ELit _) _ _ |- _ => inversion Hlit; subst
        end;
        eapply root_env_store_roots_named_update_env_named.
      all: try exact Hrn.
      all: try solve [eauto using root_env_store_roots_named_store_update_val,
          root_env_store_roots_named_store_update_path].
      all: apply root_set_store_roots_named_union.
      all: first [ unfold root_set_store_roots_named; intros z Hin;
          match goal with
          | Hlookup : root_env_lookup ?x0 ?Rbase = Some ?roots_base,
            Hupd : store_update_val _ _ _ = Some _ |- _ =>
              pose proof (root_env_store_roots_named_store_update_val Rbase _ _ _ _ Hupd Hnamed) as Hnamed_val;
              eapply Hnamed_val; [exact Hlookup | exact Hin]
          | Hlookup : root_env_lookup ?x0 ?Rbase = Some ?roots_base,
            Hupd : store_update_path _ _ _ _ = Some _ |- _ =>
              pose proof (root_env_store_roots_named_store_update_path Rbase _ _ _ _ _ Hupd Hnamed) as Hnamed_path;
              eapply Hnamed_path; [exact Hlookup | exact Hin]
          end
        | unfold root_set_store_roots_named; intros z Hin; contradiction ]. }
    assert (Hkeys' : root_env_store_keys_named R' s').
    { inversion H; subst; try congruence;
        match goal with
        | Hlit_typed : typed_env_roots_shadow_safe _ _ _ _ _ (ELit lit) _ _ _ _ |- _ =>
            inversion Hlit_typed; subst
        end;
        inversion Heval; subst;
        match goal with
        | Hlit : eval _ _ (ELit _) _ _ |- _ => inversion Hlit; subst
        end;
        unfold root_env_store_keys_named in *.
      all: apply root_env_keys_named_update.
      all: eapply root_env_keys_named_weaken; [exact Hkeys |].
      all: intros y Hy.
      all: match goal with
        | Hupd : store_update_val _ _ _ = Some _ |- _ =>
            rewrite (store_update_val_names _ _ _ _ Hupd); exact Hy
        | Hupd : store_update_path _ _ _ _ = Some _ |- _ =>
            rewrite (store_update_path_names _ _ _ _ _ Hupd); exact Hy
        end. }
    repeat split; try eassumption.
  - let solve_assign_generic_direct_runtime_prefix_ctx := ltac:(
      inversion H10; subst; try congruence;
      match goal with
      | Hrhs : typed_env_roots_shadow_safe _ _ _ _ _
          (ECallGeneric _ _ []) _ _ _ _ |- _ =>
          destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
            _ _ _ _ _ _ _ _ _ _ _ _ Hrhs)
            as (fcall_static & sigma_call & arg_roots_call & Hin_call &
                Hname_call & Hcaps_call & Harity_call & Hbounds_call &
                Htyped_args_call & Houtlives_call & Hret_call & Hroots_call)
      end;
      assert (Hstatic_eq : fcall_static = fcallee)
        by (eapply Hunique; eauto);
      subst fcall_static;
      dependent destruction Htyped_args_call;
      match goal with
      | Hcall_eval : eval _ _ (ECallGeneric _ _ []) _ _ |- _ =>
          inversion Hcall_eval; subst; clear Hcall_eval
      end;
      match goal with
      | Hargs_eval : eval_args _ _ [] _ _ |- _ =>
          inversion Hargs_eval; subst; clear Hargs_eval
      end;
      match goal with
      | Hlookup_fn : lookup_fn ?nm ?fns = Some ?f_eval,
        Hin_callee : In fcallee ?fns,
        Hname_callee : fn_name fcallee = ?nm |- _ =>
          assert (Heval_callee_eq : f_eval = fcallee);
          [ eapply lookup_fn_unique_by_name;
            [ exact Hlookup_fn | exact Hin_callee | exact Hname_callee | exact Hunique ]
          | subst f_eval ]
      end;
      match goal with
      | Hrename : alpha_rename_fn_def (store_names ?s_base) fcallee = (?fcall, ?used') |- _ =>
          destruct (alpha_rename_fn_def_subst_empty_struct_body
            (store_names s_base) fcallee fcall used' type_args sname lts tys H3 H5 Hrename)
            as [Hparams_call Hbody_call]
      end;
      match goal with
      | Heval_body : eval env
          (bind_params (apply_type_params type_args (fn_params ?fcall)) [] ?s_base)
          (subst_type_params_expr type_args (fn_body ?fcall)) _ _ |- _ =>
          rewrite Hparams_call in Heval_body; simpl in Heval_body;
          rewrite Hbody_call in Heval_body;
          inversion Heval_body; subst; try discriminate; clear Heval_body
      end;
      rewrite Hparams_call in *; simpl in *;
      match goal with
      | Hfields_eval : eval_struct_fields env ?s_base [] _ ?s_body_local ?values |- _ =>
          pose proof (eval_struct_fields_empty_exprs_store_eq
            env s_base _ s_body_local values Hfields_eval) as Hbody_store_eq;
          pose proof (eval_struct_fields_empty_exprs_values_nil
            env s_base _ s_body_local values Hfields_eval) as Hbody_values_eq;
          subst values; subst s_body_local
      end;
      simpl in *;
      repeat match goal with
      | H : store_remove_params [] ?s_base = ?s_rhs |- _ =>
          change (store_remove_params [] s_base) with s_base in H; subst s_rhs
      end;
      repeat match goal with
      | H : Some (_, _) = Some (_, _) |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
      | H : eval_place _ (PVar _) _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
      | H : store_update_path ?x [] ?v ?s_base = Some ?s_final |- _ =>
          rewrite store_update_path_nil_update_val in H
      end;
      match goal with
      | Hupdate : store_update_val ?x_assign (VStruct sname []) ?s_base = Some s' |- _ =>
          assert (Hv_body : value_has_type env s_base (VStruct sname []) T_body)
      end;
      [ pose proof Hsummary as Hsummary_struct;
        rewrite H5 in Hsummary_struct;
        eapply empty_struct_value_has_type_from_narrow_summary;
        exact Hsummary_struct
      | ];
      match goal with
      | Hv_body : value_has_type env ?s_base (VStruct sname []) T_body |- _ =>
          assert (Hv_ret : value_has_type env s_base (VStruct sname [])
            (apply_lt_ty sigma_call (subst_type_params_ty type_args (fn_ret fcallee))))
      end;
      [ apply value_has_type_apply_lt_ty;
        eapply value_has_type_compatible;
        [ exact Hv_body
        | apply ty_compatible_b_sound with (Ω := fn_outlives fcallee); exact H7 ]
      | ];
      match goal with
      | Hcall_typed : typed_env_roots_shadow_safe _ _ _ ?R_call ?Sigma_call
          (ECallGeneric _ _ []) _ ?Sigma_out ?R_out ?roots_out |- _ =>
          assert (Hcall_outputs : Sigma_out = Sigma_call /\ R_out = R_call /\ roots_out = [])
      end;
      [ match goal with
        | Hcall_typed : typed_env_roots_shadow_safe _ _ _ _ _
            (ECallGeneric _ _ []) _ _ _ _ |- _ =>
            destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
              _ _ _ _ _ _ _ _ _ _ _ _ Hcall_typed)
              as (_f & _sigma & _arg_roots & _Hin & _Hname & _Hcaps & _Harity &
                  _Hbounds & Hargs_typed & _Houtlives & _Hret & _Hroots);
            dependent destruction Hargs_typed;
            simpl; repeat split; reflexivity
        end
      | ];
      destruct Hcall_outputs as [HSigma [HRout Hroots_out]]; subst; simpl in *;
      match goal with
      | Hupdate_val : store_update_val ?x_assign (VStruct sname []) ?s_base = Some s' |- _ =>
          match goal with
          | Hplace : typed_place_env_structural _ _ (PVar _) ?T_place |- _ =>
              inversion Hplace; subst;
              assert (Hv_assign : value_has_type env s_base (VStruct sname []) T_place);
              [ eapply value_has_type_compatible;
                [ exact Hv_ret
                | match goal with
                  | Hcompat_assign : ty_compatible_b Omega _ T_place = true |- _ =>
                      apply ty_compatible_b_sound with (Ω := Omega); exact Hcompat_assign
                  end ]
              | ]
          end;
          assert (Hpres_update : store_ref_targets_preserved env s_base s');
          [ eapply store_update_val_ref_targets_preserved_prefix;
            [ eassumption | eassumption | exact Hv_assign | exact Hupdate_val ]
          | ];
          assert (Hstore_final : store_typed_prefix env s' Σ);
          [ eapply store_typed_prefix_update_val;
            [ eassumption | exact Hpres_update | eassumption | exact Hv_assign
            | exact Hupdate_val ]
          | ];
          match goal with
          | Hlookup_roots : root_env_lookup ?x_lookup ?R_base = Some ?roots_old_assign |- _ =>
              assert (Hroots_final : store_roots_within
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base) s');
              [ eapply store_update_val_roots_within_union;
                [ eassumption | eassumption | exact Hlookup_roots
                | constructor; constructor | exact Hupdate_val ]
              | ];
              assert (Hshadow_final : store_no_shadow s')
                by (eapply store_no_shadow_update_val; [ eassumption | exact Hupdate_val ]);
              assert (Hrn_final : root_env_no_shadow
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base))
                by (eapply root_env_no_shadow_update; eassumption);
              assert (Hnamed_val : root_env_store_roots_named R_base s')
                by (eapply root_env_store_roots_named_store_update_val;
                    [ exact Hupdate_val | eassumption ]);
              assert (Hrootset_named : root_set_store_roots_named [] s')
                by (unfold root_set_store_roots_named; intros z Hz; contradiction);
              assert (Hnamed_final : root_env_store_roots_named
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base) s');
              [ eapply root_env_store_roots_named_update_env_named;
                [ eassumption | exact Hnamed_val | ];
                apply root_set_store_roots_named_union;
                [ unfold root_set_store_roots_named;
                  intros z Hz;
                  unfold root_env_store_roots_named in Hnamed_val;
                  eapply Hnamed_val; [ exact Hlookup_roots | exact Hz ]
                | unfold root_set_store_roots_named; intros z Hz; contradiction ]
              | ];
              assert (Hkeys_val : root_env_store_keys_named R_base s');
              [ match goal with
                | Hkeys_base : root_env_store_keys_named R_base s_base |- _ =>
                    eapply root_env_keys_named_weaken;
                    [ exact Hkeys_base | ];
                    intros y Hy;
                    rewrite (store_update_val_names _ _ _ _ Hupdate_val); exact Hy
                end
              | ];
              assert (Hkeys_final : root_env_store_keys_named
                (root_env_update x_lookup (root_set_union roots_old_assign []) R_base) s')
                by (apply root_env_keys_named_update; exact Hkeys_val)
          end;
          assert (Hsummary_final : store_function_closure_targets_summary env s');
          [ eapply store_function_closure_targets_summary_store_update_val_value
              with (x := x_assign) (v := VStruct sname []);
            [ eassumption | simpl; exact I | exact Hupdate_val ]
          | ];
          repeat split;
            try exact Hstore_final; try constructor; try exact Hpres_update;
            try exact Hroots_final;
            try exact Hrootset_named; try exact Hshadow_final; try exact Hrn_final;
            try exact Hnamed_final; try exact Hkeys_final; try exact Hsummary_final
      end
    ) in
    inversion Heval; subst; try discriminate;
    solve_assign_generic_direct_runtime_prefix_ctx.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EVar x) T Σ' R' roots H) as Htyped_roots.
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EVar x) s' ret Heval Omega n R Σ T Σ' R' roots
      (ProvReady_Var x) Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    assert (Hsummary' : store_function_closure_targets_summary env s')
      by (eapply store_function_closure_targets_summary_eval_var; eassumption).
    assert (Hnamed' : root_env_store_roots_named R' s').
    { inversion H; subst; try congruence; inversion Heval; subst;
        try exact Hnamed;
        apply root_env_store_roots_named_store_mark_used; exact Hnamed. }
    assert (Hrootset_named : root_set_store_roots_named roots s').
    { inversion H; subst; try congruence;
        unfold root_set_store_roots_named; intros z Hin;
        eapply Hnamed'; eassumption. }
    assert (Hkeys' : root_env_store_keys_named R' s').
    { inversion H; subst; try congruence; inversion Heval; subst;
        unfold root_env_store_keys_named in *;
        try exact Hkeys; rewrite store_names_mark_used; exact Hkeys. }
    repeat split; try eassumption.
  - pose proof (typed_env_roots_shadow_safe_roots
      env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots H) as Htyped_roots.
    assert (Hready : provenance_ready_expr (EDrop (EPlace p))).
    { apply ProvReady_Drop. eapply ProvReady_Place_Direct. exact H0. }
    destruct (proj1 eval_preserves_typing_roots_ready_prefix_mutual
      env s (EDrop (EPlace p)) s' ret Heval Omega n R Σ T Σ' R' roots
      Hready Hstore Hroots Hshadow Hrn Htyped_roots)
      as [Hstore' [Hvalue [Hpres [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    assert (Hsummary' : store_function_closure_targets_summary env s')
      by (eapply store_function_closure_targets_summary_eval_drop_place_direct; eassumption).
    assert (Hnamed' : root_env_store_roots_named R' s').
    { inversion H; subst; try congruence.
      match goal with
      | Hplace_typed : typed_env_roots_shadow_safe _ _ _ _ _ (EPlace p) _ _ _ _ |- _ =>
          inversion Hplace_typed; subst; try congruence
      end;
      inversion Heval; subst;
      match goal with
      | Hplace_eval : eval _ _ (EPlace p) _ _ |- _ =>
          inversion Hplace_eval; subst; eauto using root_env_store_roots_named_store_consume_path
      end. }
    assert (Hrootset_named : root_set_store_roots_named roots s').
    { inversion H; subst; try congruence.
      unfold root_set_store_roots_named. intros z Hin. contradiction. }
    assert (Hkeys' : root_env_store_keys_named R' s').
    { inversion H; subst; try congruence.
      repeat match goal with
      | Hplace_typed : typed_env_roots_shadow_safe _ _ _ _ _ (EPlace _) _ _ _ _ |- _ =>
          inversion Hplace_typed; subst; clear Hplace_typed
      end;
      inversion Heval; subst;
      repeat match goal with
      | Hplace_eval : eval _ _ (EPlace _) _ _ |- _ =>
          inversion Hplace_eval; subst; clear Hplace_eval
      end;
      unfold root_env_store_keys_named in *;
      try solve [exact Hkeys];
      match goal with
      | Hconsume : store_consume_path _ _ _ = Some _ |- _ =>
          rewrite (store_consume_path_names _ _ _ _ Hconsume); exact Hkeys
      end. }
    repeat split; try eassumption.
Qed.

