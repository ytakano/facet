From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping AlphaEnvStructural AlphaRoots.
From Facet.TypeSystem Require Export AlphaRootEnvFacts.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.
Theorem typed_roots_shadow_safe_sctx_keys_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_keys_named R' Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ ->
    True).
Proof.
  intros env Ω n.
  apply typed_roots_shadow_safe_ind; intros; try assumption.
  - eapply root_env_sctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - eapply root_env_sctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_callee_args.
  - solve_sctx_keys_single_ih.
  - solve_sctx_keys_single_ih.
  - match goal with
    | Hscrut : typed_env_roots_shadow_safe env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHscrut : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ1,
      Hpayload : ?Rpayload = root_env_add_params_roots_same ?ps ?roots_scrut ?R1,
      Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
        (sctx_add_params ?ps ?Σ1) _ _ ?Σhead_payload ?Rhead_payload _,
      IHhead : root_env_no_shadow ?Rpayload ->
        root_env_sctx_keys_named ?Rpayload (sctx_add_params ?ps ?Σ1) ->
        root_env_sctx_keys_named ?Rhead_payload ?Σhead_payload,
      Hout : ?Rout = root_env_remove_match_params ?ps ?Rhead_payload,
      HΣhead : ?Σhead = sctx_remove_params ?ps ?Σhead_payload,
      Hmerge : ctx_merge_many (ctx_of_sctx ?Σhead) (map ctx_of_sctx ?tail) =
        Some ?Γout,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        pose proof (IHscrut Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Hscrut
              | exact Hrn]);
        assert (Hkeys_payload :
          root_env_sctx_keys_named Rpayload (sctx_add_params ps Σ1))
          by (subst Rpayload;
              apply root_env_sctx_keys_named_add_params_roots_same;
              exact Hkeys1);
        assert (Hrn_payload : root_env_no_shadow Rpayload)
          by (subst Rpayload;
              eapply root_env_add_params_roots_same_no_shadow; eauto);
        pose proof (IHhead Hrn_payload Hkeys_payload) as Hkeys_head_payload;
        assert (Hrn_head_payload : root_env_no_shadow Rhead_payload)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Hhead
              | exact Hrn_payload]);
        assert (Hkeys_head :
          root_env_sctx_keys_named Rout Σhead)
          by (subst Rout Σhead;
              apply root_env_sctx_keys_named_remove_match_params;
              assumption);
        eapply root_env_sctx_keys_named_same_bindings;
        [ eapply ctx_merge_many_same_bindings_left; exact Hmerge
        | exact Hkeys_head ]
    end.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    apply root_env_sctx_keys_named_remove_binding; assumption.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    apply root_env_sctx_keys_named_remove_binding; assumption.
  - solve_sctx_keys_single_ih.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ',
      Hrestore : sctx_restore_path ?Σ1 ?x ?path = infer_ok ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |- _ =>
        apply root_env_sctx_keys_named_update;
        eapply root_env_sctx_keys_named_same_bindings;
        [ eapply sctx_restore_path_same_bindings; exact Hrestore
        | exact (IH Hrn Henv) ]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |-
        root_env_sctx_keys_named (root_env_update _ _ ?R1) ?Σ' =>
        apply root_env_sctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |-
        root_env_sctx_keys_named (root_env_update _ _ ?R1) ?Σ' =>
        apply root_env_sctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_keys_named ?R ?Σ |-
        root_env_sctx_keys_named (root_env_update _ _ ?R1) ?Σ' =>
        apply root_env_sctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - repeat match goal with
    | Hstep : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        let Hkeys' := fresh "Hkeys_step" in
        let Hrn' := fresh "Hrn_step" in
        pose proof (Hstep Hrn Hkeys) as Hkeys';
        assert (Hrn' : root_env_no_shadow R')
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption
              | exact Hrn]);
        clear Hstep
    end.
    eapply root_env_sctx_keys_named_same_bindings.
    + eapply ctx_merge_same_bindings_left. eassumption.
    + eassumption.
  - solve_sctx_keys_callee_args.
  - match goal with
    | Hfield : root_env_no_shadow ?R ->
        root_env_sctx_keys_named ?R ?Σ ->
        root_env_sctx_keys_named ?R1 ?Σ1,
      Hrest : root_env_no_shadow ?R1 ->
        root_env_sctx_keys_named ?R1 ?Σ1 ->
        root_env_sctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_sctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hfield Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption
              | exact Hrn]);
        exact (Hrest Hrn1 Hkeys1)
    end.
  - exact I.
  - exact I.
Qed.

Theorem typed_roots_shadow_safe_sctx_roots_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ' /\
    root_set_sctx_roots_named roots Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ' /\
    Forall (fun roots => root_set_sctx_roots_named roots Σ') roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_env_sctx_roots_named R' Σ' /\
    root_set_sctx_roots_named roots Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Σ ->
    root_set_sctx_roots_named roots_scrut Σ ->
    Forall (fun roots => root_set_sctx_roots_named roots Σ) rootss).
Proof.
  intros env Ω n.
  apply typed_roots_shadow_safe_ind; intros; try solve
    [ split; try assumption; apply root_set_sctx_roots_named_nil ].
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split.
    + eapply root_env_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_set_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split.
    + eapply root_env_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_set_sctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * eapply root_env_lookup_sctx_roots_named; eassumption.
  - solve_sctx_roots_args_union.
  - solve_sctx_roots_args_union.
  - solve_sctx_roots_args_union.
  - (* TERS_CallExpr_Fn: callee roots_callee in Σ1, arg_roots in Σ', need both in Σ' *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_Closure: same pattern as Fn *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_TypeForall: same pattern as Fn/Closure *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExprGeneric_TypeForall: same pattern as TypeForall *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_MixedForall: same pattern as Fn/Closure/TypeForall *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_Forall_Fn: same pattern as Fn/Closure/TypeForall *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - (* TERS_CallExpr_Forall_Closure: same pattern as Forall_Fn *)
    match goal with
    | Htyped : typed_env_roots_shadow_safe ?env ?Ω ?n ?R ?Σ _ _ ?Σ1 ?R1 _,
      IHcallee : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\ root_set_sctx_roots_named ?roots_callee ?Σ1,
      Hargs : typed_args_roots_shadow_safe ?env ?Ω ?n ?R1 ?Σ1 _ _ ?Σ' ?R' _,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcallee Hrn Henv) as [Henv1 Hroots_callee];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; exact Htyped | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv' Harg_roots];
        assert (Hsame : sctx_same_bindings Σ1 Σ')
          by (eapply typed_args_env_structural_same_bindings;
              eapply typed_args_roots_structural;
              eapply typed_args_roots_shadow_safe_roots; exact Hargs);
        split;
        [ exact Henv'
        | apply root_set_sctx_roots_named_union;
          [ eapply root_set_sctx_roots_named_same_bindings; [exact Hsame | exact Hroots_callee]
          | apply root_sets_sctx_roots_named_union; exact Harg_roots ] ]
    end.
  - solve_sctx_roots_single_ih.
  - solve_sctx_roots_args_union.
	  - destruct (H H2 H3) as [Henv1 Hroots_scrut_named].
	    assert (Hrn1 : root_env_no_shadow R1)
	      by (eapply typed_env_roots_no_shadow;
	          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H2]).
	    assert (Henv_payload :
	      root_env_sctx_roots_named R_payload (sctx_add_params ps_head Σ1)).
	    { subst R_payload.
	      apply root_env_sctx_roots_named_add_params_roots_same; assumption. }
	    assert (Hrn_payload : root_env_no_shadow R_payload).
	    { subst R_payload.
	      eapply root_env_add_params_roots_same_no_shadow; eauto. }
	    destruct (H0 Hrn_payload Henv_payload) as
	      [Henv_head_payload Hroots_head_payload].
	    assert (Hrn_head_payload : root_env_no_shadow R_head_payload).
	    { eapply typed_env_roots_no_shadow.
	      - eapply typed_env_roots_shadow_safe_roots. exact t0.
	      - exact Hrn_payload. }
	    assert (Henv_head : root_env_sctx_roots_named R_out Σ_head).
	    { subst R_out Σ_head.
	      apply root_env_sctx_roots_named_remove_match_params; assumption. }
	    assert (Hroots_head : root_set_sctx_roots_named roots_head Σ_head).
	    { subst Σ_head.
	      apply root_set_sctx_roots_named_remove_match_params; assumption. }
	    pose proof (H1 Hrn1 Henv1 Hroots_scrut_named) as Hroots_tail.
	    assert (Hsame_head_final :
	      sctx_same_bindings Σ_head (sctx_of_ctx Γ_out)).
	    { eapply ctx_merge_many_same_bindings_left. exact e16. }
    assert (Hsame_1_head : sctx_same_bindings Σ1 Σ_head).
    { subst Σ_head.
      apply sctx_same_bindings_remove_added_params.
      eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact t0. }
    assert (Hsame_1_final :
      sctx_same_bindings Σ1 (sctx_of_ctx Γ_out)).
    { eapply sctx_same_bindings_trans; eassumption. }
    assert (Hroots_tail_final :
      Forall (fun roots => root_set_sctx_roots_named roots (sctx_of_ctx Γ_out))
        roots_tail).
    { eapply Forall_impl.
      - intros roots Hnamed.
        eapply root_set_sctx_roots_named_same_bindings.
        + exact Hsame_1_final.
        + exact Hnamed.
      - exact Hroots_tail. }
    split.
    + eapply root_env_sctx_roots_named_same_bindings.
      * exact Hsame_head_final.
      * exact Henv_head.
    + apply root_sets_sctx_roots_named_union.
      simpl. constructor.
      * eapply root_set_sctx_roots_named_same_bindings.
        -- exact Hsame_head_final.
        -- exact Hroots_head.
      * exact Hroots_tail_final.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Henv_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    split.
    + apply root_env_sctx_roots_named_remove_binding; assumption.
    + apply root_set_sctx_roots_named_remove_binding; assumption.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; exact t | exact H1]).
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Henv_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact Hrn_add. }
    split.
    + apply root_env_sctx_roots_named_remove_binding; assumption.
    + apply root_set_sctx_roots_named_remove_binding; assumption.
  - destruct (H H0 H1) as [Henv Hroots].
    split; [exact Henv | apply root_set_sctx_roots_named_nil].
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]).
    assert (Hroots_old : root_set_sctx_roots_named roots_old Σ1)
      by (eapply root_env_lookup_sctx_roots_named; eassumption).
    split.
    + eapply root_env_sctx_roots_named_update_union_restore_path;
        eassumption.
    + eapply root_env_lookup_result_sctx_roots_named_after_typed_restore_path;
        eassumption.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]).
    assert (Hroots_old : root_set_sctx_roots_named roots_old Σ1)
      by (eapply root_env_lookup_sctx_roots_named; eassumption).
    split.
    + eapply root_env_sctx_roots_named_update_union; eassumption.
    + eapply root_env_lookup_result_sctx_roots_named_after_typed;
        eassumption.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]).
    assert (Hroots_old : root_set_sctx_roots_named roots_old Σ')
      by (eapply root_env_lookup_sctx_roots_named; eassumption).
    split.
    + eapply root_env_sctx_roots_named_update_union; eassumption.
    + apply root_set_sctx_roots_named_nil.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow;
          [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]).
    assert (Hroots_old : root_set_sctx_roots_named roots_old Σ')
      by (eapply root_env_lookup_sctx_roots_named; eassumption).
    split.
    + eapply root_env_sctx_roots_named_update_union; eassumption.
    + apply root_set_sctx_roots_named_nil.
  - split; try assumption.
    eapply root_of_place_sctx_roots_named. eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_borrow_roots ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_borrow_roots_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply place_resolved_roots_sctx_roots_named.
    + eassumption.
    + eapply root_of_place_sctx_roots_named; eassumption.
    + eassumption.
  - split; try assumption.
    eapply root_store_single_sctx_roots_named_of_place_path; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_borrow_roots ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_borrow_roots_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply place_resolved_roots_sctx_roots_named.
    + eassumption.
    + eapply root_of_place_sctx_roots_named; eassumption.
    + eassumption.
  - split; try assumption.
    eapply place_resolved_write_target_writable_chain_sctx_roots_named; eassumption.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_root_lookup ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - split; try assumption.
    eapply root_env_lookup_sctx_roots_named; eassumption.
  - split; try assumption.
    match goal with
    | Hpath : place_path ?p = None,
      Hlookup : place_root_lookup ?R ?p = Some ?roots |-
        root_set_sctx_roots_named ?roots ?Σ =>
        rewrite (place_root_lookup_indirect R p Hpath) in Hlookup;
        eapply root_env_lookup_sctx_roots_named; eassumption
    end.
  - match goal with
    | IHcond : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\
        root_set_sctx_roots_named ?roots_cond ?Σ1,
      IHthen : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R2 ?Σ2 /\
        root_set_sctx_roots_named ?roots2 ?Σ2,
      IHelse : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R3 ?Σ3 /\
        root_set_sctx_roots_named ?roots3 ?Σ3,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcond Hrn Henv) as [Henv1 _];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption | exact Hrn]);
        destruct (IHthen Hrn1 Henv1) as [Henv2 Hroots2];
        destruct (IHelse Hrn1 Henv1) as [_ Hroots3];
        split;
        [ eapply root_env_sctx_roots_named_ctx_merge_left; eassumption
        | eapply root_set_sctx_roots_named_if_merge; eassumption ]
    end.
  - split; try assumption. constructor.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\
        root_set_sctx_roots_named ?roots ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_sctx_roots_named roots ?Σ2)
          ?roots_rest,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption | exact Hrn]);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_rest];
        split; [exact Henv2 | constructor; [| exact Hroots_rest]];
        eapply root_set_sctx_roots_named_typed_args_tail; eassumption
    end.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_env_sctx_roots_named ?R1 ?Σ1 /\
        root_set_sctx_roots_named ?roots_field ?Σ1,
      IHfields : root_env_no_shadow ?R1 ->
        root_env_sctx_roots_named ?R1 ?Σ1 ->
        root_env_sctx_roots_named ?R2 ?Σ2 /\
        root_set_sctx_roots_named ?roots_rest ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow;
              [eapply typed_env_roots_shadow_safe_roots; eassumption | exact Hrn]);
        destruct (IHfields Hrn1 Henv1) as [Henv2 Hroots_rest];
        split;
        [ exact Henv2
        | apply root_set_sctx_roots_named_union; [| exact Hroots_rest] ];
        eapply root_set_sctx_roots_named_typed_fields_tail; eassumption
    end.
  - constructor.
  - match goal with
    | Htyped : typed_env_roots_shadow_safe env Ω n ?Rpayload
        (sctx_add_params ?ps ?Σ) _ _ ?Σv_payload ?Rv_payload ?roots,
      IHtyped : root_env_no_shadow ?Rpayload ->
        root_env_sctx_roots_named ?Rpayload (sctx_add_params ?ps ?Σ) ->
        root_env_sctx_roots_named ?Rv_payload ?Σv_payload /\
        root_set_sctx_roots_named ?roots ?Σv_payload,
      IHtail : root_env_no_shadow ?R ->
        root_env_sctx_roots_named ?R ?Σ ->
        root_set_sctx_roots_named ?roots_scrut ?Σ ->
        Forall (fun roots0 => root_set_sctx_roots_named roots0 ?Σ) ?rootss,
      HRpayload : ?Rpayload = root_env_add_params_roots_same ?ps ?roots_scrut ?R,
      HΣv : ?Σv = sctx_remove_params ?ps ?Σv_payload,
      Hroots_excl : roots_exclude_params ?ps ?roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_sctx_roots_named ?R ?Σ,
      Hroots_scrut : root_set_sctx_roots_named ?roots_scrut ?Σ |- _ =>
        assert (Henv_payload :
          root_env_sctx_roots_named Rpayload (sctx_add_params ps Σ))
          by (subst Rpayload;
              apply root_env_sctx_roots_named_add_params_roots_same;
              assumption);
        assert (Hrn_payload : root_env_no_shadow Rpayload)
          by (subst Rpayload;
              eapply root_env_add_params_roots_same_no_shadow; eauto);
        destruct (IHtyped Hrn_payload Henv_payload) as [_ Hroots_payload];
        assert (Hsame_payload :
          sctx_same_bindings (sctx_add_params ps Σ) Σv_payload)
          by (eapply typed_env_structural_same_bindings;
              eapply typed_env_roots_structural;
              eapply typed_env_roots_shadow_safe_roots; exact Htyped);
        assert (Hsame_branch : sctx_same_bindings Σ Σv)
          by (subst Σv;
              apply sctx_same_bindings_remove_added_params;
              exact Hsame_payload);
        pose proof (IHtail Hrn Henv Hroots_scrut) as Hroots_tail;
        constructor; [| exact Hroots_tail];
        eapply root_set_sctx_roots_named_same_bindings;
        [ apply sctx_same_bindings_sym; exact Hsame_branch
        | subst Σv;
          apply root_set_sctx_roots_named_remove_match_params; assumption ]
    end.
Qed.
