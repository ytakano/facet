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


Lemma alpha_rename_typed_env_roots_trivial_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    (e = EUnit \/ exists l, e = ELit l) ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hshape Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  destruct Hshape as [Heq | [l Heq]]; subst e.
  - simpl in Hrename. injection Hrename as <- <-.
    inversion Htyped; subst.
    exists Σr, Rr, []. repeat split;
      try solve [apply TER_Unit | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
  - simpl in Hrename. injection Hrename as <- <-.
    destruct l; inversion Htyped; subst;
      exists Σr, Rr, []; repeat split;
      try solve [constructor | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
Qed.

Lemma alpha_rename_typed_env_roots_fn_forward :
  forall env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EFn fname) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EFn fname)) (rename_range rho) ->
    alpha_rename_expr rho used (EFn fname) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots
    Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  inversion Htyped; subst.
  exists Σr, Rr, [].
  split; [| split; [| split; [| split]]].
  - eapply TER_Fn; eauto.
  - exact Hctx.
  - exact HnsRr.
  - exact HRr.
  - apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_trivial_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    (e = EUnit \/ exists l, e = ELit l) ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hshape Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  destruct Hshape as [Heq | [l Heq]]; subst e.
  - simpl in Hrename. injection Hrename as <- <-.
    inversion Htyped; subst.
    exists Σr, Rr, []. repeat split;
      try solve [apply TERS_Unit | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
  - simpl in Hrename. injection Hrename as <- <-.
    destruct l; inversion Htyped; subst;
      exists Σr, Rr, []; repeat split;
      try solve [constructor | exact Hctx | exact HnsRr | exact HRr |
        apply root_set_equiv_refl].
Qed.

Lemma alpha_rename_typed_env_roots_fn_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EFn fname) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EFn fname)) (rename_range rho) ->
    alpha_rename_expr rho used (EFn fname) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots
    Htyped Hctx _ HnsRr HRr _ _ _ _ _ Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  inversion Htyped; subst.
  exists Σr, Rr, [].
  split; [| split; [| split; [| split]]].
  - eapply TERS_Fn; eauto.
  - exact Hctx.
  - exact HnsRr.
  - exact HRr.
  - apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_drop_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots env Ω n R Σ (EDrop e) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EDrop e)) (rename_range rho) ->
    alpha_rename_expr rho used (EDrop e) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (alpha_rename_expr rho used e) as [er0 used1] eqn:Hrename_e.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (Hexpr R Rr Σ Σr used er0 used1 T0 Σ' R' roots0)
    as [Σr' [Rr' [rootsr
      [Htyped_r [Hctx_r [HnsRr' [HRr' _]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e T0 Σ' R' roots0 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename_e.
  - exists Σr', Rr', [].
    split; [| split; [| split; [| split]]].
    + eapply TER_Drop. exact Htyped_r.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_drop_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EDrop e) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EDrop e)) (rename_range rho) ->
    alpha_rename_expr rho used (EDrop e) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (alpha_rename_expr rho used e) as [er0 used1] eqn:Hrename_e.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (Hexpr R Rr Σ Σr used er0 used1 T0 Σ' R' roots0)
    as [Σr' [Rr' [rootsr
      [Htyped_r [Hctx_r [HnsRr' [HRr' _]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e T0 Σ' R' roots0 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename_e.
  - exists Σr', Rr', [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Drop. exact Htyped_r.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_trivial_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
    (e = EUnit \/ exists l, e = ELit l) ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr e) (rename_range rho) ->
    alpha_rename_expr rho used e = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hshape Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_trivial_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_fn_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EFn fname) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EFn fname)) (rename_range rho) ->
    alpha_rename_expr rho used (EFn fname) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_fn_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_drop_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EDrop e) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EDrop e)) (rename_range rho) ->
    alpha_rename_expr rho used (EDrop e) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (alpha_rename_expr rho used e) as [er0 used1] eqn:Hrename_e.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (Hexpr R Rr Σ Σr used er0 used1 T0 Σ' R' roots0)
    as [Σr' [Rr' [rootsr
      [Htyped_r [Hctx_r [HnsRr' [HRr' _]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e T0 Σ' R' roots0 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR'.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj.
  - exact Hrename_e.
  - exists Σr', Rr', [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Drop. exact Htyped_r.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_replace_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots env Ω n R Σ (EReplace p e_new) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EReplace p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EReplace p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ1 R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (ctx_alpha_restore_path_forward
      rho Σ1 Σr1 x path Σ' Hctx_new_r Hsafe_x
      ltac:(match goal with
        | H : sctx_restore_path Σ1 x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr2 [Hrestore_r Hctx_restore]].
    destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_result_r Hroots_result]].
    destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr2,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TER_Replace_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Hlookup_result_r.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
      * exact Hrestore_r.
    + exact Hctx_restore.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + exact Hroots_result.
  - assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { rewrite <- (root_env_names_update x
        (root_set_union roots_old roots_new) R1).
      exact HnocollR'. }
    destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
      as [Σr1 [Rr1 [roots_newr
        [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
    + match goal with
      | H : typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
          exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_new.
    + exact Hnew.
    + assert (Htarget_r :
        place_resolved_write_target Rr (rename_place rho p) =
        Some (lookup_rename x rho)).
      { eapply place_resolved_write_target_equiv.
        - apply root_env_equiv_sym. exact HRr.
        - apply place_resolved_write_target_rename.
          + exact HnocollR.
          + match goal with
            | H : place_resolved_write_target R p = Some x |- _ => exact H
            end. }
      destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
        HRr HnocollR
        ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [roots_resultr [Hlookup_result_r Hroots_result]].
      destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
        HRr1 HnocollR1
        ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
      exists Σr1,
        (root_env_update (lookup_rename x rho)
          (root_set_union roots_oldr roots_newr) Rr1),
        roots_resultr.
      split; [| split; [| split; [| split]]].
      * eapply TER_Replace_Resolved.
        -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
        -- eapply place_resolved_write_writable_chain_rename;
           [ apply root_env_equiv_sym; exact HRr
           | exact HnocollR
           | exact Hctx
           | exact Hdisj_p
           | eassumption ].
        -- exact Htarget_r.
        -- exact Hlookup_result_r.
        -- eapply ctx_alpha_lookup_mut_forward_any; eauto.
        -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
        -- exact Htyped_new_r.
        -- exact Hlookup_old_r.
        -- match goal with
           | H : ty_compatible_b Ω T_new T = true |- _ => exact H
           end.
      * exact Hctx_new_r.
      * apply root_env_no_shadow_update. exact HnsRr1.
      * eapply root_env_equiv_update_rename_union; eauto.
        apply HnocollR1. eapply root_env_lookup_some_in_names.
        match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end.
      * exact Hroots_result.
Qed.

Lemma alpha_rename_typed_env_roots_assign_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots env Ω n R Σ (EAssign p e_new) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EAssign p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EAssign p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr1,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      [].
    split; [| split; [| split; [| split]]].
    + eapply TER_Assign_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T_old <> ULinear |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
    + exact Hctx_new_r.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + apply root_set_equiv_refl.
  - assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { rewrite <- (root_env_names_update x
        (root_set_union roots_old roots_new) R1).
      exact HnocollR'. }
    destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
      as [Σr1 [Rr1 [roots_newr
        [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
    + match goal with
      | H : typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
          exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_new.
    + exact Hnew.
    + assert (Htarget_r :
        place_resolved_write_target Rr (rename_place rho p) =
        Some (lookup_rename x rho)).
      { eapply place_resolved_write_target_equiv.
        - apply root_env_equiv_sym. exact HRr.
        - apply place_resolved_write_target_rename.
          + exact HnocollR.
          + match goal with
            | H : place_resolved_write_target R p = Some x |- _ => exact H
            end. }
      destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
        HRr1 HnocollR1
        ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
      exists Σr1,
        (root_env_update (lookup_rename x rho)
          (root_set_union roots_oldr roots_newr) Rr1),
        [].
      split; [| split; [| split; [| split]]].
      * eapply TER_Assign_Resolved.
        -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
        -- match goal with
           | H : ty_usage T_old <> ULinear |- _ => exact H
           end.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
        -- eapply place_resolved_write_writable_chain_rename;
           [ apply root_env_equiv_sym; exact HRr
           | exact HnocollR
           | exact Hctx
           | exact Hdisj_p
           | eassumption ].
        -- exact Htarget_r.
        -- eapply ctx_alpha_lookup_mut_forward_any; eauto.
        -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
        -- exact Htyped_new_r.
        -- exact Hlookup_old_r.
        -- match goal with
           | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
           end.
      * exact Hctx_new_r.
      * apply root_env_no_shadow_update. exact HnsRr1.
      * eapply root_env_equiv_update_rename_union; eauto.
        apply HnocollR1. eapply root_env_lookup_some_in_names.
        match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end.
      * apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_var_forward :
  forall env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EVar x) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (EVar x)) (rename_range rho) ->
    alpha_rename_expr rho used (EVar x) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TER_Var_Copy.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- apply Hdisj. simpl. left. reflexivity.
        -- match goal with
           | H : typed_place_env_structural env _ (PVar x) T |- _ =>
               exact H
           end.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe : ~ In x (rename_range rho)).
    { apply Hdisj. simpl. left. reflexivity. }
    destruct (ctx_alpha_consume_path_forward
      rho _ Σr x [] Σ' Hctx Hsafe
      ltac:(match goal with
        | H : sctx_consume_path _ x [] = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TER_Var_Move.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_place_forward :
  forall env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EPlace p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EPlace p)) (rename_range rho) ->
    alpha_rename_expr rho used (EPlace p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TER_Place_Copy.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    destruct (ctx_alpha_consume_path_forward
      rho Σ Σr x path Σ' Hctx Hsafe_x
      ltac:(match goal with
        | H : sctx_consume_path Σ x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TER_Place_Move.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_borrow_forward :
  forall env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots,
    typed_env_roots env Ω n R Σ (EBorrow rk p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    rename_no_collision_on rho
      (root_env_all_store_names R ++ root_set_store_names (root_of_place p)) ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EBorrow rk p)) (rename_range rho) ->
    alpha_rename_expr rho used (EBorrow rk p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR' HnocollResolved
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. destruct rk; injection Hrename as <- <-;
    inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    exists Σr, Rr, (root_of_place (rename_place rho p)). repeat split.
    + eapply TER_BorrowShared.
      eapply alpha_rename_typed_place_env_structural_forward; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + rewrite root_of_place_rename_place. simpl. tauto.
    + rewrite root_of_place_rename_place. simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TER_BorrowShared_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- exact Hsafe_root.
        -- eassumption.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hresolved : place_resolved_roots ?Rsrc p = Some roots,
      Hns : root_env_no_shadow ?Rsrc,
      Heq : root_env_equiv Rr (root_env_rename rho ?Rsrc) |- _ =>
        destruct (place_resolved_roots_rename_no_shadow_equiv
          rho Rsrc Rr p roots Hns HnsRr Heq HnocollResolved Hresolved)
          as [rootsr [Hresolved_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TER_BorrowShared_Resolved.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * exact Hresolved_r.
      * rewrite (singleton_store_root_equiv rootsr (root_set_rename rho roots) Hrootsr).
        apply singleton_store_root_rename_some.
        match goal with Hsingle : singleton_store_root roots = Some _ |- _ =>
          exact Hsingle
        end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    exists Σr, Rr, [RStore (lookup_rename x rho)]. repeat split.
    + eapply TER_BorrowUnique.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply ctx_alpha_lookup_mut_forward_any; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + simpl. tauto.
    + simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TER_BorrowUnique_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hresolved : place_resolved_roots ?Rsrc p = Some roots,
      Hns : root_env_no_shadow ?Rsrc,
      Heq : root_env_equiv Rr (root_env_rename rho ?Rsrc) |- _ =>
        destruct (place_resolved_roots_rename_no_shadow_equiv
          rho Rsrc Rr p roots Hns HnsRr Heq HnocollResolved Hresolved)
          as [rootsr [Hresolved_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TER_BorrowUnique_Resolved.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
      * exact Hresolved_r.
      * rewrite (singleton_store_root_equiv rootsr (root_set_rename rho roots) Hrootsr).
        apply singleton_store_root_rename_some.
        match goal with Hsingle : singleton_store_root roots = Some _ |- _ =>
          exact Hsingle
        end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hchain_r :
      place_resolved_write_writable_chain env Rr Σr (rename_place rho p)).
    { eapply place_resolved_write_writable_chain_rename.
      - apply root_env_equiv_sym. exact HRr.
      - exact HnocollR.
      - exact Hctx.
      - exact Hsafe_root.
      - eassumption. }
    assert (Htarget_r :
      place_resolved_write_target Rr (rename_place rho p) =
        Some (lookup_rename x rho)).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HRr.
      - apply place_resolved_write_target_rename.
        + exact HnocollR.
        + eassumption. }
    exists Σr, Rr, [RStore (lookup_rename x rho)]. repeat split.
    + eapply TER_BorrowUnique_ResolvedTarget.
      * eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- exact Hsafe_root.
        -- eassumption.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward.
        -- exact Hctx.
        -- exact Hsafe_root.
        -- eassumption.
      * exact Hchain_r.
      * exact Htarget_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + simpl. tauto.
    + simpl. tauto.
  Unshelve.
  all: try exact Hsafe_root; try exact HnocollR; try exact HnocollR'; try exact HnocollResolved; try exact Hctx; eauto.

Qed.

Lemma root_env_names_remove_preserve_neq :
  forall x y R,
    x <> y ->
    In y (root_env_names R) ->
    In y (root_env_names (root_env_remove x R)).
Proof.
  intros x y R Hneq Hin.
  induction R as [| [z roots] rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hy | Hin].
    + subst z.
      destruct (ident_eqb x y) eqn:Hxy.
      * apply ident_eqb_eq in Hxy. contradiction.
      * simpl. left. reflexivity.
    + destruct (ident_eqb x z); simpl.
      * exact Hin.
      * right. apply IH. exact Hin.
Qed.

Lemma root_env_add_params_roots_same_preserve_name :
  forall ps roots R x,
    In x (root_env_names R) ->
    In x (root_env_names (root_env_add_params_roots_same ps roots R)).
Proof.
  induction ps as [| p ps IH]; intros roots R x Hin; simpl.
  - exact Hin.
  - right. apply IH. exact Hin.
Qed.

Lemma root_env_lookup_params_none_b_not_in :
  forall ps R x,
    root_env_lookup_params_none_b ps R = true ->
    In x (ctx_names (params_ctx ps)) ->
    ~ In x (root_env_names R).
Proof.
  induction ps as [| [m y T] ps IH]; intros R x Hfresh Hin; simpl in *.
  - contradiction.
  - destruct (root_env_lookup y R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct Hin as [Heq | Hin].
    + subst x.
      apply root_env_lookup_none_not_in_names. exact Hlookup.
    + eapply IH; eassumption.
Qed.

Lemma root_env_remove_match_params_preserve_name_not_params :
  forall ps R x,
    (forall y, In y (ctx_names (params_ctx ps)) -> x <> y) ->
    In x (root_env_names R) ->
    In x (root_env_names (root_env_remove_match_params ps R)).
Proof.
  induction ps as [| [m y T] ps IH]; intros R x Hnot Hin; simpl.
  - exact Hin.
  - apply IH.
    + intros z Hz. apply Hnot. right. exact Hz.
    + apply root_env_names_remove_preserve_neq.
      * intros Heq. apply (Hnot y); [left; reflexivity | symmetry; exact Heq].
      * exact Hin.
Qed.

Lemma root_env_remove_shadow_safe_rename_no_collision_on :
  forall rho Σ Σr R x xr T m,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add x T m Σ) ->
    ~ In xr (ctx_names Σr) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho Σ Σr R x xr T m Halpha Hns Hkeys Hfresh Hnocoll
    y Hy z Hz Hneq.
  destruct (ident_eqb y x) eqn:Hxy.
  - apply ident_eqb_eq in Hxy. subst y.
    simpl. rewrite ident_eqb_refl.
    destruct (ident_eqb z x) eqn:Hzx.
    + apply ident_eqb_eq in Hzx. subst z. contradiction.
    + assert (Hno :
        lookup_rename z ((x, xr) :: rho) <> xr).
      { eapply root_env_sctx_keys_named_added_bound_no_collision.
        - exact Halpha.
        - exact Hkeys.
        - exact Hfresh.
        - exact Hz.
        - intros Heq. subst z. rewrite ident_eqb_refl in Hzx.
          discriminate. }
      simpl in Hno. rewrite Hzx in Hno. exact Hno.
  - destruct (ident_eqb z x) eqn:Hzx.
    + apply ident_eqb_eq in Hzx. subst z.
      simpl. rewrite Hxy. rewrite ident_eqb_refl.
      assert (Hno : lookup_rename y ((x, xr) :: rho) <> xr).
      { eapply root_env_sctx_keys_named_added_bound_no_collision.
        - exact Halpha.
        - exact Hkeys.
        - exact Hfresh.
        - exact Hy.
        - intros Heq'. subst y. rewrite ident_eqb_refl in Hxy.
          discriminate. }
      simpl in Hno. rewrite Hxy in Hno.
      intros Heq. apply Hno. symmetry. exact Heq.
    + simpl. rewrite Hxy. rewrite Hzx.
      eapply Hnocoll.
      * eapply root_env_names_remove_preserve_neq.
        -- intros Heq. subst y. rewrite ident_eqb_refl in Hxy.
           discriminate.
        -- exact Hy.
      * eapply root_env_names_remove_preserve_neq.
        -- intros Heq. subst z. rewrite ident_eqb_refl in Hzx.
           discriminate.
        -- exact Hz.
      * exact Hneq.
Qed.

Lemma root_env_remove_shadow_safe_rename_no_collision_on_same_bindings :
  forall rho Σ Σ2 Σr R x xr T m,
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Σ2 ->
    sctx_same_bindings (sctx_add x T m Σ) Σ2 ->
    ~ In xr (ctx_names Σr) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R).
Proof.
  intros rho Σ Σ2 Σr R x xr T m Halpha Hns Hkeys Hsame Hfresh
    Hnocoll.
  eapply root_env_remove_shadow_safe_rename_no_collision_on.
  - exact Halpha.
  - exact Hns.
  - eapply root_env_sctx_keys_named_same_bindings.
    + apply sctx_same_bindings_sym. exact Hsame.
    + exact Hkeys.
  - exact Hfresh.
  - exact Hnocoll.
Qed.

Lemma alpha_rename_params_root_env_remove_match_params_no_collision_on :
  forall rho used ps psr rho' used' R Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add_params ps Σ) ->
    params_names_nodup_b ps = true ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    rename_no_collision_on rho
      (root_env_names (root_env_remove_match_params ps R)) ->
    rename_no_collision_on rho' (root_env_names R).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used' R
    Σ Σr Hrename Hctx Hns Hkeys Hnodup Hctx_used Hrange_used Hnocoll.
  - simpl in Hrename. inversion Hrename; subst.
    simpl in Hnocoll. exact Hnocoll.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnodup.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    set (R_tail := root_env_remove x R).
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ) (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    assert (Hkeys_tail :
      root_env_sctx_keys_named R_tail (sctx_add_params ps Σ)).
    { unfold R_tail.
      eapply root_env_sctx_keys_named_same_bindings.
      - apply sctx_same_bindings_sym.
        eapply sctx_same_bindings_remove_added.
        + apply sctx_same_bindings_refl.
        + apply sctx_same_bindings_refl.
      - apply root_env_sctx_keys_named_remove_binding.
        + exact Hns.
        + exact Hkeys. }
    assert (Hnocoll_tail :
      rename_no_collision_on rho_tail (root_env_names R_tail)).
    { unfold R_tail.
      eapply IH.
      - exact Htail.
      - exact Hctx.
      - apply root_env_no_shadow_remove. exact Hns.
      - exact Hkeys_tail.
      - exact Hnodup_tail.
      - intros y Hy. right. apply Hctx_used. exact Hy.
      - intros y Hy. right. apply Hrange_used. exact Hy.
      - exact Hnocoll. }
    eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings
      with (Σ := sctx_add_params ps Σ)
           (Σ2 := sctx_add x T m (sctx_add_params ps Σ))
           (Σr := sctx_add_params ps_tail Σr).
    + exact Hctx_tail.
    + exact Hns.
    + exact Hkeys.
    + apply sctx_same_bindings_refl.
    + exact Hfresh_tail.
    + exact Hnocoll_tail.
Qed.

Lemma rename_no_collision_on_weaken_names :
  forall rho names names',
    rename_no_collision_on rho names' ->
    (forall x, In x names -> In x names') ->
    rename_no_collision_on rho names.
Proof.
  unfold rename_no_collision_on.
  intros rho names names' Hnocoll Hsub x Hin.
  eapply rename_no_collision_for_weaken_names.
  - apply Hnocoll. apply Hsub. exact Hin.
  - exact Hsub.
Qed.

Lemma alpha_rename_params_rename_no_collision_for_params :
  forall rho used ps psr rho' used' R Σ Σr,
    alpha_rename_params rho used ps = (psr, rho', used') ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R (sctx_add_params ps Σ) ->
    params_names_nodup_b ps = true ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    rename_no_collision_on rho' (root_env_names R) ->
    forall x,
      In x (ctx_names (params_ctx ps)) ->
      rename_no_collision_for rho' x (root_env_names R).
Proof.
  intros rho used ps.
  revert rho used.
  induction ps as [| [m x T] ps IH]; intros rho used psr rho' used'
    R Σ Σr Hrename Hctx Hns Hkeys Hnodup Hctx_used Hrange_used Hnocoll_result
    y Hy.
  - simpl in Hy. contradiction.
  - simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps_tail rho_tail] used_tail] eqn:Htail.
    inversion Hrename; subst; clear Hrename.
    simpl in Hnodup, Hy.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    assert (Hctx_tail :
      ctx_alpha rho_tail (sctx_add_params ps Σ)
        (sctx_add_params ps_tail Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Htail.
      - exact Hctx.
      - intros z Hz. right. apply Hctx_used. exact Hz.
      - intros z Hz. right. apply Hrange_used. exact Hz. }
    assert (Hfresh_tail :
      ~ In (fresh_ident x used) (ctx_names (sctx_add_params ps_tail Σr))).
    { unfold sctx_add_params, ctx_add_params.
      rewrite ctx_names_app.
      intros Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      - eapply alpha_rename_params_names_fresh_used.
        + exact Htail.
        + exact Hin_params.
        + left. reflexivity.
      - apply (fresh_ident_not_in x used).
        apply Hctx_used. exact Hin_tail. }
    destruct Hy as [Hy | Hy].
    + subst y.
      eapply root_env_sctx_keys_named_added_no_collision_for_head.
      * exact Hctx_tail.
      * exact Hkeys.
      * exact Hfresh_tail.
    + unfold rename_no_collision_for.
      intros z Hz Hzy.
      simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        apply negb_true_iff in Hnotin_b.
        apply ident_in_b_false_not_in in Hnotin_b.
        contradiction.
      * destruct (ident_eqb z x) eqn:Hzx.
        -- apply ident_eqb_eq in Hzx. subst z.
           intros Heq.
           assert (Hneq :
             lookup_rename y ((x, fresh_ident x used) :: rho_tail) <>
             fresh_ident x used).
           { eapply ctx_alpha_bound_no_collision_for.
             - exact Hctx_tail.
             - exact Hfresh_tail.
             - unfold sctx_add_params, ctx_add_params.
               rewrite ctx_names_app. apply in_or_app. left. exact Hy.
             - intros Heq_yx. subst y.
               apply negb_true_iff in Hnotin_b.
               apply ident_in_b_false_not_in in Hnotin_b.
               contradiction. }
           apply Hneq. simpl. rewrite Hyx. symmetry. exact Heq.
        -- simpl.
           eapply (IH rho (fresh_ident x used :: used) ps_tail rho_tail
             used' (root_env_remove x R) Σ Σr).
           ++ exact Htail.
           ++ exact Hctx.
           ++ apply root_env_no_shadow_remove. exact Hns.
           ++ eapply root_env_sctx_keys_named_remove_strip_added_same_bindings.
              ** exact Hns.
              ** exact Hkeys.
              ** apply sctx_same_bindings_refl.
           ++ exact Hnodup_tail.
           ++ intros w Hw. right. apply Hctx_used. exact Hw.
           ++ intros w Hw. right. apply Hrange_used. exact Hw.
           ++ eapply rename_no_collision_on_tail_remove; eassumption.
           ++ exact Hy.
           ++ apply root_env_names_remove_preserve_neq.
              ** intros Heq_zx. subst z. rewrite ident_eqb_refl in Hzx.
                 discriminate.
              ** exact Hz.
           ++ exact Hzy.
Qed.


Lemma typed_roots_root_env_names_subset_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    forall x, In x (root_env_names R) -> In x (root_env_names R')) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    forall x, In x (root_env_names R) -> In x (root_env_names R')) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    forall x, In x (root_env_names R) -> In x (root_env_names R')) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    True).
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros; subst; try assumption.
  - eapply H. exact H0.
  - eapply H. exact H0.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - eapply H. exact H0.
  - eapply H. exact H0.
  - eapply H. exact H0.
  - eapply root_env_remove_match_params_preserve_name_not_params.
	    + intros y Hy Heq.
	      subst y.
		      match goal with
		      | Hnone : root_env_lookup_params_none_b _ _ = true |- _ =>
		          pose proof (root_env_lookup_params_none_b_not_in _ _ _ Hnone Hy)
		            as Hnot
		      end.
	      apply Hnot. eapply H. exact H2.
    + eapply H0.
      apply root_env_add_params_roots_same_preserve_name.
      eapply H. exact H2.
  - eapply root_env_names_remove_preserve_neq.
    + intros Heq. subst x0.
      eapply root_env_lookup_none_not_in_names; eauto.
    + eapply H0. simpl. right. eapply H. exact H1.
  - eapply root_env_names_remove_preserve_neq.
    + intros Heq. subst x0.
      eapply root_env_lookup_none_not_in_names; eauto.
    + eapply H0. simpl. right. eapply H. exact H1.
  - eapply H. exact H0.
  - rewrite root_env_names_update. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - rewrite root_env_names_update. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - rewrite root_env_names_update. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - rewrite root_env_names_update. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - eapply H0. eapply H.
    match goal with
    | Hin : In _ (root_env_names _) |- _ => exact Hin
    end.
  - eapply H0. eapply H. exact H1.
  - eapply H0. eapply H. exact H1.
  - exact I.
Qed.

Lemma typed_env_roots_root_env_names_subset :
  forall env Ω n R Σ e T Σ' R' roots x,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros env Ω n R Σ e T Σ' R' roots x Htyped Hin.
  exact (proj1 (typed_roots_root_env_names_subset_mutual env Ω n)
    R Σ e T Σ' R' roots Htyped x Hin).
Qed.

Lemma typed_env_roots_let_body_no_collision_from_removed :
  forall env Ω n rho x roots1 R1 Σ1 e2 T m T2 Σ2 R2 roots2,
    typed_env_roots env Ω n (root_env_add x roots1 R1)
      (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
    root_env_lookup x R1 = None ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
    rename_no_collision_on rho (root_env_names R1).
Proof.
  intros env Ω n rho x roots1 R1 Σ1 e2 T m T2 Σ2 R2 roots2
    Htyped Hlookup Hnocoll.
  eapply rename_no_collision_on_weaken_names.
  - exact Hnocoll.
  - intros y Hin.
    eapply root_env_names_remove_preserve_neq.
    + intros Heq. subst y.
      eapply root_env_lookup_none_not_in_names; eauto.
    + eapply typed_env_roots_root_env_names_subset.
      * exact Htyped.
      * simpl. right. exact Hin.
Qed.

Lemma typed_args_roots_root_env_names_subset :
  forall env Ω n R Σ args ps Σ' R' roots x,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros env Ω n R Σ args ps Σ' R' roots x Htyped Hin.
  exact (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))
    R Σ args ps Σ' R' roots Htyped x Hin).
Qed.

Lemma typed_fields_roots_root_env_names_subset :
  forall env Ω n lts args R Σ fields defs Σ' R' roots x,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots x Htyped Hin.
  exact (proj1 (proj2 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n)))
    lts args R Σ fields defs Σ' R' roots Htyped x Hin).
Qed.

Lemma alpha_rename_typed_env_roots_let_forward :
  forall env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x Tann m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr Tann m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        typed_env_roots env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr Tann m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots env Ω n R Σ (ELet m x Tann e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELet m x Tann e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELet m x Tann e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed; eauto. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr Tann m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Htyped2_r &
        Hctx2_r & HnsRr2 & HRremove & Hroots2 & Hexcl_roots_r &
        Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots env Ω n (root_env_add x roots1 R1)
          (sctx_add x Tann m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TER_Let.
        -- exact Htyped1_r.
        -- match goal with
        | H : ty_compatible_b Ω T1 Tann = true |- _ => exact H
        end.
        -- exact Hlookup_xr_none.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x Tann Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_letinfer_forward :
  forall env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr T1 m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        typed_env_roots env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr T1 m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots env Ω n R Σ (ELetInfer m x e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELetInfer m x e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed; eauto. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 T1 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Htyped2_r &
        Hctx2_r & HnsRr2 & HRremove & Hroots2 & Hexcl_roots_r &
        Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots env Ω n (root_env_add x roots1 R1)
          (sctx_add x T1 m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TER_LetInfer.
        -- exact Htyped1_r.
        -- exact Hlookup_xr_none.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x T1 Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.


Lemma alpha_rename_typed_env_roots_let_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x Tann m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr Tann m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr Tann m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELet m x Tann e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELet m x Tann e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELet m x Tann e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr Tann m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x Tann m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_Let.
        -- exact Htyped1_r.
        -- match goal with
        | H : ty_compatible_b Ω T1 Tann = true |- _ => exact H
        end.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x Tann Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_letinfer_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      (forall y, In y (ctx_names (sctx_add xr T1 m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr T1 m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELetInfer m x e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELetInfer m x e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 T1 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x T1 m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_LetInfer.
        -- exact Htyped1_r.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x T1 Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.


Lemma alpha_rename_typed_env_roots_let_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x Tann m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      root_env_no_shadow R1r ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      rename_no_collision_on rho (root_env_names R1) ->
      rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      root_env_equiv R1r (root_env_rename rho R1) ->
      root_set_equiv roots1r (root_set_rename rho roots1) ->
      root_env_sctx_keys_named R1 Σ1 ->
      root_env_sctx_roots_named R1 Σ1 ->
      root_set_sctx_roots_named roots1 Σ1 ->
      (forall y, In y (ctx_names (sctx_add xr Tann m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr Tann m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELet m x Tann e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELet m x Tann e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELet m x Tann e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x Tann e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow;
      [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [Hroots_env1 _].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_env1. }
  assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [_ Hroots_set1].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_set1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x Tann m Σ1) (sctx_add xr Tann m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr Tann m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x Tann m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact HnsRr1.
    + match goal with
      | H : root_env_lookup x R1 = None |- _ => exact H
      end.
    + match goal with
      | H : roots_exclude x roots1 |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x R1 |- _ => exact H
      end.
    + exact HnocollR1.
    + exact HnocollR'.
    + match goal with
      | H : roots_exclude x roots |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x (root_env_remove x R2) |- _ => exact H
      end.
    + exact HRr1.
    + exact Hroots1.
    + exact HkeysR1.
    + exact HrootsR1.
    + exact Hroots1_named.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_Let.
        -- exact Htyped1_r.
        -- match goal with
        | H : ty_compatible_b Ω T1 Tann = true |- _ => exact H
        end.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x Tann Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_letinfer_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e1 T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall y, In y (ctx_names Σb) -> In y used0) ->
      (forall y, In y (rename_range rho) -> In y used0) ->
      disjoint_names (free_vars_expr e1) (rename_range rho) ->
      alpha_rename_expr rho used0 e1 = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (forall xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
      roots1r T2 Σ2 R2 roots2,
      xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
      used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
      alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
      typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      ctx_alpha ((x, xr) :: rho)
        (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r) ->
      root_env_no_shadow (root_env_add x roots1 R1) ->
      root_env_no_shadow R1r ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      rename_no_collision_on rho (root_env_names R1) ->
      rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      root_env_equiv R1r (root_env_rename rho R1) ->
      root_set_equiv roots1r (root_set_rename rho roots1) ->
      root_env_sctx_keys_named R1 Σ1 ->
      root_env_sctx_roots_named R1 Σ1 ->
      root_set_sctx_roots_named roots1 Σ1 ->
      (forall y, In y (ctx_names (sctx_add xr T1 m Σ1r)) ->
        In y used2) ->
      (forall y, In y (rename_range ((x, xr) :: rho)) -> In y used2) ->
      disjoint_names (free_vars_expr e2) (rename_range ((x, xr) :: rho)) ->
      exists Σ2r R2r roots2r,
        root_env_lookup xr R1r = None /\
        roots_exclude xr roots1r /\
        root_env_excludes xr R1r /\
        typed_env_roots_shadow_safe env Ω n (root_env_add xr roots1r R1r)
          (sctx_add xr T1 m Σ1r) e2r T2 Σ2r R2r roots2r /\
        ctx_alpha ((x, xr) :: rho) Σ2 Σ2r /\
        root_env_no_shadow R2r /\
        root_env_equiv (root_env_remove xr R2r)
          (root_env_rename rho (root_env_remove x R2)) /\
        root_set_equiv roots2r (root_set_rename rho roots2) /\
        roots_exclude xr roots2r /\
        root_env_excludes xr (root_env_remove xr R2r)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (ELetInfer m x e1 e2)
      Tret Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (ELetInfer m x e1 e2))
      (rename_range rho) ->
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er Tret Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr m x e1 e2 er used used'
    Tret Σ' R' roots Hexpr1 Hexpr2 Htyped Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l x (free_vars_expr e1 ++ free_vars_expr e2)
    (rename_range rho) Hdisj) as [Hsafe_x Hdisj_tail].
  destruct (disjoint_names_app_l (free_vars_expr e1) (free_vars_expr e2)
    (rename_range rho) Hdisj_tail) as [Hdisj1 Hdisj2].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1)).
  { reflexivity. }
  set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
  assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1).
  { reflexivity. }
  destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
    as [e2r used3] eqn:He2.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow;
      [eapply typed_env_roots_shadow_safe_roots; eassumption | eassumption]. }
  assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [Hroots_env1 _].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_env1. }
  assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1) as [_ Hroots_set1].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_set1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply typed_env_roots_let_body_no_collision_from_removed.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - eassumption.
    - exact HnocollR'. }
  destruct (Hexpr1 R Rr Σ Σr used e1r used1 T1 Σ1 R1 roots1)
    as [Σr1 [Rr1 [roots1r
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots1]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σr1)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σr1)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σr1)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy]; [left; exact Hy |].
      right. right. apply in_or_app. right.
      apply Hctx_used1. exact Hy. }
    assert (Hrange_used2 : forall y,
      In y (rename_range ((x, xr) :: rho)) -> In y used2).
    { unfold used2. intros y Hy. simpl in Hy.
      destruct Hy as [Hy | Hy].
      - left. exact Hy.
      - right. right. apply in_or_app. right.
        apply Hrange_used1. exact Hy. }
    destruct (Hexpr2 xr used1 used2 e2r used3 T1 roots1 R1 Σ1 Rr1
      Σr1 roots1r Tret Σ2 R2 roots)
      as (Σr2 & Rr2 & roots2r & Hlookup_xr_none & Hinit_roots_r &
        Hinit_env_r & Htyped2_r & Hctx2_r & HnsRr2 & HRremove &
        Hroots2 & Hexcl_roots_r & Hexcl_env_r).
    + exact Hxr.
    + exact Hused2.
    + exact He2.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n (root_env_add x roots1 R1)
          (sctx_add x T1 m Σ1) e2 Tret Σ2 R2 roots |- _ =>
          exact H
      end.
    + exact Hctx_body.
    + apply root_env_no_shadow_add; assumption.
    + exact HnsRr1.
    + match goal with
      | H : root_env_lookup x R1 = None |- _ => exact H
      end.
    + match goal with
      | H : roots_exclude x roots1 |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x R1 |- _ => exact H
      end.
    + exact HnocollR1.
    + exact HnocollR'.
    + match goal with
      | H : roots_exclude x roots |- _ => exact H
      end.
    + match goal with
      | H : root_env_excludes x (root_env_remove x R2) |- _ => exact H
      end.
    + exact HRr1.
    + exact Hroots1.
    + exact HkeysR1.
    + exact HrootsR1.
    + exact Hroots1_named.
    + exact Hctx_used2.
    + exact Hrange_used2.
    + eapply alpha_rename_let_body_disjoint_forward; eauto.
    + change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
        in Hrename.
      change (xr :: x :: free_vars_expr e2 ++ used1) with used2
        in Hrename.
      rewrite He2 in Hrename.
      injection Hrename as <- <-.
      exists (sctx_remove xr Σr2), (root_env_remove xr Rr2), roots2r.
      split; [| split; [| split; [| split]]].
      * eapply TERS_LetInfer.
        -- exact Htyped1_r.
        -- exact Hlookup_xr_none.
        -- exact Hinit_roots_r.
        -- exact Hinit_env_r.
        -- exact Htyped2_r.
        -- assert (Hlookup_xr :
             lookup_rename x ((x, xr) :: rho) = xr).
           { simpl. rewrite ident_eqb_refl. reflexivity. }
           rewrite <- Hlookup_xr.
           eapply ctx_alpha_check_ok_forward.
           ++ exact Hctx2_r.
           ++ eapply alpha_rename_let_bound_safe_forward.
              ** exact Hxr.
              ** exact Hsafe_x.
           ++ match goal with
              | H : sctx_check_ok env x T1 Σ2 = true |- _ => exact H
              end.
        -- exact Hexcl_roots_r.
        -- exact Hexcl_env_r.
      * eapply ctx_alpha_remove_bound. exact Hctx2_r.
      * apply root_env_no_shadow_remove. exact HnsRr2.
      * exact HRremove.
      * exact Hroots2.
Qed.

Lemma alpha_rename_typed_env_roots_if_forward :
  forall env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      typed_env_roots env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots env Ω n R Σ (EIf e1 e2 e3) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EIf e1 e2 e3)) (rename_range rho) ->
  alpha_rename_expr rho used (EIf e1 e2 e3) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l (free_vars_expr e1)
    (free_vars_expr e2 ++ free_vars_expr e3) (rename_range rho))
    as [Hdisj1 Hdisj23].
  { intros x Hin. apply Hdisj. exact Hin. }
  destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
    (rename_range rho) Hdisj23) as [Hdisj2 Hdisj3].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
  destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnsR2 : root_env_no_shadow R').
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnsR3 : root_env_no_shadow R3).
  { eapply typed_env_roots_no_shadow; eassumption. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      eapply typed_env_roots_root_env_names_subset; eassumption. }
  assert (HnocollR3 : rename_no_collision_on rho (root_env_names R3)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      destruct (root_env_lookup x R3) as [roots3_x |] eqn:Hlookup3.
      + match goal with
        | H : root_env_equiv R' R3 |- _ =>
            specialize (H x) as HeqR
        end.
        rewrite Hlookup3 in HeqR.
        destruct (root_env_lookup x R') as [roots2_x |] eqn:Hlookup2;
          try contradiction.
        eapply root_env_lookup_some_in_names. exact Hlookup2.
      + exfalso. eapply root_env_lookup_none_not_in_names; eauto. }
  destruct (Hexpr R Rr Σ Σr used e1 e1r used1 T_cond Σ1 R1 roots_cond)
    as [Σr1 [Rr1 [roots_condr
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots_cond]]]]]]].
  - match goal with
    | H : typed_env_roots env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall x, In x (ctx_names Σr1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hin.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped1_r. }
    assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used1).
    { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
    destruct (Hexpr R1 Rr1 Σ1 Σr1 used1 e2 e2r used2 T2 Σ2 R' roots2)
      as [Σr2 [Rr2 [roots2r
        [Htyped2_r [Hctx2_r [HnsRr2 [HRr2 Hroots2]]]]]]].
    + match goal with
      | H : typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R' roots2 |- _ =>
          exact H
      end.
    + exact Hctx1_r.
    + exact HnsR1.
    + exact HnsRr1.
    + exact HRr1.
    + exact HnocollR1.
    + exact HnocollR'.
    + exact Hctx_used1.
    + exact Hrange_used1.
    + exact Hdisj2.
    + exact He2.
    + assert (Hctx_used2 : forall x, In x (ctx_names Σr1) -> In x used2).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact He2 |].
        apply Hctx_used1. exact Hin. }
      assert (Hrange_used2 : forall x, In x (rename_range rho) -> In x used2).
      { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
      destruct (Hexpr R1 Rr1 Σ1 Σr1 used2 e3 e3r used3 T3 Σ3 R3 roots3)
        as [Σr3 [Rr3 [roots3r
          [Htyped3_r [Hctx3_r [HnsRr3 [HRr3 Hroots3]]]]]]].
      * match goal with
        | H : typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 |- _ =>
            exact H
        end.
      * exact Hctx1_r.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR3.
      * exact Hctx_used2.
      * exact Hrange_used2.
      * exact Hdisj3.
      * exact He3.
      * destruct (ctx_alpha_merge_forward
          rho Σ2 Σr2 Σ3 Σr3 Σ' Hctx2_r Hctx3_r
          ltac:(match goal with
          | H : ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ' |- _ =>
              exact H
          end)) as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4, Rr2, (root_set_union roots2r roots3r).
        split; [| split; [| split; [| split]]].
        -- eapply TER_If.
           ++ exact Htyped1_r.
           ++ match goal with
              | H : ty_core T_cond = TBooleans |- _ => exact H
              end.
           ++ exact Htyped2_r.
           ++ exact Htyped3_r.
           ++ match goal with
              | H : ty_core T2 = ty_core T3 |- _ => exact H
              end.
           ++ exact Hmerge_r.
           ++ eapply root_env_equiv_trans.
              ** exact HRr2.
              ** eapply root_env_equiv_trans.
                 --- eapply root_env_equiv_rename;
                     [ match goal with
                       | H : root_env_equiv R' R3 |- _ => exact H
                       end
                     | exact HnsR2
                     | exact HnsR3
                     | exact HnocollR'
                     | exact HnocollR3 ].
                 --- apply root_env_equiv_sym. exact HRr3.
        -- exact Hctx_merge.
        -- exact HnsRr2.
        -- exact HRr2.
        -- eapply root_set_equiv_trans.
           ++ apply root_set_union_equiv; eassumption.
           ++ apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_env_roots_var_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (EVar x)) (rename_range rho) ->
    alpha_rename_expr rho used (EVar x) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TERS_Var_Copy.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- apply Hdisj. simpl. left. reflexivity.
        -- match goal with
           | H : typed_place_env_structural env _ (PVar x) T |- _ =>
               exact H
           end.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe : ~ In x (rename_range rho)).
    { apply Hdisj. simpl. left. reflexivity. }
    destruct (ctx_alpha_consume_path_forward
      rho _ Σr x [] Σ' Hctx Hsafe
      ltac:(match goal with
        | H : sctx_consume_path _ x [] = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TERS_Var_Move.
      * change (typed_place_env_structural env Σr
          (PVar (lookup_rename x rho)) T) with
          (typed_place_env_structural env Σr
            (rename_place rho (PVar x)) T).
        eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_var_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall y, In y (ctx_names Σr) -> In y used) ->
    (forall y, In y (rename_range rho) -> In y used) ->
    disjoint_names (free_vars_expr (EVar x)) (rename_range rho) ->
    alpha_rename_expr rho used (EVar x) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr x er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_var_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_place_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EPlace p)) (rename_range rho) ->
    alpha_rename_expr rho used (EPlace p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. injection Hrename as <- <-.
  set (R0 := R) in *.
  set (Rr0 := Rr) in *.
  inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr, Rr0, rootsr. repeat split.
    + eapply TERS_Place_Copy.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T = UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hlookup_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    destruct (ctx_alpha_consume_path_forward
      rho Σ Σr x path Σ' Hctx Hsafe_x
      ltac:(match goal with
        | H : sctx_consume_path Σ x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr' [Hconsume_r Hctx_r]].
    destruct (root_env_equiv_rename_lookup_forward rho R0 Rr0 x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R0 = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_r Hroots_r]].
    exists Σr', Rr0, rootsr. repeat split.
    + eapply TERS_Place_Move.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T <> UUnrestricted |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * exact Hconsume_r.
      * exact Hlookup_r.
    + exact Hctx_r.
    + exact HnsRr.
    + exact HRr.
    + apply Hroots_r.
    + apply Hroots_r.
Qed.

Lemma alpha_rename_typed_env_roots_place_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EPlace p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EPlace p)) (rename_range rho) ->
    alpha_rename_expr rho used (EPlace p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr _ _ HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply alpha_rename_typed_env_roots_place_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_borrow_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EBorrow rk p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    rename_no_collision_on rho
      (root_env_all_store_names R ++ root_set_store_names (root_of_place p)) ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EBorrow rk p)) (rename_range rho) ->
    alpha_rename_expr rho used (EBorrow rk p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR' HnocollResolved
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename. destruct rk; injection Hrename as <- <-;
    inversion Htyped; subst.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    exists Σr, Rr, (root_of_place (rename_place rho p)). repeat split.
    + eapply TERS_BorrowShared.
      eapply alpha_rename_typed_place_env_structural_forward; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + rewrite root_of_place_rename_place. simpl. tauto.
    + rewrite root_of_place_rename_place. simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TERS_BorrowShared_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hresolved : place_resolved_roots ?Rsrc p = Some roots,
      Hns : root_env_no_shadow ?Rsrc,
      Heq : root_env_equiv Rr (root_env_rename rho ?Rsrc) |- _ =>
        destruct (place_resolved_roots_rename_no_shadow_equiv
          rho Rsrc Rr p roots Hns HnsRr Heq HnocollResolved Hresolved)
          as [rootsr [Hresolved_r Hrootsr]]
    end.
    match goal with
    | Hlookup : root_env_lookup ?x ?Rsrc = Some ?roots_x,
      Heq : root_env_equiv Rr (root_env_rename rho ?Rsrc) |- _ =>
        destruct (root_env_equiv_rename_lookup_forward rho Rsrc Rr x roots_x
          Heq HnocollR Hlookup) as [roots_xr [Hlookup_xr Hroots_xr]]
    end.
    assert (Hsingle_xr :
      singleton_store_root roots_xr = Some (lookup_rename x rho)).
    { rewrite (singleton_store_root_equiv roots_xr
        (root_set_rename rho roots_x) Hroots_xr).
      apply singleton_store_root_rename_some.
      match goal with Hsingle_x : singleton_store_root roots_x = Some x |- _ =>
        exact Hsingle_x
      end. }
    exists Σr, Rr, rootsr. repeat split.
    + eapply TERS_BorrowShared_Resolved.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * exact Hresolved_r.
      * rewrite (singleton_store_root_equiv rootsr (root_set_rename rho roots) Hrootsr).
        apply singleton_store_root_rename_some.
        match goal with Hsingle : singleton_store_root roots = Some _ |- _ =>
          exact Hsingle
        end.
      * exact Hlookup_xr.
      * exact Hsingle_xr.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hsafe_x : ~ In x (rename_range rho)).
    { rewrite <- (place_path_root p x path
        ltac:(match goal with
          | H : place_path p = Some (x, path) |- _ => exact H
          end)).
      exact Hsafe_root. }
    exists Σr, Rr, [RStore (lookup_rename x rho)]. repeat split.
    + eapply TERS_BorrowUnique.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply ctx_alpha_lookup_mut_forward_any; eauto.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + simpl. tauto.
    + simpl. tauto.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hpath : place_path p = None,
      Hborrow : place_borrow_roots ?R0 p = Some roots,
      Heq : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
        assert (Hlookup_root :
          root_env_lookup (root_provenance_place_name p) R0 = Some roots)
          by (rewrite <- (place_borrow_roots_indirect R0 p Hpath); exact Hborrow);
        destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
          (root_provenance_place_name p) roots Heq HnocollR Hlookup_root)
          as [rootsr [Hlookup_r Hrootsr]]
    end.
    exists Σr, Rr, rootsr. repeat split.
    + eapply TERS_BorrowUnique_Indirect.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
      * rewrite (place_borrow_roots_indirect Rr (rename_place rho p)).
        -- rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    match goal with
    | Hresolved : place_resolved_roots ?Rsrc p = Some roots,
      Hns : root_env_no_shadow ?Rsrc,
      Heq : root_env_equiv Rr (root_env_rename rho ?Rsrc) |- _ =>
        destruct (place_resolved_roots_rename_no_shadow_equiv
          rho Rsrc Rr p roots Hns HnsRr Heq HnocollResolved Hresolved)
          as [rootsr [Hresolved_r Hrootsr]]
    end.
    match goal with
    | Hlookup : root_env_lookup ?x ?Rsrc = Some ?roots_x,
      Heq : root_env_equiv Rr (root_env_rename rho ?Rsrc) |- _ =>
        destruct (root_env_equiv_rename_lookup_forward rho Rsrc Rr x roots_x
          Heq HnocollR Hlookup) as [roots_xr [Hlookup_xr Hroots_xr]]
    end.
    assert (Hsingle_xr :
      singleton_store_root roots_xr = Some (lookup_rename x rho)).
    { rewrite (singleton_store_root_equiv roots_xr
        (root_set_rename rho roots_x) Hroots_xr).
      apply singleton_store_root_rename_some.
      match goal with Hsingle_x : singleton_store_root roots_x = Some x |- _ =>
        exact Hsingle_x
      end. }
    exists Σr, Rr, rootsr. repeat split.
    + eapply TERS_BorrowUnique_Resolved.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
      * exact Hresolved_r.
      * rewrite (singleton_store_root_equiv rootsr (root_set_rename rho roots) Hrootsr).
        apply singleton_store_root_rename_some.
        match goal with Hsingle : singleton_store_root roots = Some _ |- _ =>
          exact Hsingle
        end.
      * exact Hlookup_xr.
      * exact Hsingle_xr.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + apply Hrootsr.
    + apply Hrootsr.
  - assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
    { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
    assert (Hchain_r :
      place_resolved_write_writable_chain env Rr Σr (rename_place rho p)).
    { eapply place_resolved_write_writable_chain_rename.
      - apply root_env_equiv_sym. exact HRr.
      - exact HnocollR.
      - exact Hctx.
      - exact Hsafe_root.
      - eassumption. }
    assert (Htarget_r :
      place_resolved_write_target Rr (rename_place rho p) =
        Some (lookup_rename x rho)).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HRr.
      - apply place_resolved_write_target_rename.
        + exact HnocollR.
        + eassumption. }
    exists Σr, Rr, [RStore (lookup_rename x rho)]. repeat split.
    + eapply TERS_BorrowUnique_ResolvedTarget.
      * eapply alpha_rename_typed_place_env_structural_forward.
        -- exact Hctx.
        -- exact Hsafe_root.
        -- eassumption.
      * match goal with Hpath : place_path p = None |- _ =>
          apply place_path_rename_place_none; exact Hpath
        end.
      * eapply alpha_rename_place_under_unique_ref_structural_forward.
        -- exact Hctx.
        -- exact Hsafe_root.
        -- eassumption.
      * exact Hchain_r.
      * exact Htarget_r.
    + exact Hctx.
    + exact HnsRr.
    + exact HRr.
    + simpl. tauto.
    + simpl. tauto.
Qed.
Lemma alpha_rename_typed_env_roots_borrow_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EBorrow rk p) T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EBorrow rk p)) (rename_range rho) ->
    alpha_rename_expr rho used (EBorrow rk p) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr rk p er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  assert (Hplace_roots : root_set_sctx_roots_named (root_of_place p) Σ).
  { inversion Htyped; subst; eapply root_of_place_sctx_roots_named; eassumption. }
  assert (HnocollResolved : rename_no_collision_on rho
      (root_env_all_store_names R ++ root_set_store_names (root_of_place p))).
  { eapply rename_no_collision_on_weaken.
    - eapply ctx_alpha_no_collision_on_any. exact Hctx.
    - intros x Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + eapply (root_env_all_store_names_sctx_names R Σ x); eassumption.
      + eapply (root_set_store_names_sctx_names (root_of_place p) Σ x); eassumption. }
  eapply alpha_rename_typed_env_roots_borrow_shadow_safe_forward;
    eassumption.
Qed.

Lemma alpha_rename_typed_env_roots_replace_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EReplace p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EReplace p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ1 R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (ctx_alpha_restore_path_forward
      rho Σ1 Σr1 x path Σ' Hctx_new_r Hsafe_x
      ltac:(match goal with
        | H : sctx_restore_path Σ1 x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr2 [Hrestore_r Hctx_restore]].
    destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_result_r Hroots_result]].
    destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr2,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Replace_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Hlookup_result_r.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
      * exact Hrestore_r.
    + exact Hctx_restore.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + exact Hroots_result.
  - assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { rewrite <- (root_env_names_update x
        (root_set_union roots_old roots_new) R1).
      exact HnocollR'. }
    destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
      as [Σr1 [Rr1 [roots_newr
        [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
          exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_new.
    + exact Hnew.
    + assert (Htarget_r :
        place_resolved_write_target Rr (rename_place rho p) =
        Some (lookup_rename x rho)).
      { eapply place_resolved_write_target_equiv.
        - apply root_env_equiv_sym. exact HRr.
        - apply place_resolved_write_target_rename.
          + exact HnocollR.
          + match goal with
            | H : place_resolved_write_target R p = Some x |- _ => exact H
            end. }
      destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
        HRr HnocollR
        ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [roots_resultr [Hlookup_result_r Hroots_result]].
      destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
        HRr1 HnocollR1
        ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
      exists Σr1,
        (root_env_update (lookup_rename x rho)
          (root_set_union roots_oldr roots_newr) Rr1),
        roots_resultr.
      split; [| split; [| split; [| split]]].
      * eapply TERS_Replace_Resolved.
        -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
        -- eapply place_resolved_write_writable_chain_rename;
           [ apply root_env_equiv_sym; exact HRr
           | exact HnocollR
           | exact Hctx
           | exact Hdisj_p
           | eassumption ].
        -- exact Htarget_r.
        -- exact Hlookup_result_r.
        -- eapply ctx_alpha_lookup_mut_forward_any; eauto.
        -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
        -- exact Htyped_new_r.
        -- exact Hlookup_old_r.
        -- match goal with
           | H : ty_compatible_b Ω T_new T = true |- _ => exact H
           end.
      * exact Hctx_new_r.
      * apply root_env_no_shadow_update. exact HnsRr1.
      * eapply root_env_equiv_update_rename_union; eauto.
        apply HnocollR1. eapply root_env_lookup_some_in_names.
        match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end.
      * exact Hroots_result.
Qed.

Lemma alpha_rename_typed_env_roots_replace_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EReplace p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EReplace p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EReplace p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ1 R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ1 R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (ctx_alpha_restore_path_forward
      rho Σ1 Σr1 x path Σ' Hctx_new_r Hsafe_x
      ltac:(match goal with
        | H : sctx_restore_path Σ1 x path = infer_ok Σ' |- _ => exact H
        end))
      as [Σr2 [Hrestore_r Hctx_restore]].
    destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
      HRr HnocollR
      ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [rootsr [Hlookup_result_r Hroots_result]].
    destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr2,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Replace_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Hlookup_result_r.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
      * exact Hrestore_r.
    + exact Hctx_restore.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + exact Hroots_result.
  - assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { rewrite <- (root_env_names_update x
        (root_set_union roots_old roots_new) R1).
      exact HnocollR'. }
    destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
      as [Σr1 [Rr1 [roots_newr
        [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
          exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact Hkeys.
    + exact Hroots.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_new.
    + exact Hnew.
    + assert (Htarget_r :
        place_resolved_write_target Rr (rename_place rho p) =
        Some (lookup_rename x rho)).
      { eapply place_resolved_write_target_equiv.
        - apply root_env_equiv_sym. exact HRr.
        - apply place_resolved_write_target_rename.
          + exact HnocollR.
          + match goal with
            | H : place_resolved_write_target R p = Some x |- _ => exact H
            end. }
      destruct (root_env_equiv_rename_lookup_forward rho R Rr x roots
        HRr HnocollR
        ltac:(match goal with
        | H : root_env_lookup x R = Some roots |- _ => exact H
        end)) as [roots_resultr [Hlookup_result_r Hroots_result]].
      destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
        HRr1 HnocollR1
        ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
      exists Σr1,
        (root_env_update (lookup_rename x rho)
          (root_set_union roots_oldr roots_newr) Rr1),
        roots_resultr.
      split; [| split; [| split; [| split]]].
      * eapply TERS_Replace_Resolved.
        -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
        -- match goal with Hpath : place_path p = None |- _ =>
             apply place_path_rename_place_none; exact Hpath
           end.
        -- eapply place_resolved_write_writable_chain_rename;
           [ apply root_env_equiv_sym; exact HRr
           | exact HnocollR
           | exact Hctx
           | exact Hdisj_p
           | eassumption ].
        -- exact Htarget_r.
        -- exact Hlookup_result_r.
        -- eapply ctx_alpha_lookup_mut_forward_any; eauto.
        -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
        -- exact Htyped_new_r.
        -- exact Hlookup_old_r.
        -- match goal with
           | H : ty_compatible_b Ω T_new T = true |- _ => exact H
           end.
      * exact Hctx_new_r.
      * apply root_env_no_shadow_update. exact HnsRr1.
      * eapply root_env_equiv_update_rename_union; eauto.
        apply HnocollR1. eapply root_env_lookup_some_in_names.
        match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end.
      * exact Hroots_result.
Qed.
Lemma alpha_rename_typed_env_roots_assign_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EAssign p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EAssign p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr1,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Assign_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T_old <> ULinear |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
    + exact Hctx_new_r.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + apply root_set_equiv_refl.
  - assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { rewrite <- (root_env_names_update x
        (root_set_union roots_old roots_new) R1).
      exact HnocollR'. }
    destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
      as [Σr1 [Rr1 [roots_newr
        [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ => exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_new.
    + exact Hnew.
    + assert (Htarget_r : place_resolved_write_target Rr (rename_place rho p) = Some (lookup_rename x rho)).
      { eapply place_resolved_write_target_equiv.
        - apply root_env_equiv_sym. exact HRr.
        - apply place_resolved_write_target_rename.
          + exact HnocollR.
          + match goal with H : place_resolved_write_target R p = Some x |- _ => exact H end. }
      destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old HRr1 HnocollR1
        ltac:(match goal with H : root_env_lookup x R1 = Some roots_old |- _ => exact H end))
        as [roots_oldr [Hlookup_old_r Hroots_old]].
      exists Σr1, (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1), [].
      split; [| split; [| split; [| split]]].
      * eapply TERS_Assign_Resolved.
        -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
        -- match goal with H : ty_usage T_old <> ULinear |- _ => exact H end.
        -- match goal with Hpath : place_path p = None |- _ => apply place_path_rename_place_none; exact Hpath end.
        -- eapply place_resolved_write_writable_chain_rename;
           [ apply root_env_equiv_sym; exact HRr
           | exact HnocollR
           | exact Hctx
           | exact Hdisj_p
           | eassumption ].
        -- exact Htarget_r.
        -- eapply ctx_alpha_lookup_mut_forward_any; eauto.
        -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
        -- exact Htyped_new_r.
        -- exact Hlookup_old_r.
        -- match goal with H : ty_compatible_b Ω T_new T_old = true |- _ => exact H end.
      * exact Hctx_new_r.
      * apply root_env_no_shadow_update. exact HnsRr1.
      * eapply root_env_equiv_update_rename_union; eauto.
        apply HnocollR1. eapply root_env_lookup_some_in_names.
        match goal with H : root_env_lookup x R1 = Some roots_old |- _ => exact H end.
      * apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_assign_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e_new T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e_new) (rename_range rho) ->
      alpha_rename_expr rho used0 e_new = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
    typed_env_roots_shadow_safe env Ω n R Σ (EAssign p e_new)
      T Σ' R' roots ->
    ctx_alpha rho Σ Σr ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R') ->
    (forall x, In x (ctx_names Σr) -> In x used) ->
    (forall x, In x (rename_range rho) -> In x used) ->
    disjoint_names (free_vars_expr (EAssign p e_new)) (rename_range rho) ->
    alpha_rename_expr rho used (EAssign p e_new) = (er, used') ->
    exists Σr' Rr' rootsr,
      typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
      ctx_alpha rho Σ' Σr' /\
      root_env_no_shadow Rr' /\
      root_env_equiv Rr' (root_env_rename rho R') /\
      root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr p e_new er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_cons_l (place_name p) (free_vars_expr e_new)
    (rename_range rho) Hdisj) as [Hdisj_p Hdisj_new].
  destruct (alpha_rename_expr rho used e_new)
    as [er_new used_new] eqn:Hnew.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (Hsafe_p : ~ In (place_root p) (rename_range rho)).
  { rewrite <- place_name_root. exact Hdisj_p. }
  assert (Hsafe_x : ~ In x (rename_range rho)).
  { rewrite <- (place_path_root p x path
      ltac:(match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end)).
    exact Hsafe_p. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { rewrite <- (root_env_names_update x
      (root_set_union roots_old roots_new) R1).
    exact HnocollR'. }
  destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
    as [Σr1 [Rr1 [roots_newr
      [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj_new.
  - exact Hnew.
  - destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old
      HRr1 HnocollR1
      ltac:(match goal with
        | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
        end)) as [roots_oldr [Hlookup_old_r Hroots_old]].
    exists Σr1,
      (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1),
      [].
    split; [| split; [| split; [| split]]].
    + eapply TERS_Assign_Path.
      * eapply alpha_rename_typed_place_env_structural_forward; eauto.
      * match goal with
        | H : ty_usage T_old <> ULinear |- _ => exact H
        end.
      * eapply place_path_rename_place_some.
        match goal with
        | H : place_path p = Some (x, path) |- _ => exact H
        end.
      * eapply alpha_rename_writable_place_env_structural_forward; eauto.
      * exact Htyped_new_r.
      * exact Hlookup_old_r.
      * match goal with
        | H : ty_compatible_b Ω T_new T_old = true |- _ => exact H
        end.
      * eapply ctx_alpha_path_available_forward; eauto.
    + exact Hctx_new_r.
    + apply root_env_no_shadow_update. exact HnsRr1.
    + eapply root_env_equiv_update_rename_union; eauto.
      apply HnocollR1. eapply root_env_lookup_some_in_names.
      match goal with
      | H : root_env_lookup x R1 = Some roots_old |- _ => exact H
      end.
    + apply root_set_equiv_refl.
  - assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { rewrite <- (root_env_names_update x
        (root_set_union roots_old roots_new) R1).
      exact HnocollR'. }
    destruct (Hexpr R Rr Σ Σr used er_new used_new T_new Σ' R1 roots_new)
      as [Σr1 [Rr1 [roots_newr
        [Htyped_new_r [Hctx_new_r [HnsRr1 [HRr1 Hroots_new]]]]]]].
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e_new T_new Σ' R1 roots_new |- _ => exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact Hkeys.
    + exact Hroots.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_new.
    + exact Hnew.
    + assert (Htarget_r : place_resolved_write_target Rr (rename_place rho p) = Some (lookup_rename x rho)).
      { eapply place_resolved_write_target_equiv.
        - apply root_env_equiv_sym. exact HRr.
        - apply place_resolved_write_target_rename.
          + exact HnocollR.
          + match goal with H : place_resolved_write_target R p = Some x |- _ => exact H end. }
      destruct (root_env_equiv_rename_lookup_forward rho R1 Rr1 x roots_old HRr1 HnocollR1
        ltac:(match goal with H : root_env_lookup x R1 = Some roots_old |- _ => exact H end))
        as [roots_oldr [Hlookup_old_r Hroots_old]].
      exists Σr1, (root_env_update (lookup_rename x rho)
        (root_set_union roots_oldr roots_newr) Rr1), [].
      split; [| split; [| split; [| split]]].
      * eapply TERS_Assign_Resolved.
        -- eapply alpha_rename_typed_place_env_structural_forward; eauto.
        -- match goal with H : ty_usage T_old <> ULinear |- _ => exact H end.
        -- match goal with Hpath : place_path p = None |- _ => apply place_path_rename_place_none; exact Hpath end.
        -- eapply place_resolved_write_writable_chain_rename;
           [ apply root_env_equiv_sym; exact HRr
           | exact HnocollR
           | exact Hctx
           | exact Hdisj_p
           | eassumption ].
        -- exact Htarget_r.
        -- eapply ctx_alpha_lookup_mut_forward_any; eauto.
        -- eapply alpha_rename_writable_place_env_structural_forward; eauto.
        -- exact Htyped_new_r.
        -- exact Hlookup_old_r.
        -- match goal with H : ty_compatible_b Ω T_new T_old = true |- _ => exact H end.
      * exact Hctx_new_r.
      * apply root_env_no_shadow_update. exact HnsRr1.
      * eapply root_env_equiv_update_rename_union; eauto.
        apply HnocollR1. eapply root_env_lookup_some_in_names.
        match goal with H : root_env_lookup x R1 = Some roots_old |- _ => exact H end.
      * apply root_set_equiv_refl.
Qed.

Lemma alpha_rename_typed_env_roots_if_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (EIf e1 e2 e3)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EIf e1 e2 e3)) (rename_range rho) ->
  alpha_rename_expr rho used (EIf e1 e2 e3) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l (free_vars_expr e1)
    (free_vars_expr e2 ++ free_vars_expr e3) (rename_range rho))
    as [Hdisj1 Hdisj23].
  { intros x Hin. apply Hdisj. exact Hin. }
  destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
    (rename_range rho) Hdisj23) as [Hdisj2 Hdisj3].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
  destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR. }
  assert (HnsR2 : root_env_no_shadow R').
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnsR3 : root_env_no_shadow R3).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      eapply typed_env_roots_root_env_names_subset.
      + eapply typed_env_roots_shadow_safe_roots. eassumption.
      + exact Hin. }
  assert (HnocollR3 : rename_no_collision_on rho (root_env_names R3)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      destruct (root_env_lookup x R3) as [roots3_x |] eqn:Hlookup3.
      + match goal with
        | H : root_env_equiv R' R3 |- _ =>
            specialize (H x) as HeqR
        end.
        rewrite Hlookup3 in HeqR.
        destruct (root_env_lookup x R') as [roots2_x |] eqn:Hlookup2;
          try contradiction.
        eapply root_env_lookup_some_in_names. exact Hlookup2.
      + exfalso. eapply root_env_lookup_none_not_in_names; eauto. }
  destruct (Hexpr R Rr Σ Σr used e1 e1r used1 T_cond Σ1 R1 roots_cond)
    as [Σr1 [Rr1 [roots_condr
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots_cond]]]]]]].
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall x, In x (ctx_names Σr1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hin.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used1).
    { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
    destruct (Hexpr R1 Rr1 Σ1 Σr1 used1 e2 e2r used2 T2 Σ2 R' roots2)
      as [Σr2 [Rr2 [roots2r
        [Htyped2_r [Hctx2_r [HnsRr2 [HRr2 Hroots2]]]]]]].
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R' roots2 |- _ =>
          exact H
      end.
    + exact Hctx1_r.
    + exact HnsR1.
    + exact HnsRr1.
    + exact HRr1.
    + exact HnocollR1.
    + exact HnocollR'.
    + exact Hctx_used1.
    + exact Hrange_used1.
    + exact Hdisj2.
    + exact He2.
    + assert (Hctx_used2 : forall x, In x (ctx_names Σr1) -> In x used2).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact He2 |].
        apply Hctx_used1. exact Hin. }
      assert (Hrange_used2 : forall x, In x (rename_range rho) -> In x used2).
      { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
      destruct (Hexpr R1 Rr1 Σ1 Σr1 used2 e3 e3r used3 T3 Σ3 R3 roots3)
        as [Σr3 [Rr3 [roots3r
          [Htyped3_r [Hctx3_r [HnsRr3 [HRr3 Hroots3]]]]]]].
      * match goal with
        | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 |- _ =>
            exact H
        end.
      * exact Hctx1_r.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR3.
      * exact Hctx_used2.
      * exact Hrange_used2.
      * exact Hdisj3.
      * exact He3.
      * destruct (ctx_alpha_merge_forward
          rho Σ2 Σr2 Σ3 Σr3 Σ' Hctx2_r Hctx3_r
          ltac:(match goal with
          | H : ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ' |- _ =>
              exact H
          end)) as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4, Rr2, (root_set_union roots2r roots3r).
        split; [| split; [| split; [| split]]].
        -- eapply TERS_If.
           ++ exact Htyped1_r.
           ++ match goal with
              | H : ty_core T_cond = TBooleans |- _ => exact H
              end.
           ++ exact Htyped2_r.
           ++ exact Htyped3_r.
           ++ match goal with
              | H : ty_core T2 = ty_core T3 |- _ => exact H
              end.
           ++ exact Hmerge_r.
           ++ eapply root_env_equiv_trans.
              ** exact HRr2.
              ** eapply root_env_equiv_trans.
                 --- eapply root_env_equiv_rename;
                     [ match goal with
                       | H : root_env_equiv R' R3 |- _ => exact H
                       end
                     | exact HnsR2
                     | exact HnsR3
                     | exact HnocollR'
                     | exact HnocollR3 ].
                 --- apply root_env_equiv_sym. exact HRr3.
        -- exact Hctx_merge.
        -- exact HnsRr2.
        -- exact HRr2.
        -- eapply root_set_equiv_trans.
           ++ apply root_set_union_equiv; eassumption.
           ++ apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_env_roots_if_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      expr_size e < expr_size (EIf e1 e2 e3) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T0 Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0
          Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_env_roots_shadow_safe env Ω n R Σ (EIf e1 e2 e3)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EIf e1 e2 e3)) (rename_range rho) ->
  alpha_rename_expr rho used (EIf e1 e2 e3) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct (disjoint_names_app_l (free_vars_expr e1)
    (free_vars_expr e2 ++ free_vars_expr e3) (rename_range rho))
    as [Hdisj1 Hdisj23].
  { intros x Hin. apply Hdisj. exact Hin. }
  destruct (disjoint_names_app_l (free_vars_expr e2) (free_vars_expr e3)
    (rename_range rho) Hdisj23) as [Hdisj2 Hdisj3].
  destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
  destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
  destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  assert (HnsR1 : root_env_no_shadow R1).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR. }
  assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
      as [Hroots_env _].
    destruct (Hroots_env R Σ e1 T_cond Σ1 R1 roots_cond)
      as [Hroots_env1 _].
    - match goal with
      | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
          exact H
      end.
    - exact HnsR.
    - exact Hroots.
    - exact Hroots_env1. }
  assert (HnsR2 : root_env_no_shadow R').
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnsR3 : root_env_no_shadow R3).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. eassumption.
    - exact HnsR1. }
  assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      eapply typed_env_roots_root_env_names_subset.
      + eapply typed_env_roots_shadow_safe_roots. eassumption.
      + exact Hin. }
  assert (HnocollR3 : rename_no_collision_on rho (root_env_names R3)).
  { eapply rename_no_collision_on_weaken_names.
    - exact HnocollR'.
    - intros x Hin.
      destruct (root_env_lookup x R3) as [roots3_x |] eqn:Hlookup3.
      + match goal with
        | H : root_env_equiv R' R3 |- _ =>
            specialize (H x) as HeqR
        end.
        rewrite Hlookup3 in HeqR.
        destruct (root_env_lookup x R') as [roots2_x |] eqn:Hlookup2;
          try contradiction.
        eapply root_env_lookup_some_in_names. exact Hlookup2.
      + exfalso. eapply root_env_lookup_none_not_in_names; eauto. }
  destruct (Hexpr R Rr Σ Σr used e1 e1r used1 T_cond Σ1 R1 roots_cond)
    as [Σr1 [Rr1 [roots_condr
      [Htyped1_r [Hctx1_r [HnsRr1 [HRr1 Hroots_cond]]]]]]].
  - simpl; lia.
  - match goal with
    | H : typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1 roots_cond |- _ =>
        exact H
    end.
  - exact Hctx.
  - exact HnsR.
  - exact HnsRr.
  - exact HRr.
  - exact Hkeys.
  - exact Hroots.
  - exact HnocollR.
  - exact HnocollR1.
  - exact Hctx_used.
  - exact Hrange_used.
  - exact Hdisj1.
  - exact He1.
  - assert (Hctx_used1 : forall x, In x (ctx_names Σr1) -> In x used1).
    { intros x Hin.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
        + exact Hin.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1_r. }
    assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used1).
    { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
    destruct (Hexpr R1 Rr1 Σ1 Σr1 used1 e2 e2r used2 T2 Σ2 R' roots2)
      as [Σr2 [Rr2 [roots2r
        [Htyped2_r [Hctx2_r [HnsRr2 [HRr2 Hroots2]]]]]]].
    + simpl; lia.
    + match goal with
      | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e2 T2 Σ2 R' roots2 |- _ =>
          exact H
      end.
    + exact Hctx1_r.
    + exact HnsR1.
    + exact HnsRr1.
    + exact HRr1.
    + exact HkeysR1.
    + exact HrootsR1.
    + exact HnocollR1.
    + exact HnocollR'.
    + exact Hctx_used1.
    + exact Hrange_used1.
    + exact Hdisj2.
    + exact He2.
    + assert (Hctx_used2 : forall x, In x (ctx_names Σr1) -> In x used2).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact He2 |].
        apply Hctx_used1. exact Hin. }
      assert (Hrange_used2 : forall x, In x (rename_range rho) -> In x used2).
      { intros x Hin. eapply alpha_rename_expr_used_extends; eauto. }
      destruct (Hexpr R1 Rr1 Σ1 Σr1 used2 e3 e3r used3 T3 Σ3 R3 roots3)
        as [Σr3 [Rr3 [roots3r
          [Htyped3_r [Hctx3_r [HnsRr3 [HRr3 Hroots3]]]]]]].
      * simpl; lia.
      * match goal with
        | H : typed_env_roots_shadow_safe env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 |- _ =>
            exact H
        end.
      * exact Hctx1_r.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR3.
      * exact Hctx_used2.
      * exact Hrange_used2.
      * exact Hdisj3.
      * exact He3.
      * destruct (ctx_alpha_merge_forward
          rho Σ2 Σr2 Σ3 Σr3 Σ' Hctx2_r Hctx3_r
          ltac:(match goal with
          | H : ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ' |- _ =>
              exact H
          end)) as [Σr4 [Hmerge_r Hctx_merge]].
        exists Σr4, Rr2, (root_set_union roots2r roots3r).
        split; [| split; [| split; [| split]]].
        -- eapply TERS_If.
           ++ exact Htyped1_r.
           ++ match goal with
              | H : ty_core T_cond = TBooleans |- _ => exact H
              end.
           ++ exact Htyped2_r.
           ++ exact Htyped3_r.
           ++ match goal with
              | H : ty_core T2 = ty_core T3 |- _ => exact H
              end.
           ++ exact Hmerge_r.
           ++ eapply root_env_equiv_trans.
              ** exact HRr2.
              ** eapply root_env_equiv_trans.
                 --- eapply root_env_equiv_rename;
                     [ match goal with
                       | H : root_env_equiv R' R3 |- _ => exact H
                       end
                     | exact HnsR2
                     | exact HnsR3
                     | exact HnocollR'
                     | exact HnocollR3 ].
                 --- apply root_env_equiv_sym. exact HRr3.
        -- exact Hctx_merge.
        -- exact HnsRr2.
        -- exact HRr2.
        -- eapply root_set_equiv_trans.
           ++ apply root_set_union_equiv; eassumption.
           ++ apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_args_roots_forward :
  forall env Ω n rho R Rr Σ Σr args argsr used used' ps psr Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e args ->
      typed_env_roots env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range rho) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exists Σr' Rr' rootsr,
    typed_args_roots env Ω n Rr Σr argsr psr Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots).
Proof.
  intros env Ω n rho R Rr Σ Σr args.
  revert R Rr Σ Σr.
  induction args as [| arg rest IH]; intros R Rr Σ Σr argsr used used'
    ps psr Σ' R' roots Hexpr Htyped_args Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hparams Hrename;
    simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr, Rr, []. repeat split; try constructor; assumption.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range rho) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr rho used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct ps as [| p ps_tail]; [inversion Htyped_args|].
    destruct psr as [| pr psr_tail]; [inversion Hparams|].
    inversion Htyped_args; subst.
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_args_roots_root_env_names_subset; eassumption. }
    destruct (Hexpr R Rr Σ Σr used arg ar used1 T_e Σ1 R1 roots0)
      as [Σr1 [Rr1 [rootsr0
        [Htyped_arg_r [Hctx_arg [HnsRr1 [HRr1 Hroots0]]]]]]].
    + left. reflexivity.
    + assumption.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range rho) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH R1 Rr1 Σ1 Σr1 restr used1 used2 ps_tail psr_tail
        Σ' R' roots_rest)
        as [Σr2 [Rr2 [rootsr_rest
          [Htyped_tail_r [Hctx_tail [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      * intros R0 R0r Σa Σb used0 e er used_tail T Σa' R0' roots_e
          Hin Htyped_e Halpha HnsR0 HnsR0r HR0r HnocollR0 HnocollR0'
          Hcu Hru Hd Hr.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Htyped_e.
        -- exact Halpha.
        -- exact HnsR0.
        -- exact HnsR0r.
        -- exact HR0r.
        -- exact HnocollR0.
        -- exact HnocollR0'.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
      * assumption.
      * exact Hctx_arg.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exists Σr2, Rr2, (rootsr0 :: rootsr_rest). repeat split.
        -- eapply TERArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              assumption.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
        -- exact HnsRr2.
        -- exact HRr2.
        -- simpl. constructor; assumption.
Qed.

Lemma alpha_rename_typed_fields_roots_forward :
  forall env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_fields_roots env Ω n lts args_ty R Σ fields defs Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr rho used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  exists Σr' Rr' rootsr,
    typed_fields_roots env Ω n lts args_ty Rr Σr fieldsr defs Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots Hexpr Htyped_fields Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  revert Rr Σr used fieldsr used' Hctx HnsRr HRr HnocollR Hctx_used
    Hrange_used Hrename.
  induction Htyped_fields; intros Rr0 Σr0 used0 fieldsr0 used_out
    Hctx HnsRr0 HRr0 HnocollR0 Hctx_used0 Hrange_used0 Hrename0.
  - exists Σr0, Rr0, [].
    split; [eapply TERFields_Nil|].
    split; [exact Hctx|].
    split; [exact HnsRr0|].
    split; [exact HRr0|].
    simpl. apply root_set_equiv_refl.
  - destruct (alpha_rename_struct_fields_lookup_exists_forward rho used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename0 H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_fields_roots_root_env_names_subset; eassumption. }
    destruct (Hexpr R Rr0 Σ Σr0 used_field e_field e_fieldr
      used_field_out T_field Σ1 R1 roots_field)
      as [Σr1 [Rr1 [roots_fieldr
        [Htyped_field_r [Hctx_field [HnsRr1 [HRr1 Hroots_field]]]]]]].
    + exact Hfield_in.
    + exact H0.
    + exact Hctx.
    + assumption.
    + exact HnsRr0.
    + exact HRr0.
    + exact HnocollR0.
    + exact HnocollR1.
    + intros x Hin. apply Hused_prefix. apply Hctx_used0. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used0. exact Hin.
    + clear -H Hdisj.
      induction fields as [| [fname0 e0] rest IH]; simpl in H, Hdisj.
      * discriminate.
      * destruct (String.eqb (Program.field_name f) fname0) eqn:Hname.
        -- injection H as <-.
           destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [_ Hrest_disj].
           eapply IH; eauto.
    + exact Hrename_field.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used0.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr HnsR1 HnocollR' Hdisj
        Rr1 Σr1 used0 fieldsr0 used_out Hctx_field HnsRr1 HRr1
        HnocollR1 Hctx_used_tail Hrange_used0 Hrename0)
        as [Σr2 [Rr2 [roots_restr
          [Htyped_rest_r [Hctx_rest [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      exists Σr2, Rr2, (root_set_union roots_fieldr roots_restr).
      split.
      * eapply TERFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * split; [exact Hctx_rest|].
        split; [exact HnsRr2|].
        split; [exact HRr2|].
        eapply root_set_equiv_trans.
        -- apply root_set_union_equiv; eassumption.
        -- apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_args_roots_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr args argsr used used' ps psr Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range rho) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exists Σr' Rr' rootsr,
    typed_args_roots_shadow_safe env Ω n Rr Σr argsr psr Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots).
Proof.
  intros env Ω n rho R Rr Σ Σr args.
  revert R Rr Σ Σr.
  induction args as [| arg rest IH]; intros R Rr Σ Σr argsr used used'
    ps psr Σ' R' roots Hexpr Htyped_args Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hparams Hrename;
    simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr, Rr, []. repeat split; try constructor; assumption.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range rho) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr rho used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct ps as [| p ps_tail]; [inversion Htyped_args|].
    destruct psr as [| pr psr_tail]; [inversion Hparams|].
    inversion Htyped_args; subst.
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_args_roots_root_env_names_subset.
        + eapply typed_args_roots_shadow_safe_roots. exact H10.
        + exact Hin. }
    destruct (Hexpr R Rr Σ Σr used arg ar used1 T_e Σ1 R1 roots0)
      as [Σr1 [Rr1 [rootsr0
        [Htyped_arg_r [Hctx_arg [HnsRr1 [HRr1 Hroots0]]]]]]].
    + left. reflexivity.
    + assumption.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range rho) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH R1 Rr1 Σ1 Σr1 restr used1 used2 ps_tail psr_tail
        Σ' R' roots_rest)
        as [Σr2 [Rr2 [rootsr_rest
          [Htyped_tail_r [Hctx_tail [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      * intros R0 R0r Σa Σb used0 e er used_tail T Σa' R0' roots_e
          Hin Htyped_e Halpha HnsR0 HnsR0r HR0r HnocollR0 HnocollR0'
          Hcu Hru Hd Hr.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Htyped_e.
        -- exact Halpha.
        -- exact HnsR0.
        -- exact HnsR0r.
        -- exact HR0r.
        -- exact HnocollR0.
        -- exact HnocollR0'.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
      * assumption.
      * exact Hctx_arg.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exists Σr2, Rr2, (rootsr0 :: rootsr_rest). repeat split.
        -- eapply TERSArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              assumption.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
        -- exact HnsRr2.
        -- exact HRr2.
        -- simpl. constructor; assumption.
Qed.

Lemma alpha_rename_typed_fields_roots_shadow_safe_forward :
  forall env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_fields_roots_shadow_safe env Ω n lts args_ty R Σ fields defs
    Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr rho used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  exists Σr' Rr' rootsr,
    typed_fields_roots_shadow_safe env Ω n lts args_ty Rr Σr fieldsr defs
      Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots Hexpr Htyped_fields Hctx HnsR HnsRr HRr
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  revert Rr Σr used fieldsr used' Hctx HnsRr HRr HnocollR Hctx_used
    Hrange_used Hrename.
  induction Htyped_fields; intros Rr0 Σr0 used0 fieldsr0 used_out
    Hctx HnsRr0 HRr0 HnocollR0 Hctx_used0 Hrange_used0 Hrename0.
  - exists Σr0, Rr0, [].
    split; [eapply TERSFields_Nil|].
    split; [exact Hctx|].
    split; [exact HnsRr0|].
    split; [exact HRr0|].
    simpl. apply root_set_equiv_refl.
  - destruct (alpha_rename_struct_fields_lookup_exists_forward rho used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename0 H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_fields_roots_root_env_names_subset.
        + match goal with
          | Htail : typed_fields_roots_shadow_safe _ _ _ _ _ R1 Σ1 fields rest _ _ _ |- _ =>
              eapply typed_fields_roots_shadow_safe_roots; exact Htail
          end.
        + exact Hin. }
    destruct (Hexpr R Rr0 Σ Σr0 used_field e_field e_fieldr
      used_field_out T_field Σ1 R1 roots_field)
      as [Σr1 [Rr1 [roots_fieldr
        [Htyped_field_r [Hctx_field [HnsRr1 [HRr1 Hroots_field]]]]]]].
    + exact Hfield_in.
    + exact H0.
    + exact Hctx.
    + assumption.
    + exact HnsRr0.
    + exact HRr0.
    + exact HnocollR0.
    + exact HnocollR1.
    + intros x Hin. apply Hused_prefix. apply Hctx_used0. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used0. exact Hin.
    + clear -H Hdisj.
      induction fields as [| [fname0 e0] rest IH]; simpl in H, Hdisj.
      * discriminate.
      * destruct (String.eqb (Program.field_name f) fname0) eqn:Hname.
        -- injection H as <-.
           destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [_ Hrest_disj].
           eapply IH; eauto.
    + exact Hrename_field.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used0.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr HnsR1 HnocollR' Hdisj
        Rr1 Σr1 used0 fieldsr0 used_out Hctx_field HnsRr1 HRr1
        HnocollR1 Hctx_used_tail Hrange_used0 Hrename0)
        as [Σr2 [Rr2 [roots_restr
          [Htyped_rest_r [Hctx_rest [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      exists Σr2, Rr2, (root_set_union roots_fieldr roots_restr).
      split.
      * eapply TERSFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * split; [exact Hctx_rest|].
        split; [exact HnsRr2|].
        split; [exact HRr2|].
        eapply root_set_equiv_trans.
        -- apply root_set_union_equiv; eassumption.
        -- apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_args_roots_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr args argsr used used' ps psr Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e args ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args)
    (rename_range rho) ->
  params_alpha ps psr ->
  ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) = (argsr, used') ->
  exists Σr' Rr' rootsr,
    typed_args_roots_shadow_safe env Ω n Rr Σr argsr psr Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    Forall2 root_set_equiv rootsr (map (root_set_rename rho) roots).
Proof.
  intros env Ω n rho R Rr Σ Σr args.
  revert R Rr Σ Σr.
  induction args as [| arg rest IH]; intros R Rr Σ Σr argsr used used'
    ps psr Σ' R' roots Hexpr Htyped_args Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj
    Hparams Hrename; simpl in Hrename.
  - injection Hrename as <- <-.
    inversion Htyped_args; subst.
    inversion Hparams; subst.
    exists Σr, Rr, []. repeat split; try constructor; assumption.
  - destruct (disjoint_names_app_l (free_vars_expr arg)
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg0 :: rest0 => free_vars_expr arg0 ++ go rest0
          end) rest) (rename_range rho) Hdisj) as [Hdisj_arg Hdisj_rest].
    destruct (alpha_rename_expr rho used arg) as [ar used1] eqn:Harg.
    destruct ((fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg0 :: rest0 =>
              let (arg', used2) := alpha_rename_expr rho used0 arg0 in
              let (rest', used3) := go used2 rest0 in
              (arg' :: rest', used3)
          end) used1 rest) as [restr used2] eqn:Hrest.
    injection Hrename as <- <-.
    destruct ps as [| p ps_tail]; [inversion Htyped_args|].
    destruct psr as [| pr psr_tail]; [inversion Hparams|].
    inversion Htyped_args; subst.
    destruct (params_alpha_cons_inv (p :: ps_tail) pr psr_tail Hparams)
      as [p0 [ps0 [Hps [Hshape Hparams_tail]]]].
    injection Hps as <- <-.
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ arg T_e Σ1 R1 roots0) as [Hroots_env1 _].
      - match goal with
        | H : typed_env_roots_shadow_safe env Ω n R Σ arg T_e Σ1 R1 roots0 |- _ =>
            exact H
        end.
      - exact HnsR.
      - exact Hroots.
      - exact Hroots_env1. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_args_roots_root_env_names_subset.
        + eapply typed_args_roots_shadow_safe_roots. exact H10.
        + exact Hin. }
    destruct (Hexpr R Rr Σ Σr used arg ar used1 T_e Σ1 R1 roots0)
      as [Σr1 [Rr1 [rootsr0
        [Htyped_arg_r [Hctx_arg [HnsRr1 [HRr1 Hroots0]]]]]]].
    + left. reflexivity.
    + assumption.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact Hkeys.
    + exact Hroots.
    + exact HnocollR.
    + exact HnocollR1.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_arg.
    + exact Harg.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hctx_used.
          rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
          + exact Hin.
          + eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped_arg_r. }
      assert (Hrange_used_tail : forall x, In x (rename_range rho) -> In x used1).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends.
        - exact Harg.
        - apply Hrange_used. exact Hin. }
      destruct (IH R1 Rr1 Σ1 Σr1 restr used1 used2 ps_tail psr_tail
        Σ' R' roots_rest)
        as [Σr2 [Rr2 [rootsr_rest
          [Htyped_tail_r [Hctx_tail [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      * intros R0 R0r Σa Σb used0 e er used_tail T Σa' R0' roots_e
          Hin Htyped_e Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots_support
          HnocollR0 HnocollR0' Hcu Hru Hd Hr.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Htyped_e.
        -- exact Halpha.
        -- exact HnsR0.
        -- exact HnsR0r.
        -- exact HR0r.
        -- exact Hkeys0.
        -- exact Hroots_support.
        -- exact HnocollR0.
        -- exact HnocollR0'.
        -- exact Hcu.
        -- exact Hru.
        -- exact Hd.
        -- exact Hr.
      * assumption.
      * exact Hctx_arg.
      * exact HnsR1.
      * exact HnsRr1.
      * exact HRr1.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used_tail.
      * exact Hrange_used_tail.
      * exact Hdisj_rest.
      * exact Hparams_tail.
      * exact Hrest.
      * exists Σr2, Rr2, (rootsr0 :: rootsr_rest). repeat split.
        -- eapply TERSArgs_Cons.
           ++ exact Htyped_arg_r.
           ++ destruct Hshape as [_ HT]. simpl in HT. rewrite <- HT.
              assumption.
           ++ exact Htyped_tail_r.
        -- exact Hctx_tail.
        -- exact HnsRr2.
        -- exact HRr2.
        -- simpl. constructor; assumption.
Qed.

Lemma alpha_rename_typed_fields_roots_shadow_safe_support_forward :
  forall env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er used1 T Σa' R0' roots0,
      In e (map snd fields) ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho (root_env_names R0) ->
      rename_no_collision_on rho (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho) ->
      alpha_rename_expr rho used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  typed_fields_roots_shadow_safe env Ω n lts args_ty R Σ fields defs
    Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names
    ((fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end) fields)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (fields0 : list (string * expr))
      : list (string * expr) * list ident :=
      match fields0 with
      | [] => ([], used0)
      | (fname, e) :: rest =>
          let (e', used1) := alpha_rename_expr rho used0 e in
          let (rest', used2) := go used1 rest in
          ((fname, e') :: rest', used2)
      end) used fields) = (fieldsr, used') ->
  exists Σr' Rr' rootsr,
    typed_fields_roots_shadow_safe env Ω n lts args_ty Rr Σr fieldsr defs
      Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho lts args_ty R Rr Σ Σr fields fieldsr used used'
    defs Σ' R' roots Hexpr Htyped_fields Hctx HnsR HnsRr HRr
    Hkeys Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj
    Hrename.
  revert Rr Σr used fieldsr used' Hctx HnsRr HRr Hkeys Hroots
    HnocollR Hctx_used Hrange_used Hrename.
  induction Htyped_fields; intros Rr0 Σr0 used0 fieldsr0 used_out
    Hctx HnsRr0 HRr0 Hkeys0 Hroots0 HnocollR0 Hctx_used0
    Hrange_used0 Hrename0.
  - exists Σr0, Rr0, [].
    split; [eapply TERSFields_Nil|].
    split; [exact Hctx|].
    split; [exact HnsRr0|].
    split; [exact HRr0|].
    simpl. apply root_set_equiv_refl.
  - destruct (alpha_rename_struct_fields_lookup_exists_forward rho used0 fields
      fieldsr0 used_out (Program.field_name f) e_field Hrename0 H)
      as [e_fieldr [used_field [used_field_out
        [Hlookup_r [Hrename_field Hused_prefix]]]]].
    assert (Hfield_in : In e_field (map snd fields)).
    { eapply lookup_field_b_in_alpha. exact H. }
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. eassumption.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e_field T_field Σ1 R1 roots_field)
        as [Hroots_env1 _].
      - exact H0.
      - exact HnsR.
      - exact Hroots0.
      - exact Hroots_env1. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply typed_fields_roots_root_env_names_subset.
        + match goal with
          | Htail : typed_fields_roots_shadow_safe _ _ _ _ _ R1 Σ1 fields rest _ _ _ |- _ =>
              eapply typed_fields_roots_shadow_safe_roots; exact Htail
          end.
        + exact Hin. }
    destruct (Hexpr R Rr0 Σ Σr0 used_field e_field e_fieldr
      used_field_out T_field Σ1 R1 roots_field)
      as [Σr1 [Rr1 [roots_fieldr
        [Htyped_field_r [Hctx_field [HnsRr1 [HRr1 Hroots_field]]]]]]].
    + exact Hfield_in.
    + exact H0.
    + exact Hctx.
    + assumption.
    + exact HnsRr0.
    + exact HRr0.
    + exact Hkeys0.
    + exact Hroots0.
    + exact HnocollR0.
    + exact HnocollR1.
    + intros x Hin. apply Hused_prefix. apply Hctx_used0. exact Hin.
    + intros x Hin. apply Hused_prefix. apply Hrange_used0. exact Hin.
    + clear -H Hdisj.
      induction fields as [| [fname0 e0] rest IH]; simpl in H, Hdisj.
      * discriminate.
      * destruct (String.eqb (Program.field_name f) fname0) eqn:Hname.
        -- injection H as <-.
           destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [Hfield_disj _].
           exact Hfield_disj.
        -- destruct (disjoint_names_app_l (free_vars_expr e0)
             ((fix go (fields0 : list (string * expr)) : list ident :=
                 match fields0 with
                 | [] => []
                 | (_, e) :: rest0 => free_vars_expr e ++ go rest0
                 end) rest) (rename_range rho) Hdisj) as [_ Hrest_disj].
           eapply IH; eauto.
    + exact Hrename_field.
    + assert (Hctx_used_tail : forall x, In x (ctx_names Σr1) -> In x used0).
      { intros x Hin.
        apply Hctx_used0.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σr1).
        - exact Hin.
        - eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped_field_r. }
      destruct (IHHtyped_fields Hexpr HnsR1 HnocollR'
        Hdisj Rr1 Σr1 used0 fieldsr0 used_out Hctx_field HnsRr1
        HRr1 HkeysR1 HrootsR1 HnocollR1 Hctx_used_tail Hrange_used0
        Hrename0)
        as [Σr2 [Rr2 [roots_restr
          [Htyped_rest_r [Hctx_rest [HnsRr2 [HRr2 Hroots_rest]]]]]]].
      exists Σr2, Rr2, (root_set_union roots_fieldr roots_restr).
      split.
      * eapply TERSFields_Cons.
        -- exact Hlookup_r.
        -- exact Htyped_field_r.
        -- exact H1.
        -- exact Htyped_rest_r.
      * split; [exact Hctx_rest|].
        split; [exact HnsRr2|].
        split; [exact HRr2|].
        eapply root_set_equiv_trans.
        -- apply root_set_union_equiv; eassumption.
        -- apply root_set_equiv_sym. apply root_set_union_rename_equiv.
Qed.

Lemma alpha_rename_typed_match_tail_roots_shadow_safe_forward :
  forall env Ω n rho lts args R roots_scrut roots_scrutr Rr Σ Σr branches branchesr used used'
      variants expected_core R_out Rr_out Σs Ts rootss,
  (forall rho0 R0 R0r Σa Σb used0 variant binders e er used1 T Σa' R0' roots0,
      In (variant, binders, e) branches ->
      typed_env_roots_shadow_safe env Ω n R0 Σa e T Σa' R0' roots0 ->
      ctx_alpha rho0 Σa Σb ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0r ->
      root_env_equiv R0r (root_env_rename rho0 R0) ->
      root_env_sctx_keys_named R0 Σa ->
      root_env_sctx_roots_named R0 Σa ->
      rename_no_collision_on rho0 (root_env_names R0) ->
      rename_no_collision_on rho0 (root_env_names R0') ->
      (forall x, In x (ctx_names Σb) -> In x used0) ->
      (forall x, In x (rename_range rho0) -> In x used0) ->
      disjoint_names (free_vars_expr e) (rename_range rho0) ->
      alpha_rename_expr rho0 used0 e = (er, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er T
          Σb' R0r' roots0r /\
        ctx_alpha rho0 Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho0 R0') /\
        root_set_equiv roots0r (root_set_rename rho0 roots0)) ->
  typed_match_tail_roots_shadow_safe env Ω n lts args R roots_scrut Σ branches variants
    expected_core R_out Σs Ts rootss ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow R_out ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  root_env_sctx_keys_named R Σ ->
  root_env_sctx_roots_named R Σ ->
  root_set_sctx_roots_named roots_scrut Σ ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R_out) ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  root_set_equiv roots_scrutr (root_set_rename rho roots_scrut) ->
  disjoint_names
    ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
        match branches0 with
        | [] => []
        | (_, _, e) :: rest => free_vars_expr e ++ go rest
        end) branches)
    (rename_range rho) ->
  ((fix go (used0 : list ident) (branches0 : list (string * list ident * expr))
      : list (string * list ident * expr) * list ident :=
      match branches0 with
      | [] => ([], used0)
      | (name, binders, e) :: rest =>
          let binder_seed := binders ++ free_vars_expr e ++ used0 in
          let '(binders', rho_branch, used1) :=
            alpha_rename_idents rho binder_seed binders in
          let (e', used2) := alpha_rename_expr rho_branch used1 e in
          let (rest', used3) := go used2 rest in
          ((name, binders', e') :: rest', used3)
      end) used branches) = (branchesr, used') ->
  root_env_equiv Rr_out (root_env_rename rho R_out) ->
  exists Σrs rootssr,
    typed_match_tail_roots_shadow_safe env Ω n lts args Rr roots_scrutr Σr branchesr variants
      expected_core Rr_out Σrs Ts rootssr /\
    Forall2 (ctx_alpha rho) Σs Σrs /\
    Forall2 root_set_equiv rootssr (map (root_set_rename rho) rootss).
Proof.
  intros env Ω n rho lts args R roots_scrut roots_scrutr Rr Σ Σr branches branchesr used used'
    variants expected_core R_out Rr_out Σs Ts rootss Hexpr Htyped_tail
    Hctx HnsR HnsRout HnsRr HRr Hkeys Hroots Hroots_scrut_named
    HnocollR HnocollRout Hctx_used Hrange_used Hroots_scrutr Hdisj Hrename HRout.
  induction Htyped_tail.
  - exists [], []. repeat split; constructor.
	  - destruct (alpha_rename_match_branches_lookup_payload_forward
	      rho used branches branchesr used' (Program.enum_variant_name v) binders e
	      Hrename H H4)
      as [bindersr [rho_branch [er [used_pre [used_branch [used_branch_out
        [Hbinders_r [Hlookup_r [Hrename_binders
          [Hrename_branch Hused_prefix]]]]]]]]]].
	    pose proof (lookup_expr_branch_binders_expr_in_alpha _ _ _ _ H H4)
	      as Hbranch_in.
	    unfold match_payload_params in H0.
	    destruct (match_binder_params_alpha_rename_idents
	      rho (binders ++ free_vars_expr e ++ used_pre) binders bindersr rho_branch
	      used_branch (instantiate_enum_variant_field_tys lts args v) ps
	      Hrename_binders H0) as [psr [Hparams_r [Hparams_alpha Hrename_params]]].
    assert (Hparams_nodup_r : params_names_nodup_b psr = true).
    { apply params_names_nodup_b_complete_alpha.
      rewrite (match_binder_params_names _ _ _ Hparams_r).
      eapply alpha_rename_idents_outputs_nodup. exact Hrename_binders. }
    assert (Hctx_none_r : ctx_lookup_params_none_b psr Σr = true).
    { eapply ctx_lookup_params_none_b_fresh_used with (used := used_pre).
      - intros x Hin. apply Hused_prefix. apply Hctx_used. exact Hin.
      - rewrite (match_binder_params_names _ _ _ Hparams_r).
        eapply Forall_fresh_weaken.
        + intros x Hin.
          apply in_or_app. right. apply in_or_app. right. exact Hin.
        + eapply alpha_rename_idents_fresh_used. exact Hrename_binders. }
    assert (Hctx_payload :
      ctx_alpha rho_branch (sctx_add_params ps Σ) (sctx_add_params psr Σr)).
    { unfold sctx_add_params, ctx_add_params.
      eapply alpha_rename_params_ctx_alpha_extend_tail.
      - exact Hrename_params.
      - exact Hctx.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin. }
    assert (Hkeys_r : root_env_sctx_keys_named Rr Σr).
    { eapply root_env_sctx_keys_named_rename; eassumption. }
    assert (Hroots_r : root_env_sctx_roots_named Rr Σr).
    { eapply root_env_sctx_roots_named_rename.
      - exact Hctx.
      - exact HnsR.
      - exact HRr.
      - exact Hroots. }
    assert (Hroots_scrutr_named : root_set_sctx_roots_named roots_scrutr Σr).
    { eapply root_set_sctx_roots_named_rename.
      - exact Hctx.
      - exact Hroots_scrutr.
      - exact Hroots_scrut_named. }
    assert (Hroots_scrut_excl : roots_exclude_params ps roots_scrut).
    { unfold roots_exclude_params.
      apply Forall_forall. intros x Hin.
      eapply root_set_sctx_roots_named_fresh_exclude.
      - exact Hroots_scrut_named.
      - eapply ctx_lookup_params_none_b_not_in_names; eassumption. }
    assert (Henv_excl_R : root_env_excludes_params ps R).
    { unfold root_env_excludes_params.
      apply Forall_forall. intros x Hin.
      eapply root_env_sctx_roots_named_fresh_excludes.
      - exact Hroots.
      - eapply ctx_lookup_params_none_b_not_in_names; eassumption. }
    assert (Hroot_none_r : root_env_lookup_params_none_b psr Rr = true).
    { eapply root_env_lookup_params_none_b_from_sctx_keys; eassumption. }
    pose (R_payload_r := root_env_add_params_roots_same psr roots_scrutr Rr).
    assert (Hroots_scrutr_branch :
      root_set_equiv roots_scrutr (root_set_rename rho_branch roots_scrut)).
    { eapply root_set_equiv_trans.
      - exact Hroots_scrutr.
      - apply root_set_equiv_sym.
        eapply alpha_rename_params_root_set_rename_excluded.
        + exact Hrename_params.
        + exact Hroots_scrut_excl. }
    assert (HRpayload_r :
	      root_env_equiv R_payload_r (root_env_rename rho_branch R_payload)).
	    { unfold R_payload_r. subst R_payload.
	      eapply alpha_rename_params_root_env_add_params_roots_same_rename_equiv.
	      - exact Hrename_params.
	      - exact HnsR.
	      - exact H3.
	      - exact H1.
	      - exact Hroots_scrut_excl.
	      - exact Henv_excl_R.
	      - exact HRr.
      - exact Hroots_scrutr_branch. }
    assert (Hkeys_payload_r :
      root_env_sctx_keys_named R_payload_r (sctx_add_params psr Σr)).
    { unfold R_payload_r.
      apply root_env_sctx_keys_named_add_params_roots_same. exact Hkeys_r. }
    assert (Hkeys_payload :
      root_env_sctx_keys_named R_payload (sctx_add_params ps Σ)).
    { subst R_payload.
      apply root_env_sctx_keys_named_add_params_roots_same. exact Hkeys. }
    assert (Hroots_payload_r :
      root_env_sctx_roots_named R_payload_r (sctx_add_params psr Σr)).
    { unfold R_payload_r.
      apply root_env_sctx_roots_named_add_params_roots_same; assumption. }
    assert (Hns_payload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hns_payload_r : root_env_no_shadow R_payload_r).
    { unfold R_payload_r.
      eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hnocoll_payload :
      rename_no_collision_on rho_branch (root_env_names R_payload)).
    { subst R_payload.
	      eapply alpha_rename_params_root_env_add_params_roots_same_no_collision_on.
	      - exact Hrename_params.
	      - exact Hctx.
	      - exact Hkeys.
	      - exact H3.
	      - exact H1.
	      - exact H2.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin.
      - exact HnocollR. }
    assert (HnocollRv : rename_no_collision_on rho (root_env_names Rv)).
    { eapply rename_no_collision_on_weaken_names.
	      - exact HnocollRout.
	      - intros x Hin.
	        eapply root_env_equiv_names_subset_l.
	        + exact H13.
	        + exact Hin. }
    assert (HnsRv : root_env_no_shadow Rv).
    { subst Rv.
	      apply root_env_remove_match_params_no_shadow.
	      eapply typed_env_roots_no_shadow.
	      - eapply typed_env_roots_shadow_safe_roots. exact H6.
      - subst R_payload.
        eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (Hkeys_Rv_payload :
      root_env_sctx_keys_named Rv_payload (sctx_add_params ps Σ)).
    { assert (Hkeys_Rv_payload0 :
	        root_env_sctx_keys_named Rv_payload Σv_payload).
	      { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
	          as [Hkeys_expr _].
	        eapply Hkeys_expr.
	        - exact H6.
        - exact Hns_payload.
        - exact Hkeys_payload. }
      eapply root_env_sctx_keys_named_same_bindings.
      - apply sctx_same_bindings_sym.
	        eapply typed_env_structural_same_bindings.
	        eapply typed_env_roots_structural.
	        eapply typed_env_roots_shadow_safe_roots. exact H6.
      - exact Hkeys_Rv_payload0. }
    assert (Hnocoll_Rv_payload :
      rename_no_collision_on rho_branch (root_env_names Rv_payload)).
    { subst Rv.
      eapply alpha_rename_params_root_env_remove_match_params_no_collision_on.
      - exact Hrename_params.
	      - exact Hctx.
	      - eapply typed_env_roots_no_shadow.
	        + eapply typed_env_roots_shadow_safe_roots. exact H6.
	        + exact Hns_payload.
	      - exact Hkeys_Rv_payload.
	      - exact H1.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hctx_used. exact Hin.
      - intros x Hin. apply in_or_app. right. apply in_or_app. right.
        apply Hused_prefix. apply Hrange_used. exact Hin.
      - exact HnocollRv. }
    destruct (Hexpr rho_branch R_payload R_payload_r
      (sctx_add_params ps Σ) (sctx_add_params psr Σr) used_branch
      (Program.enum_variant_name v) binders e er used_branch_out T
      Σv_payload Rv_payload roots)
      as [Σvr [Rvr [rootsr
        [Htyped_branch_r [Hctx_branch [HnsRvr [HRvr Hrootsr]]]]]]].
	    + exact Hbranch_in.
	    + exact H6.
    + exact Hctx_payload.
    + exact Hns_payload.
    + exact Hns_payload_r.
    + exact HRpayload_r.
    + exact Hkeys_payload.
    + subst R_payload.
      apply root_env_sctx_roots_named_add_params_roots_same; assumption.
    + exact Hnocoll_payload.
    + exact Hnocoll_Rv_payload.
    + intros x Hin.
      unfold sctx_add_params, ctx_add_params in Hin.
      rewrite ctx_names_app in Hin.
      apply in_app_or in Hin as [Hin_params | Hin_tail].
      * eapply alpha_rename_params_names_in_used.
        -- exact Hrename_params.
        -- exact Hin_params.
      * eapply alpha_rename_params_used_extends.
        -- exact Hrename_params.
        -- apply in_or_app. right. apply in_or_app. right.
           apply Hused_prefix. apply Hctx_used. exact Hin_tail.
    + intros x Hin.
      destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _
        Hrename_params _ Hin) as [Hin_params | Hin_range].
      * eapply alpha_rename_params_names_in_used.
        -- exact Hrename_params.
        -- exact Hin_params.
      * eapply alpha_rename_params_used_extends.
        -- exact Hrename_params.
        -- apply in_or_app. right. apply in_or_app. right.
           apply Hused_prefix. apply Hrange_used. exact Hin_range.
    + intros x Hfree Hrange.
      destruct (alpha_rename_params_range_ctx_or_tail _ _ _ _ _ _
        Hrename_params _ Hrange) as [Hin_params | Hin_range].
      * eapply alpha_rename_params_names_fresh_used.
        -- exact Hrename_params.
        -- exact Hin_params.
        -- apply in_or_app. right. apply in_or_app. left. exact Hfree.
	      * eapply lookup_expr_branch_disjoint_alpha.
	        -- exact H4.
        -- exact Hdisj.
        -- exact Hfree.
        -- exact Hin_range.
    + exact Hrename_branch.
    + destruct (IHHtyped_tail Hexpr Hctx HnsR HnsRout HRr Hkeys Hroots
        Hroots_scrut_named HnocollR HnocollRout Hroots_scrutr Hdisj Hrename HRout)
        as [Σrs [rootssr [Htail_r [Hctx_tail Hroots_tail]]]].
      pose (Rv_r := root_env_remove_match_params psr Rvr).
      pose (Σv_r := sctx_remove_params psr Σvr).
      assert (Hparams_ok_r :
        params_ok_sctx_b env psr Σvr = true).
	      { eapply alpha_rename_params_params_ok_sctx_b_forward_gen.
	        - exact Hrename_params.
	        - rewrite <- params_ctx_names_param_names.
	          eapply params_names_nodup_b_sound. exact H1.
	        - intros x Hin.
	          rewrite <- params_ctx_names_param_names in Hin.
	          rewrite (match_binder_params_names _ _ _ H0) in Hin.
          apply in_or_app. left. exact Hin.
        - intros x Hin.
          apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hrange_used. exact Hin.
	        - exact Hctx_branch.
	        - exact H7. }
      assert (Hrootsr_outer :
        root_set_equiv rootsr (root_set_rename rho roots)).
	      { eapply root_set_equiv_trans.
	        - exact Hrootsr.
	        - eapply alpha_rename_params_root_set_rename_excluded.
	          + exact Hrename_params.
	          + exact H8. }
      assert (Hroots_branch_named :
        root_set_sctx_roots_named roots (sctx_add_params ps Σ)).
      { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
          as [Hroots_env _].
	        destruct (Hroots_env R_payload (sctx_add_params ps Σ) e T
	          Σv_payload Rv_payload roots H6 Hns_payload) as [_ Hroots_branch].
        - subst R_payload.
          apply root_env_sctx_roots_named_add_params_roots_same; assumption.
        - eapply root_set_sctx_roots_named_same_bindings.
          + apply sctx_same_bindings_sym.
	            eapply typed_env_structural_same_bindings.
	            eapply typed_env_roots_structural.
	            eapply typed_env_roots_shadow_safe_roots. exact H6.
          + exact Hroots_branch. }
	      assert (Hns_Rv_payload : root_env_no_shadow Rv_payload).
	      { eapply typed_env_roots_no_shadow.
	        - eapply typed_env_roots_shadow_safe_roots. exact H6.
	        - exact Hns_payload. }
      assert (Hroots_Rv_payload :
        root_env_sctx_roots_named Rv_payload (sctx_add_params ps Σ)).
      { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
          as [Hroots_env _].
	        destruct (Hroots_env R_payload (sctx_add_params ps Σ) e T
	          Σv_payload Rv_payload roots H6 Hns_payload) as [Hroots_env_branch _].
        - subst R_payload.
          apply root_env_sctx_roots_named_add_params_roots_same; assumption.
        - eapply root_env_sctx_roots_named_same_bindings.
          + apply sctx_same_bindings_sym.
	            eapply typed_env_structural_same_bindings.
	            eapply typed_env_roots_structural.
	            eapply typed_env_roots_shadow_safe_roots. exact H6.
          + exact Hroots_env_branch. }
      assert (Hkeys_Rv :
        root_env_sctx_keys_named Rv (sctx_add_params ps Σ)).
      { eapply root_env_sctx_keys_named_add_params_env.
        eapply root_env_sctx_keys_named_same_bindings.
        - apply sctx_same_bindings_sym.
          eapply sctx_same_bindings_remove_added_params.
          apply sctx_same_bindings_refl.
	        - rewrite H9.
	          eapply root_env_sctx_keys_named_remove_match_params.
          + exact Hns_Rv_payload.
          + exact Hkeys_Rv_payload. }
      assert (Hroots_Rv :
        root_env_sctx_roots_named Rv (sctx_add_params ps Σ)).
      { eapply root_env_sctx_roots_named_add_params_env.
        eapply root_env_sctx_roots_named_same_bindings.
        - apply sctx_same_bindings_sym.
          eapply sctx_same_bindings_remove_added_params.
          apply sctx_same_bindings_refl.
	        - rewrite H9.
	          eapply root_env_sctx_roots_named_remove_match_params.
	          + exact Hns_Rv_payload.
	          + rewrite <- H9. exact H10.
	          + exact Hroots_Rv_payload. }
	      assert (Hroot_none_Rv : root_env_lookup_params_none_b ps Rv = true).
	      { rewrite H9.
	        apply root_env_lookup_params_none_b_remove_match_params.
	        exact Hns_Rv_payload. }
      assert (Hnocoll_params_Rv_payload :
        forall x, In x (ctx_names (params_ctx ps)) ->
          rename_no_collision_for rho_branch x (root_env_names Rv_payload)).
      { intros x Hin.
        eapply alpha_rename_params_rename_no_collision_for_params.
        - exact Hrename_params.
	        - exact Hctx.
	        - exact Hns_Rv_payload.
	        - exact Hkeys_Rv_payload.
	        - exact H1.
        - intros y Hy. apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hctx_used. exact Hy.
        - intros y Hy. apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hrange_used. exact Hy.
        - exact Hnocoll_Rv_payload.
        - exact Hin. }
	      assert (HRv_r_branch :
	        root_env_equiv Rv_r (root_env_rename rho_branch Rv)).
	      { unfold Rv_r. rewrite H9.
	        eapply alpha_rename_params_root_env_remove_match_params_full_rename_equiv.
	        - exact Hrename_params.
	        - exact H1.
        - exact Hns_Rv_payload.
        - exact HnsRvr.
        - exact HRvr.
        - exact Hnocoll_Rv_payload.
        - exact Hnocoll_params_Rv_payload.
        - intros x Hin. reflexivity. }
	      assert (Henv_excl_r : root_env_excludes_params psr Rv_r).
	      { eapply alpha_rename_params_root_env_excludes_params_rename.
	        - exact Hrename_params.
	        - exact Hctx.
        - exact HnsRv.
	        - exact Hkeys_Rv.
	        - exact Hroots_Rv.
	        - exact Hroot_none_Rv.
	        - exact H10.
        - exact HRv_r_branch.
        - intros x Hin. apply in_or_app. right. apply in_or_app. right.
          apply Hused_prefix. apply Hctx_used. exact Hin.
	        - intros x Hin. apply in_or_app. right. apply in_or_app. right.
	          apply Hused_prefix. apply Hrange_used. exact Hin. }
	      exists (Σv_r :: Σrs), (rootsr :: rootssr).
	      split.
	      * eapply TERSMatchTail_Cons.
	        -- exact Hbinders_r.
	        -- unfold match_payload_params. exact Hparams_r.
        -- exact Hparams_nodup_r.
        -- exact Hctx_none_r.
        -- exact Hroot_none_r.
        -- exact Hlookup_r.
        -- reflexivity.
        -- exact Htyped_branch_r.
        -- exact Hparams_ok_r.
        -- eapply alpha_rename_params_roots_exclude_params_rename.
           ++ exact Hrename_params.
           ++ exact Hctx.
           ++ exact Hroots_branch_named.
	           ++ exact H8.
           ++ exact Hrootsr.
           ++ intros x Hin. apply in_or_app. right. apply in_or_app. right.
              apply Hused_prefix. apply Hctx_used. exact Hin.
           ++ intros x Hin. apply in_or_app. right. apply in_or_app. right.
              apply Hused_prefix. apply Hrange_used. exact Hin.
	        -- reflexivity.
	        -- exact Henv_excl_r.
	        -- reflexivity.
	        -- exact H12.
	        -- eapply root_env_equiv_trans.
	           ++ exact HRv_r_branch.
	           ++ eapply root_env_equiv_trans.
	              ** eapply alpha_rename_params_root_env_rename_excluded.
	                 --- exact Hrename_params.
	                 --- exact HnsRv.
	                 --- exact Hroot_none_Rv.
	                 --- exact H10.
	              ** eapply root_env_equiv_trans.
	                 --- eapply root_env_equiv_rename with (rho := rho).
	                     +++ exact H13.
                     +++ exact HnsRv.
                     +++ exact HnsRout.
                     +++ exact HnocollRv.
                     +++ exact HnocollRout.
                 --- apply root_env_equiv_sym. exact HRout.
        -- exact Htail_r.
      * split.
        -- constructor.
           ++ subst Σv_r Σv.
              eapply alpha_rename_params_ctx_alpha_remove.
              ** exact Hrename_params.
              ** exact Hctx_branch.
           ++ assumption.
        -- constructor; assumption.
Qed.
