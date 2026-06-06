From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping AlphaEnvStructural AlphaRoots.
From Facet.TypeSystem Require Export AlphaRootEnvFacts.
From Facet.TypeSystem Require Export AlphaTypedRoots.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

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

Lemma root_env_names_in_lookup :
  forall x R,
    In x (root_env_names R) ->
    exists roots, root_env_lookup x R = Some roots.
Proof.
  intros x R Hin.
  induction R as [| [y roots_y] rest IH]; simpl in Hin; try contradiction.
  simpl.
  destruct Hin as [Heq | Hin].
  - subst y. rewrite ident_eqb_refl. eauto.
  - destruct (ident_eqb x y); eauto.
Qed.

Lemma root_env_equiv_names_subset_l :
  forall R R' x,
    root_env_equiv R R' ->
    In x (root_env_names R) ->
    In x (root_env_names R').
Proof.
  intros R R' x Heq Hin.
  destruct (root_env_names_in_lookup x R Hin) as [roots Hlookup].
  destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
    as [roots' [Hlookup' _]].
  eapply root_env_lookup_some_in_names. exact Hlookup'.
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

Lemma alpha_rename_typed_env_roots_call_forward :
  forall env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
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
  typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECall fname args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECall fname args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (fn_params fdef))
    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots _ _ _ _ _ args
          (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
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
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TER_Call; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_struct_forward :
  forall env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e (map snd fields) ->
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
  typed_env_roots env Ω n R Σ (EStruct sname lts args fields)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EStruct sname lts args fields))
    (rename_range rho) ->
  alpha_rename_expr rho used (EStruct sname lts args fields) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
              : list (string * expr) * list ident :=
              match fields0 with
              | [] => ([], used0)
              | (fname, e) :: rest =>
                  let (e', used1) := alpha_rename_expr rho used0 e in
                  let (rest', used2) := go used1 rest in
                  ((fname, e') :: rest', used2)
              end) used fields) as [fieldsr used_fields] eqn:Hfields.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_fields_roots_forward
    env Ω n rho lts args R Rr Σ Σr fields fieldsr used used_fields
    (Program.struct_fields sdef) Σ' R' roots)
    as [Σr' [Rr' [rootsr
      [Hfields_r [Hctx_r [HnsRr' [HRr' Hroots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_fields_roots _ _ _ lts args _ _ fields
          (Program.struct_fields sdef) _ _ roots |- _ =>
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
  - exact Hfields.
  - exists Σr', Rr', rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TER_Struct; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + exact Hroots.
Qed.

Lemma alpha_rename_typed_env_roots_call_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
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
  typed_env_roots_shadow_safe env Ω n R Σ (ECall fname args)
    T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (ECall fname args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECall fname args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_shadow_safe_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (fn_params fdef))
    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots_shadow_safe _ _ _ _ _ args
          (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
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
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_Call; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_struct_shadow_safe_forward :
  forall env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e (map snd fields) ->
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
  typed_env_roots_shadow_safe env Ω n R Σ
    (EStruct sname lts args fields) T Σ' R' roots ->
  ctx_alpha rho Σ Σr ->
  root_env_no_shadow R ->
  root_env_no_shadow Rr ->
  root_env_equiv Rr (root_env_rename rho R) ->
  rename_no_collision_on rho (root_env_names R) ->
  rename_no_collision_on rho (root_env_names R') ->
  (forall x, In x (ctx_names Σr) -> In x used) ->
  (forall x, In x (rename_range rho) -> In x used) ->
  disjoint_names (free_vars_expr (EStruct sname lts args fields))
    (rename_range rho) ->
  alpha_rename_expr rho used (EStruct sname lts args fields) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
              : list (string * expr) * list ident :=
              match fields0 with
              | [] => ([], used0)
              | (fname, e) :: rest =>
                  let (e', used1) := alpha_rename_expr rho used0 e in
                  let (rest', used2) := go used1 rest in
                  ((fname, e') :: rest', used2)
              end) used fields) as [fieldsr used_fields] eqn:Hfields.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_fields_roots_shadow_safe_forward
    env Ω n rho lts args R Rr Σ Σr fields fieldsr used used_fields
    (Program.struct_fields sdef) Σ' R' roots)
    as [Σr' [Rr' [rootsr
      [Hfields_r [Hctx_r [HnsRr' [HRr' Hroots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_fields_roots_shadow_safe _ _ _ lts args _ _ fields
          (Program.struct_fields sdef) _ _ roots |- _ =>
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
  - exact Hfields.
  - exists Σr', Rr', rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Struct; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + exact Hroots.
Qed.

Lemma alpha_rename_typed_env_roots_call_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
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
  typed_env_roots_shadow_safe env Ω n R Σ (ECall fname args)
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
  disjoint_names (free_vars_expr (ECall fname args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECall fname args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (fn_params fdef))
    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots_shadow_safe _ _ _ _ _ args
          (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
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
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_Call; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_call_generic_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr fname type_args args er used used' T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
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
  typed_env_roots_shadow_safe env Ω n R Σ (ECallGeneric fname type_args args)
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
  disjoint_names (free_vars_expr (ECallGeneric fname type_args args))
    (rename_range rho) ->
  alpha_rename_expr rho used (ECallGeneric fname type_args args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr fname type_args args er used used' T Σ' R' roots
    Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR
    HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used args) as [argsr used_args] eqn:Hargs.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
    env Ω n rho R Rr Σ Σr args argsr used used_args
    (apply_lt_params σ (apply_type_params type_args (fn_params fdef)))
    (apply_lt_params σ (apply_type_params type_args (fn_params fdef))) Σ' R' arg_roots)
    as [Σr' [Rr' [arg_rootsr
      [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_args_roots_shadow_safe _ _ _ _ _ args
          (apply_lt_params σ (apply_type_params type_args (fn_params fdef)))
          _ _ arg_roots |- _ =>
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
  - apply params_alpha_refl.
  - exact Hargs.
  - exists Σr', Rr', (root_sets_union arg_rootsr).
    split; [| split; [| split; [| split]]].
    + eapply TERS_CallGeneric; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + eapply root_sets_union_rename_equiv. exact Harg_roots.
Qed.

Lemma alpha_rename_typed_env_roots_call_expr_fn_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr callee args er used used' T Σ' R' roots,
  (* IH for callee *)
  (forall R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0,
      typed_env_roots_shadow_safe env Ω n R0 Σa callee T0 Σa' R0' roots0 ->
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
      disjoint_names (free_vars_expr callee) (rename_range rho) ->
      alpha_rename_expr rho used0 callee = (er0, used1) ->
      exists Σb' R0r' roots0r,
        typed_env_roots_shadow_safe env Ω n R0r Σb er0 T0 Σb' R0r' roots0r /\
        ctx_alpha rho Σa' Σb' /\
        root_env_no_shadow R0r' /\
        root_env_equiv R0r' (root_env_rename rho R0') /\
        root_set_equiv roots0r (root_set_rename rho roots0)) ->
  (* IH for args *)
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e args ->
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
  typed_env_roots_shadow_safe env Ω n R Σ (ECallExpr callee args) T Σ' R' roots ->
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
  disjoint_names (free_vars_expr (ECallExpr callee args)) (rename_range rho) ->
  alpha_rename_expr rho used (ECallExpr callee args) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr callee args er used used' T Σ' R' roots
    Hcallee_ih Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  simpl in Hdisj.
  destruct (alpha_rename_expr rho used callee) as [callee_r used_callee] eqn:Hcallee_rename.
  destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
              : list expr * list ident :=
              match args0 with
              | [] => ([], used0)
              | arg :: rest =>
                  let (arg', used1) := alpha_rename_expr rho used0 arg in
                  let (rest', used2) := go used1 rest in
                  (arg' :: rest', used2)
              end) used_callee args) as [argsr used_args] eqn:Hargs_rename.
  injection Hrename as <- <-.
  destruct (disjoint_names_app_l (free_vars_expr callee)
    ((fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end) args) (rename_range rho) Hdisj) as [Hdisj_callee Hdisj_args].
  inversion Htyped; subst.
  - (* TERS_CallExpr_MakeClosure *)
    simpl in Hcallee_rename; injection Hcallee_rename as <- <-.
    destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
      env Ω n rho R Rr Σ Σr args argsr used used_args
      (apply_lt_params σ (fn_params fdef))
      (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots)
      as [Σr' [Rr' [arg_rootsr
        [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
    + exact Hexpr.
    + match goal with
      | H : typed_args_roots_shadow_safe _ _ _ _ _ args
            (apply_lt_params σ (fn_params fdef)) _ _ arg_roots |- _ =>
          exact H
      end.
    + exact Hctx.
    + exact HnsR.
    + exact HnsRr.
    + exact HRr.
    + exact Hkeys.
    + exact Hroots.
    + exact HnocollR.
    + exact HnocollR'.
    + exact Hctx_used.
    + exact Hrange_used.
    + exact Hdisj_args.
    + apply params_alpha_refl.
    + exact Hargs_rename.
    + exists Σr', Rr', (root_sets_union arg_rootsr).
      split; [| split; [| split; [| split]]].
      * eapply TERS_CallExpr_MakeClosure; eauto.
        eapply check_make_closure_captures_sctx_with_env_alpha_forward;
          eauto using disjoint_names_app_l.
      * exact Hctx_r.
      * exact HnsRr'.
      * exact HRr'.
      * eapply root_sets_union_rename_equiv. exact Harg_roots.
  - (* TERS_CallExpr_Fn *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys param_tys) (params_of_tys param_tys) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys param_tys) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Fn.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_Closure *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys param_tys) (params_of_tys param_tys) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys param_tys) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Closure.
          - intros fname caps Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname caps used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_TypeForall: same structure as Fn/Closure *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys (map (subst_type_params_ty type_args) param_tys)) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_TypeForall.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_MixedForall: same structure as TypeForall *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys)))
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys))) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys
                (map (open_bound_ty σ)
                  (map (subst_type_params_ty type_args) param_tys))) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_MixedForall.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_Forall_Fn: same structure as TypeForall *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys (map (open_bound_ty σ) param_tys))
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys (map (open_bound_ty σ) param_tys)) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Forall_Fn.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
  - (* TERS_CallExpr_Forall_Closure: same structure as Forall_Fn *)
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
        as [Hkeys_env _].
      eapply Hkeys_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hkeys. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
        as [Hroots_env _].
      eapply proj1. eapply Hroots_env.
      - match goal with
        | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ _ _ _ |- _ => exact H
        end.
      - exact HnsR.
      - exact Hroots. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply rename_no_collision_on_weaken_names.
      - exact HnocollR'.
      - intros x Hin.
        eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
        + eapply typed_args_roots_shadow_safe_roots.
          match goal with
          | H : typed_args_roots_shadow_safe _ _ _ _ _ args _ _ _ _ |- _ => exact H
          end.
        + exact Hin. }
    destruct (Hcallee_ih R Rr Σ Σr used callee_r used_callee _ Σ1 R1 roots_callee
              ltac:(match goal with
                    | H : typed_env_roots_shadow_safe _ _ _ _ _ callee _ Σ1 R1 roots_callee |- _ =>
                        exact H
                    end)
              Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used
              Hdisj_callee Hcallee_rename)
      as [Σ1r [R1r [roots_callee_r [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
    assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        apply Hctx_used.
        assert (Hsame : sctx_same_bindings Σr Σ1r) by
          (eapply typed_env_structural_same_bindings;
           eapply typed_env_roots_structural;
           eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
        rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
        exact Hin. }
      assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used_callee).
      { intros x Hin.
        eapply alpha_rename_expr_used_extends; [exact Hcallee_rename |].
        exact (Hrange_used x Hin). }
      destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
        env Ω n rho R1 R1r Σ1 Σ1r args argsr used_callee used_args
        (params_of_tys (map (open_bound_ty σ) param_tys))
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots)
        as [Σr' [Rr' [arg_rootsr
          [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
      * exact Hexpr.
      * match goal with
        | H : typed_args_roots_shadow_safe _ _ _ _ _ args
              (params_of_tys (map (open_bound_ty σ) param_tys)) _ _ arg_roots |- _ =>
            exact H
        end.
      * exact Hctx1r.
      * exact HnsR1.
      * exact HnsR1r.
      * exact HR1r.
      * exact HkeysR1.
      * exact HrootsR1.
      * exact HnocollR1.
      * exact HnocollR'.
      * exact Hctx_used1.
      * exact Hrange_used1.
      * exact Hdisj_args.
      * apply params_alpha_refl.
      * exact Hargs_rename.
      * exists Σr', Rr',
          (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
        split; [| split; [| split; [| split]]].
        { eapply TERS_CallExpr_Forall_Closure.
          - intros fname' caps' Heq_r.
            subst callee_r.
            destruct (alpha_rename_expr_is_make_closure_inv
                rho used callee fname' caps' used_callee Hcallee_rename)
              as [fn0 [cs0 Hcallee_eq]].
            match goal with
            | H : forall fn cs, callee <> EMakeClosure fn cs |- _ =>
                exact (H fn0 cs0 Hcallee_eq)
            end.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto. }
        { exact Hctx_r. }
        { exact HnsRr'. }
        { exact HRr'. }
        { eapply root_set_equiv_trans.
          - apply root_set_union_equiv.
            + exact Hrootscallee_r.
            + eapply root_sets_union_rename_equiv. exact Harg_roots.
          - apply root_set_equiv_sym.
            apply root_set_union_rename_equiv. }
Qed.


Lemma alpha_rename_typed_env_roots_struct_shadow_safe_support_forward :
  forall env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots,
  (forall R0 R0r Σa Σb used0 e er0 used1 T0 Σa' R0' roots0,
      In e (map snd fields) ->
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
  typed_env_roots_shadow_safe env Ω n R Σ
    (EStruct sname lts args fields) T Σ' R' roots ->
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
  disjoint_names (free_vars_expr (EStruct sname lts args fields))
    (rename_range rho) ->
  alpha_rename_expr rho used (EStruct sname lts args fields) = (er, used') ->
  exists Σr' Rr' rootsr,
    typed_env_roots_shadow_safe env Ω n Rr Σr er T Σr' Rr' rootsr /\
    ctx_alpha rho Σ' Σr' /\
    root_env_no_shadow Rr' /\
    root_env_equiv Rr' (root_env_rename rho R') /\
    root_set_equiv rootsr (root_set_rename rho roots).
Proof.
  intros env Ω n rho R Rr Σ Σr sname lts args fields er used used'
    T Σ' R' roots Hexpr Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
    HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
              : list (string * expr) * list ident :=
              match fields0 with
              | [] => ([], used0)
              | (fname, e) :: rest =>
                  let (e', used1) := alpha_rename_expr rho used0 e in
                  let (rest', used2) := go used1 rest in
                  ((fname, e') :: rest', used2)
              end) used fields) as [fieldsr used_fields] eqn:Hfields.
  injection Hrename as <- <-.
  inversion Htyped; subst.
  destruct (alpha_rename_typed_fields_roots_shadow_safe_support_forward
    env Ω n rho lts args R Rr Σ Σr fields fieldsr used used_fields
    (Program.struct_fields sdef) Σ' R' roots)
    as [Σr' [Rr' [rootsr
      [Hfields_r [Hctx_r [HnsRr' [HRr' Hroots_equiv]]]]]]].
  - exact Hexpr.
  - match goal with
    | H : typed_fields_roots_shadow_safe _ _ _ lts args _ _ fields
          (Program.struct_fields sdef) _ _ roots |- _ =>
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
  - exact Hfields.
  - exists Σr', Rr', rootsr.
    split; [| split; [| split; [| split]]].
    + eapply TERS_Struct; eauto.
    + exact Hctx_r.
    + exact HnsRr'.
    + exact HRr'.
    + exact Hroots_equiv.
Qed.

Lemma alpha_rename_typed_env_roots_shadow_safe_full_support_forward :
  forall env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots,
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
  assert (Hsize : forall fuel env Ω n rho R Rr Σ Σr e er used used'
      T Σ' R' roots,
    expr_size e < fuel ->
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
      root_set_equiv rootsr (root_set_rename rho roots)).
  {
    induction fuel as [| fuel IH]; intros env Ω n rho R Rr Σ Σr e er
      used used' T Σ' R' roots Hlt Htyped Hctx HnsR HnsRr HRr Hkeys
      Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
    - lia.
    - destruct e.
      + eapply alpha_rename_typed_env_roots_trivial_shadow_safe_support_forward;
          try eassumption.
        left. reflexivity.
      + eapply alpha_rename_typed_env_roots_trivial_shadow_safe_support_forward;
          try eassumption.
        right. eexists. reflexivity.
      + eapply alpha_rename_typed_env_roots_var_shadow_safe_support_forward;
          eauto.
      + eapply (alpha_rename_typed_env_roots_let_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr m i t e1 e2 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e1 er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * intros xr used1 used2 e2r used3 roots1 R1 Σ1 R1r Σ1r
            roots1r T2 Σ2 R2 roots2 Hxr Hused2 He2 Htyped2 Hctx_body
            Hns_add HnsR1r Hlookup_x Hroots1_excl Henv1_excl HnocollR1
            Hnocoll_remove Hroots2_excl Henv2_excl HR1r Hroots1r HkeysR1
            HrootsR1 Hroots1_named Hctx_used2 Hrange_used2 Hdisj2.
          destruct (ctx_alpha_add_fresh_inv rho Σ1 Σ1r i xr t m Hctx_body)
            as [Hctx1 [Hfresh_ctx _]].
          assert (HnsR1 : root_env_no_shadow R1).
          { unfold root_env_no_shadow, root_env_add in Hns_add.
            simpl in Hns_add. inversion Hns_add; assumption. }
          destruct (root_env_sctx_support_fresh_renamed_let_init rho R1 R1r
            roots1 roots1r Σ1 Σ1r xr Hctx1 HnsR1 HnsR1r HR1r
            Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
            as [Hlookup_xr [Hroots1r_excl Henv1r_excl]].
          assert (Hns_add_r :
            root_env_no_shadow (root_env_add xr roots1r R1r)).
          { eapply root_env_no_shadow_add.
            - exact HnsR1r.
            - exact Hlookup_xr. }
          assert (HRadd :
            root_env_equiv (root_env_add xr roots1r R1r)
              (root_env_rename ((i, xr) :: rho)
                (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
          assert (Hkeys_add :
            root_env_sctx_keys_named (root_env_add i roots1 R1)
              (sctx_add i t m Σ1)).
          { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
          assert (Hroots_add :
            root_env_sctx_roots_named (root_env_add i roots1 R1)
              (sctx_add i t m Σ1)).
          { apply root_env_sctx_roots_named_add_binding; assumption. }
          assert (Hnocoll_add :
            rename_no_collision_on ((i, xr) :: rho)
              (root_env_names (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_no_collision_on;
              eassumption. }
          assert (HnsR2 : root_env_no_shadow R2).
          { eapply typed_env_roots_no_shadow.
            - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
            - exact Hns_add. }
          assert (HkeysR2 : root_env_sctx_keys_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
              as [Hkeys_env _].
            eapply Hkeys_env; eassumption. }
          assert (HrootsR2 : root_env_sctx_roots_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i t m Σ1) e2 T2 Σ2 R2 roots2)
              as [Hroots_env2 _].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_env2. }
          assert (Hroots2_named : root_set_sctx_roots_named roots2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i t m Σ1) e2 T2 Σ2 R2 roots2)
              as [_ Hroots_set2].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_set2. }
          assert (Hsame_body :
            sctx_same_bindings (sctx_add i t m Σ1) Σ2).
          { eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
          assert (HnocollR2_cons :
            rename_no_collision_on ((i, xr) :: rho) (root_env_names R2)).
          { eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings.
            - exact Hctx1.
            - exact HnsR2.
            - exact HkeysR2.
            - exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hnocoll_remove. }
          destruct (IH env Ω n ((i, xr) :: rho)
            (root_env_add i roots1 R1) (root_env_add xr roots1r R1r)
            (sctx_add i t m Σ1) (sctx_add xr t m Σ1r)
            e2 e2r used2 used3 T2 Σ2 R2 roots2)
            as [Σ2r [R2r [roots2r
              [Htyped2r [Hctx2r [HnsR2r [HR2r Hroots2r_cons]]]]]]].
          { simpl in Hlt. lia. }
          { exact Htyped2. }
          { exact Hctx_body. }
          { exact Hns_add. }
          { exact Hns_add_r. }
          { exact HRadd. }
          { exact Hkeys_add. }
          { exact Hroots_add. }
          { exact Hnocoll_add. }
          { exact HnocollR2_cons. }
          { exact Hctx_used2. }
          { exact Hrange_used2. }
          { exact Hdisj2. }
          { exact He2. }
          assert (Hnocoll_x :
            rename_no_collision_for ((i, xr) :: rho) i (root_env_names R2)).
          { eapply root_env_sctx_keys_named_added_no_collision_for_head.
            - exact Hctx1.
            - eapply root_env_sctx_keys_named_same_bindings.
              + apply sctx_same_bindings_sym. exact Hsame_body.
              + exact HkeysR2.
            - exact Hfresh_ctx. }
          assert (HRremove :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename rho (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_equiv;
              eassumption. }
          assert (Hroots2r :
            root_set_equiv roots2r (root_set_rename rho roots2)).
          { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
          assert (Hroots2r_excl : roots_exclude xr roots2r).
          { eapply roots_exclude_shadow_safe_rename_body.
            - exact Hctx1.
            - eapply root_set_sctx_roots_named_strip_added_same_bindings.
              + exact Hroots2_excl.
              + exact Hroots2_named.
              + exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hroots2r_cons.
            - exact Hroots2_excl. }
          assert (Hremove_ext :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename ((i, xr) :: rho) (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
              eassumption. }
          assert (Henv2r_excl :
            root_env_excludes xr (root_env_remove xr R2r)).
          { eapply root_env_excludes_shadow_safe_rename_body.
            - exact Hctx1.
            - apply root_env_no_shadow_remove. exact HnsR2.
            - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
                eassumption.
            - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
                eassumption.
            - exact Hfresh_ctx.
            - exact Hremove_ext.
            - exact Henv2_excl. }
	          exists Σ2r, R2r, roots2r.
	          refine (conj Hlookup_xr
	            (conj Hroots1r_excl
	            (conj Henv1r_excl
	            (conj Htyped2r
	            (conj Hctx2r
	            (conj HnsR2r
	            (conj HRremove
	            (conj Hroots2r
	            (conj Hroots2r_excl Henv2r_excl))))))))).
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_letinfer_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr m i e1 e2 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e1 er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * intros xr used1 used2 e2r used3 T1 roots1 R1 Σ1 R1r Σ1r
            roots1r T2 Σ2 R2 roots2 Hxr Hused2 He2 Htyped2 Hctx_body
            Hns_add HnsR1r Hlookup_x Hroots1_excl Henv1_excl HnocollR1
            Hnocoll_remove Hroots2_excl Henv2_excl HR1r Hroots1r HkeysR1
            HrootsR1 Hroots1_named Hctx_used2 Hrange_used2 Hdisj2.
          destruct (ctx_alpha_add_fresh_inv rho Σ1 Σ1r i xr T1 m Hctx_body)
            as [Hctx1 [Hfresh_ctx _]].
          assert (HnsR1 : root_env_no_shadow R1).
          { unfold root_env_no_shadow, root_env_add in Hns_add.
            simpl in Hns_add. inversion Hns_add; assumption. }
          destruct (root_env_sctx_support_fresh_renamed_let_init rho R1 R1r
            roots1 roots1r Σ1 Σ1r xr Hctx1 HnsR1 HnsR1r HR1r
            Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
            as [Hlookup_xr [Hroots1r_excl Henv1r_excl]].
          assert (Hns_add_r :
            root_env_no_shadow (root_env_add xr roots1r R1r)).
          { eapply root_env_no_shadow_add.
            - exact HnsR1r.
            - exact Hlookup_xr. }
          assert (HRadd :
            root_env_equiv (root_env_add xr roots1r R1r)
              (root_env_rename ((i, xr) :: rho)
                (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
          assert (Hkeys_add :
            root_env_sctx_keys_named (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1)).
          { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
          assert (Hroots_add :
            root_env_sctx_roots_named (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1)).
          { apply root_env_sctx_roots_named_add_binding; assumption. }
          assert (Hnocoll_add :
            rename_no_collision_on ((i, xr) :: rho)
              (root_env_names (root_env_add i roots1 R1))).
          { eapply root_env_add_shadow_safe_rename_no_collision_on;
              eassumption. }
          assert (HnsR2 : root_env_no_shadow R2).
          { eapply typed_env_roots_no_shadow.
            - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
            - exact Hns_add. }
          assert (HkeysR2 : root_env_sctx_keys_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
              as [Hkeys_env _].
            eapply Hkeys_env; eassumption. }
          assert (HrootsR2 : root_env_sctx_roots_named R2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1) e2 T2 Σ2 R2 roots2)
              as [Hroots_env2 _].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_env2. }
          assert (Hroots2_named : root_set_sctx_roots_named roots2 Σ2).
          { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
              as [Hroots_env _].
            destruct (Hroots_env (root_env_add i roots1 R1)
              (sctx_add i T1 m Σ1) e2 T2 Σ2 R2 roots2)
              as [_ Hroots_set2].
            - exact Htyped2.
            - exact Hns_add.
            - exact Hroots_add.
            - exact Hroots_set2. }
          assert (Hsame_body :
            sctx_same_bindings (sctx_add i T1 m Σ1) Σ2).
          { eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
          assert (HnocollR2_cons :
            rename_no_collision_on ((i, xr) :: rho) (root_env_names R2)).
          { eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings.
            - exact Hctx1.
            - exact HnsR2.
            - exact HkeysR2.
            - exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hnocoll_remove. }
          destruct (IH env Ω n ((i, xr) :: rho)
            (root_env_add i roots1 R1) (root_env_add xr roots1r R1r)
            (sctx_add i T1 m Σ1) (sctx_add xr T1 m Σ1r)
            e2 e2r used2 used3 T2 Σ2 R2 roots2)
            as [Σ2r [R2r [roots2r
              [Htyped2r [Hctx2r [HnsR2r [HR2r Hroots2r_cons]]]]]]].
          { simpl in Hlt. lia. }
          { exact Htyped2. }
          { exact Hctx_body. }
          { exact Hns_add. }
          { exact Hns_add_r. }
          { exact HRadd. }
          { exact Hkeys_add. }
          { exact Hroots_add. }
          { exact Hnocoll_add. }
          { exact HnocollR2_cons. }
          { exact Hctx_used2. }
          { exact Hrange_used2. }
          { exact Hdisj2. }
          { exact He2. }
          assert (Hnocoll_x :
            rename_no_collision_for ((i, xr) :: rho) i (root_env_names R2)).
          { eapply root_env_sctx_keys_named_added_no_collision_for_head.
            - exact Hctx1.
            - eapply root_env_sctx_keys_named_same_bindings.
              + apply sctx_same_bindings_sym. exact Hsame_body.
              + exact HkeysR2.
            - exact Hfresh_ctx. }
          assert (HRremove :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename rho (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_equiv;
              eassumption. }
          assert (Hroots2r :
            root_set_equiv roots2r (root_set_rename rho roots2)).
          { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
          assert (Hroots2r_excl : roots_exclude xr roots2r).
          { eapply roots_exclude_shadow_safe_rename_body.
            - exact Hctx1.
            - eapply root_set_sctx_roots_named_strip_added_same_bindings.
              + exact Hroots2_excl.
              + exact Hroots2_named.
              + exact Hsame_body.
            - exact Hfresh_ctx.
            - exact Hroots2r_cons.
            - exact Hroots2_excl. }
          assert (Hremove_ext :
            root_env_equiv (root_env_remove xr R2r)
              (root_env_rename ((i, xr) :: rho) (root_env_remove i R2))).
          { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
              eassumption. }
          assert (Henv2r_excl :
            root_env_excludes xr (root_env_remove xr R2r)).
          { eapply root_env_excludes_shadow_safe_rename_body.
            - exact Hctx1.
            - apply root_env_no_shadow_remove. exact HnsR2.
            - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
                eassumption.
            - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
                eassumption.
            - exact Hfresh_ctx.
            - exact Hremove_ext.
            - exact Henv2_excl. }
	          exists Σ2r, R2r, roots2r.
	          refine (conj Hlookup_xr
	            (conj Hroots1r_excl
	            (conj Henv1r_excl
	            (conj Htyped2r
	            (conj Hctx2r
	            (conj HnsR2r
	            (conj HRremove
	            (conj Hroots2r
	            (conj Hroots2r_excl Henv2r_excl))))))))).
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply alpha_rename_typed_env_roots_fn_shadow_safe_support_forward;
          eauto.
	      + injection Hrename as <- <-.
	        inversion Htyped; subst.
	        * do 3 eexists.
	          repeat split; try exact Hctx; try exact HnsRr; try exact HRr;
	            try apply root_set_equiv_refl.
	          eapply TERS_MakeClosure; eauto.
	          eapply check_make_closure_captures_sctx_with_env_alpha_forward; eauto.
	        * do 3 eexists.
	          repeat split; try exact Hctx; try exact HnsRr; try exact HRr;
	            try apply root_set_equiv_refl.
	          eapply TERS_MakeClosure_Static; eauto.
	          eapply check_make_closure_captures_sctx_alpha_forward; eauto.
      + eapply alpha_rename_typed_env_roots_place_shadow_safe_support_forward;
          eauto.
	      + eapply (alpha_rename_typed_env_roots_call_shadow_safe_support_forward
	          env Ω n rho R Rr Σ Σr i l er used used' T Σ' R' roots).
	        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
	            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_call_arg_lt i l e0 Hin) as Harg_lt.
            simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
	        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * exact Hrename.
	      + eapply (alpha_rename_typed_env_roots_call_generic_shadow_safe_support_forward
	          env Ω n rho R Rr Σ Σr i l l0 er used used' T Σ' R' roots).
	        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
	            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
	            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
	          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
	            T0 Σa' R0' roots0).
	          { pose proof (expr_size_call_generic_arg_lt i l l0 e0 Hin)
	              as Harg_lt.
	            simpl in *. lia. }
	          all: eassumption.
	        * exact Htyped.
	        * exact Hctx.
	        * exact HnsR.
	        * exact HnsRr.
	        * exact HRr.
	        * exact Hkeys.
	        * exact Hroots.
	        * exact HnocollR.
	        * exact HnocollR'.
	        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * exact Hrename.
	      + eapply alpha_rename_typed_env_roots_call_expr_fn_shadow_safe_support_forward.
        * (* callee IH *)
          intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_callexpr_callee_lt e l) as Hcallee_lt.
            simpl in *. lia. }
          all: eassumption.
        * (* args IH *)
          intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_callexpr_arg_lt e l e0 Hin) as Harg_lt.
            simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + simpl in Hrename.
        simpl in Hdisj.
        destruct (disjoint_names_app_l (free_vars_expr e)
          ((fix go (args0 : list expr) : list ident :=
              match args0 with
              | [] => []
              | arg :: rest => free_vars_expr arg ++ go rest
              end) l0) (rename_range rho) Hdisj) as [Hdisj_callee Hdisj_args].
        destruct (alpha_rename_expr rho used e) as [callee_r used0] eqn:Hcallee.
        destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
                    : list expr * list ident :=
                    match args0 with
                    | [] => ([], used0)
                    | arg :: rest =>
                        let (arg', used1) := alpha_rename_expr rho used0 arg in
                        let (rest', used2) := go used1 rest in
                        (arg' :: rest', used2)
                    end) used0 l0) as [argsr used_args] eqn:Hargs.
        injection Hrename as <- <-.
        inversion Htyped; subst.
        assert (HnsR1 : root_env_no_shadow R1).
        { eapply typed_env_roots_no_shadow.
          - eapply typed_env_roots_shadow_safe_roots.
            match goal with
            | H : typed_env_roots_shadow_safe _ _ _ _ _ e _ _ _ _ |- _ => exact H
            end.
          - exact HnsR. }
        assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
        { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
            as [Hkeys_env _].
          eapply Hkeys_env.
          - match goal with
            | H : typed_env_roots_shadow_safe _ _ _ _ _ e _ _ _ _ |- _ => exact H
            end.
          - exact HnsR.
          - exact Hkeys. }
        assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
        { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
            as [Hroots_env _].
          eapply proj1. eapply Hroots_env.
          - match goal with
            | H : typed_env_roots_shadow_safe _ _ _ _ _ e _ _ _ _ |- _ => exact H
            end.
          - exact HnsR.
          - exact Hroots. }
        assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
        { eapply rename_no_collision_on_weaken_names.
          - exact HnocollR'.
          - intros x Hin.
            eapply (proj1 (proj2 (typed_roots_root_env_names_subset_mutual env Ω n))).
            + eapply typed_args_roots_shadow_safe_roots.
              match goal with
              | H : typed_args_roots_shadow_safe _ _ _ _ _ l0 _ _ _ _ |- _ => exact H
              end.
            + exact Hin. }
        destruct (IH env Ω n rho R Rr Σ Σr e callee_r used used0
                  (MkTy u (TTypeForall type_params bounds body_ty))
                  Σ1 R1 roots_callee) as
          [Σ1r [R1r [roots_callee_r
            [H_callee_r [Hctx1r [HnsR1r [HR1r Hrootscallee_r]]]]]]].
        * pose proof (expr_size_callexpr_generic_callee_lt e l l0) as Hcallee_lt.
          simpl in *. lia.
        * match goal with
          | H : typed_env_roots_shadow_safe _ _ _ _ _ e _ Σ1 R1 roots_callee |- _ => exact H
          end.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR1.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj_callee.
        * exact Hcallee.
        * assert (Hctx_used1 : forall x, In x (ctx_names Σ1r) -> In x used0).
          { intros x Hin.
            eapply alpha_rename_expr_used_extends; [exact Hcallee |].
            apply Hctx_used.
            assert (Hsame : sctx_same_bindings Σr Σ1r) by
              (eapply typed_env_structural_same_bindings;
               eapply typed_env_roots_structural;
               eapply typed_env_roots_shadow_safe_roots; exact H_callee_r).
            rewrite (sctx_same_bindings_names_alpha Σr Σ1r Hsame) in Hin.
            exact Hin. }
          assert (Hrange_used1 : forall x, In x (rename_range rho) -> In x used0).
          { intros x Hin.
            eapply alpha_rename_expr_used_extends; [exact Hcallee |].
            exact (Hrange_used x Hin). }
          destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
            env Ω n rho R1 R1r Σ1 Σ1r l0 argsr used0 used_args
            (params_of_tys (map (subst_type_params_ty l) param_tys))
            (params_of_tys (map (subst_type_params_ty l) param_tys)) Σ' R' arg_roots)
            as [Σr' [Rr' [arg_rootsr
              [Hargs_r [Hctx_r [HnsRr' [HRr' Harg_roots]]]]]]].
          -- intros R0 R0r Σa Σb used1 e0 er0 used2 T0 Σa' R0' roots0
               Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
               Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
             eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used1 used2
               T0 Σa' R0' roots0).
             ++ pose proof (expr_size_callexpr_generic_arg_lt e l l0 e0 Hin) as Harg_lt.
                simpl in *. lia.
             ++ exact Htyped0.
             ++ exact Halpha.
             ++ exact HnsR0.
             ++ exact HnsR0r.
             ++ exact HR0r.
             ++ exact Hkeys0.
             ++ exact Hroots0.
             ++ exact Hnocoll0.
             ++ exact Hnocoll0'.
             ++ exact Hcu.
             ++ exact Hru.
             ++ exact Hd.
             ++ exact Hr.
          -- match goal with
             | H : typed_args_roots_shadow_safe _ _ _ _ _ l0
                   (params_of_tys (map (subst_type_params_ty l) param_tys)) _ _ arg_roots |- _ => exact H
             end.
          -- exact Hctx1r.
          -- exact HnsR1.
          -- exact HnsR1r.
          -- exact HR1r.
          -- exact HkeysR1.
          -- exact HrootsR1.
          -- exact HnocollR1.
          -- exact HnocollR'.
          -- exact Hctx_used1.
          -- exact Hrange_used1.
          -- exact Hdisj_args.
          -- apply params_alpha_refl.
          -- exact Hargs.
          -- exists Σr', Rr',
              (root_set_union roots_callee_r (root_sets_union arg_rootsr)).
             split; [| split; [| split; [| split]]].
             ++ eapply TERS_CallExprGeneric_TypeForall; eauto.
             ++ exact Hctx_r.
             ++ exact HnsRr'.
             ++ exact HRr'.
             ++ eapply root_set_equiv_trans.
                ** apply root_set_union_equiv.
                   --- exact Hrootscallee_r.
                   --- eapply root_sets_union_rename_equiv. exact Harg_roots.
                ** apply root_set_equiv_sym.
                   apply root_set_union_rename_equiv.
      + eapply (alpha_rename_typed_env_roots_struct_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr s l l0 l1 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { pose proof (expr_size_struct_field_snd_lt s l l0 l1 e0 Hin)
              as Hfield_lt.
            simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * exact Hrename.
	      + simpl in Hrename.
	        destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
	                    : list expr * list ident :=
	                    match args0 with
	                    | [] => ([], used0)
	                    | arg :: rest =>
	                        let (arg', used1) := alpha_rename_expr rho used0 arg in
	                        let (rest', used2) := go used1 rest in
	                        (arg' :: rest', used2)
	                    end) used l1) as [payloadsr used_payloads] eqn:Hpayloads.
	        injection Hrename as <- <-.
	        inversion Htyped; subst.
	        destruct (alpha_rename_typed_args_roots_shadow_safe_support_forward
	          env Ω n rho R Rr Σ Σr l1 payloadsr used used_payloads
	          (params_of_tys
	            (map (instantiate_enum_variant_field_ty l l0)
	              (enum_variant_fields vdef)))
	          (params_of_tys
	            (map (instantiate_enum_variant_field_ty l l0)
	              (enum_variant_fields vdef))) Σ' R' payload_roots)
	          as [Σr' [Rr' [payload_rootsr
	            [Hpayloads_r [Hctx_r [HnsRr' [HRr' Hpayload_roots]]]]]]].
	        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
	            Hin Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
	            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
	          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
	            T0 Σa' R0' roots0).
	          { pose proof (expr_size_enum_payload_lt s s0 l l0 l1 e0 Hin)
	              as Hpayload_lt.
	            simpl in *. lia. }
	          all: eassumption.
	        * match goal with
	          | H : typed_args_roots_shadow_safe _ _ _ _ _ l1
	                (params_of_tys
	                  (map (instantiate_enum_variant_field_ty l l0)
	                    (enum_variant_fields vdef))) _ _ payload_roots |- _ =>
	              exact H
	          end.
	        * exact Hctx.
	        * exact HnsR.
	        * exact HnsRr.
	        * exact HRr.
	        * exact Hkeys.
	        * exact Hroots.
	        * exact HnocollR.
	        * exact HnocollR'.
	        * exact Hctx_used.
	        * exact Hrange_used.
	        * exact Hdisj.
	        * apply params_alpha_refl.
		        * exact Hpayloads.
		        * exists Σr', Rr', (root_sets_union payload_rootsr).
		          split; [| split; [| split; [| split]]].
		          -- eapply TERS_Enum; eauto.
		          -- exact Hctx_r.
		          -- exact HnsRr'.
		          -- exact HRr'.
		          -- eapply root_sets_union_rename_equiv. exact Hpayload_roots.
		      + simpl in Hrename.
		        destruct (alpha_rename_expr rho used e) as [scrutr used_scrut] eqn:Hscrut.
		        destruct ((fix go
		                    (used0 : list ident)
		                    (branches0 : list (string * list ident * expr)) {struct branches0}
		                    : list (string * list ident * expr) * list ident :=
		                    match branches0 with
		                    | [] => ([], used0)
		                    | (variant_name, binders, e0) :: rest =>
		                        let binder_seed := binders ++ free_vars_expr e0 ++ used0 in
		                        let '(binders', rho_branch, used1) :=
		                          alpha_rename_idents rho binder_seed binders in
		                        let (e0', used2) := alpha_rename_expr rho_branch used1 e0 in
		                        let (rest', used3) := go used2 rest in
		                        ((variant_name, binders', e0') :: rest', used3)
		                    end) used_scrut l) as [branchesr used_branches] eqn:Hbranches.
		        injection Hrename as <- <-.
		        destruct (disjoint_names_app_l (free_vars_expr e)
		          ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
		              match branches0 with
		              | [] => []
		              | (_, _, e0) :: rest => free_vars_expr e0 ++ go rest
		              end) l) (rename_range rho) Hdisj)
		          as [Hdisj_scrut Hdisj_branches].
		        inversion Htyped; subst.
		        assert (HnsR1 : root_env_no_shadow R1).
		        { eapply typed_env_roots_no_shadow.
		          - eapply typed_env_roots_shadow_safe_roots. eassumption.
		          - exact HnsR. }
			        match goal with
			        | Htail0 : typed_match_tail_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _
			            ?Rout _ _ _ |- _ =>
			            assert (HnsRout : root_env_no_shadow Rout)
			        end.
				        { match goal with
				          | Hpayload : ?Rpayload =
		              root_env_add_params_roots_same ?ps ?roots R1,
		            Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
		              ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
		              ?roots_head0,
		            Hout : ?Rout = root_env_remove_match_params ?ps
		              ?Rhead_payload |- root_env_no_shadow ?Rout =>
		              rewrite Hout;
		              apply root_env_remove_match_params_no_shadow;
		                eapply typed_env_roots_no_shadow;
		              [eapply typed_env_roots_shadow_safe_roots; exact Hhead
		              | subst Rpayload;
		                eapply root_env_add_params_roots_same_no_shadow; eauto]
		          | Hhead : typed_env_roots_shadow_safe env Ω n
		              (root_env_add_params_roots_same ?ps ?roots R1)
		              ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
		              ?roots_head0
		            |- root_env_no_shadow
		                 (root_env_remove_match_params ?ps ?Rhead_payload) =>
		              apply root_env_remove_match_params_no_shadow;
		              eapply typed_env_roots_no_shadow;
		              [eapply typed_env_roots_shadow_safe_roots; exact Hhead
		              | eapply root_env_add_params_roots_same_no_shadow; eauto]
		          end. }
		        assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
		        { eapply rename_no_collision_on_weaken_names.
			          - exact HnocollR'.
			          - intros x Hin.
			            match goal with
			            | Hpayload : ?Rpayload =
			                root_env_add_params_roots_same ?ps ?roots R1,
			              Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
			                ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
			                ?roots_head0,
			              Hout : ?Rout = root_env_remove_match_params ?ps
			                ?Rhead_payload,
			              Hnone : root_env_lookup_params_none_b ?ps R1 = true |- _ =>
			                rewrite Hout;
			                eapply root_env_remove_match_params_preserve_name_not_params
			            | Hhead : typed_env_roots_shadow_safe env Ω n
			                (root_env_add_params_roots_same ?ps ?roots R1)
			                ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
			                ?roots_head0,
			              Hnone : root_env_lookup_params_none_b ?ps R1 = true
			                |- In x (root_env_names
			                     (root_env_remove_match_params ?ps ?Rhead_payload)) =>
			                eapply root_env_remove_match_params_preserve_name_not_params
			            end.
			            + intros y Hy Heq. subst y.
			              match goal with
			              | Hnone : root_env_lookup_params_none_b ?ps R1 = true |- _ =>
			                  pose proof (root_env_lookup_params_none_b_not_in
			                    _ _ _ Hnone Hy) as Hnot;
			                  apply Hnot; exact Hin
			              end.
			            + eapply typed_env_roots_root_env_names_subset.
			              * eapply typed_env_roots_shadow_safe_roots.
			                match goal with
			                | Hhead : typed_env_roots_shadow_safe env Ω n ?Rpayload
			                    ?Σpayload ?e0 ?T0 ?Σhead_payload ?Rhead_payload
			                    ?roots_head0 |- _ => exact Hhead
			                end.
			              * match goal with
			                | Hpayload : ?Rpayload =
			                    root_env_add_params_roots_same ?ps ?roots R1 |- _ =>
			                    subst Rpayload;
			                    apply root_env_add_params_roots_same_preserve_name;
			                    exact Hin
			                | |- In x (root_env_names
			                    (root_env_add_params_roots_same ?ps ?roots R1)) =>
			                    apply root_env_add_params_roots_same_preserve_name;
			                    exact Hin
			                end. }
		        destruct (IH env Ω n rho R Rr Σ Σr e scrutr used used_scrut
		          T_scrut Σ1 R1 roots_scrut)
		          as [Σr1 [Rr1 [roots_scrutr
		            [Hscrut_r [Hctx1_r [HnsRr1 [HRr1 Hroots_scrut]]]]]]].
		        * simpl in *. lia.
		        * match goal with
		          | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                Σ1 R1 roots_scrut |- _ => exact H
		          end.
		        * exact Hctx.
		        * exact HnsR.
		        * exact HnsRr.
		        * exact HRr.
		        * exact Hkeys.
		        * exact Hroots.
		        * exact HnocollR.
		        * exact HnocollR1.
		        * exact Hctx_used.
		        * exact Hrange_used.
		        * exact Hdisj_scrut.
		        * exact Hscrut.
		        * assert (Hctx_used1 : forall y, In y (ctx_names Σr1) -> In y used_scrut).
		          { intros y Hy.
		            eapply alpha_rename_expr_used_extends.
		            - exact Hscrut.
		            - apply Hctx_used.
		              rewrite <- (sctx_same_bindings_names_alpha Σr Σr1).
		              + exact Hy.
		              + eapply typed_env_structural_same_bindings.
		                eapply typed_env_roots_structural.
		                eapply typed_env_roots_shadow_safe_roots. exact Hscrut_r. }
		          assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used_scrut).
		          { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
			          destruct (alpha_rename_match_branches_lookup_payload_forward
			            rho used_scrut l branchesr used_branches
			            (Program.enum_variant_name v_head) binders_head e_head
			            Hbranches
			            ltac:(match goal with
			              | H : lookup_expr_branch_binders
			                      (Program.enum_variant_name v_head) l =
			                    Some binders_head |- _ => exact H
			            end)
		            ltac:(match goal with
		              | H : lookup_expr_branch (Program.enum_variant_name v_head) l =
		                    Some e_head |- _ => exact H
		            end))
		            as [binders_head_r [rho_head [e_headr
		              [used_head_pre [used_head [used_head_out
		                [Hbinders_head_r [Hlookup_head_r
		                  [Hrename_head_binders [Hrename_head
		                    Hused_head_pre]]]]]]]]]].
			          pose proof (lookup_expr_branch_binders_expr_in_alpha _ _ _ _
			            ltac:(match goal with
			              | H : lookup_expr_branch_binders
			                      (Program.enum_variant_name v_head) l =
			                    Some binders_head |- _ => exact H
			            end)
		            ltac:(match goal with
		              | H : lookup_expr_branch (Program.enum_variant_name v_head) l =
		                    Some e_head |- _ => exact H
		            end)) as Hhead_in.
			          match goal with
			          | H : match_payload_params binders_head lts args v_head =
			                infer_ok ps_head |- _ =>
			              destruct (match_binder_params_alpha_rename_idents
			                rho (binders_head ++ free_vars_expr e_head ++ used_head_pre)
			                binders_head binders_head_r rho_head used_head
		                (instantiate_enum_variant_field_tys lts args v_head)
		                ps_head Hrename_head_binders H)
		              as [ps_head_r [Hparams_head_r [Hparams_head_alpha
		                Hrename_head_params]]]
		          end.
		          assert (Hparams_head_nodup_r :
		            params_names_nodup_b ps_head_r = true).
		          { apply params_names_nodup_b_complete_alpha.
		            rewrite (match_binder_params_names _ _ _ Hparams_head_r).
		            eapply alpha_rename_idents_outputs_nodup.
		            exact Hrename_head_binders. }
		          assert (Hctx_head_none_r :
		            ctx_lookup_params_none_b ps_head_r Σr1 = true).
		          { eapply ctx_lookup_params_none_b_fresh_used
		              with (used := used_head_pre).
		            - intros y Hy.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - rewrite (match_binder_params_names _ _ _ Hparams_head_r).
		              eapply Forall_fresh_weaken.
		              + intros y Hy.
		                apply in_or_app. right. apply in_or_app. right.
		                exact Hy.
		              + eapply alpha_rename_idents_fresh_used.
		                exact Hrename_head_binders. }
		          assert (Hctx_head_payload :
		            ctx_alpha rho_head
		              (sctx_add_params ps_head Σ1)
		              (sctx_add_params ps_head_r Σr1)).
		          { unfold sctx_add_params, ctx_add_params.
		            eapply alpha_rename_params_ctx_alpha_extend_tail.
		            - exact Hrename_head_params.
		            - exact Hctx1_r.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hrange_used1. exact Hy. }
		          assert (Hkeys_R1 : root_env_sctx_keys_named R1 Σ1).
		          { match goal with
		            | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                  Σ1 R1 roots_scrut |- _ =>
		                destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                  as [Hkeys_env _];
		                eapply Hkeys_env; eassumption
		            end. }
		          assert (Hroots_R1 : root_env_sctx_roots_named R1 Σ1).
		          { match goal with
		            | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                  Σ1 R1 roots_scrut |- _ =>
		                destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                  as [Hroots_env _];
		                destruct (Hroots_env R Σ e T_scrut Σ1 R1 roots_scrut)
		                  as [Hroots_env1 _]; eauto
		            end. }
		          assert (Hkeys_Rr1 : root_env_sctx_keys_named Rr1 Σr1).
		          { eapply root_env_sctx_keys_named_rename; eassumption. }
		          assert (Hroots_Rr1 : root_env_sctx_roots_named Rr1 Σr1).
		          { eapply root_env_sctx_roots_named_rename.
		            - exact Hctx1_r.
		            - exact HnsR1.
		            - exact HRr1.
		            - exact Hroots_R1. }
		          assert (Hroots_scrut_named :
		            root_set_sctx_roots_named roots_scrut Σ1).
		          { match goal with
		            | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                  Σ1 R1 roots_scrut |- _ =>
		                destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                  as [Hroots_env _];
		                destruct (Hroots_env R Σ e T_scrut Σ1 R1 roots_scrut)
		                  as [_ Hroots_expr]; eauto
		            end. }
		          assert (Hroot_head_none_r :
		            root_env_lookup_params_none_b ps_head_r Rr1 = true).
		          { eapply root_env_lookup_params_none_b_from_sctx_keys;
		            eassumption. }
		          assert (Hroots_scrut_excl :
		            roots_exclude_params ps_head roots_scrut).
		          { unfold roots_exclude_params.
		            apply Forall_forall. intros x Hin.
		            eapply root_set_sctx_roots_named_fresh_exclude.
		            - exact Hroots_scrut_named.
		            - eapply ctx_lookup_params_none_b_not_in_names.
		              match goal with
		              | H : ctx_lookup_params_none_b ps_head Σ1 = true |- _ =>
		                  exact H
		              end.
		              exact Hin. }
		          assert (Henv_excl_R1 :
		            root_env_excludes_params ps_head R1).
		          { unfold root_env_excludes_params.
		            apply Forall_forall. intros x Hin.
		            eapply root_env_sctx_roots_named_fresh_excludes.
		            - exact Hroots_R1.
		            - eapply ctx_lookup_params_none_b_not_in_names.
		              match goal with
		              | H : ctx_lookup_params_none_b ps_head Σ1 = true |- _ =>
		                  exact H
		              end.
		              exact Hin. }
		          set (R_payload :=
		            root_env_add_params_roots_same ps_head roots_scrut R1) in *.
		          pose (R_payload_head_r :=
		            root_env_add_params_roots_same ps_head_r roots_scrutr Rr1).
		          assert (Hroots_scrutr_branch :
		            root_set_equiv roots_scrutr
		              (root_set_rename rho_head roots_scrut)).
		          { eapply root_set_equiv_trans.
		            - exact Hroots_scrut.
		            - apply root_set_equiv_sym.
		              eapply alpha_rename_params_root_set_rename_excluded.
		              + exact Hrename_head_params.
		              + exact Hroots_scrut_excl. }
		          assert (HRpayload_head_r :
		            root_env_equiv R_payload_head_r
		              (root_env_rename rho_head R_payload)).
		          { unfold R_payload_head_r. subst R_payload.
		            eapply alpha_rename_params_root_env_add_params_roots_same_rename_equiv.
		            - exact Hrename_head_params.
		            - exact HnsR1.
			            - assumption.
			            - assumption.
		            - exact Hroots_scrut_excl.
		            - exact Henv_excl_R1.
		            - exact HRr1.
		            - exact Hroots_scrutr_branch. }
		          assert (Hkeys_payload_head :
		            root_env_sctx_keys_named R_payload
		              (sctx_add_params ps_head Σ1)).
		          { subst R_payload.
		            apply root_env_sctx_keys_named_add_params_roots_same.
		            exact Hkeys_R1. }
		          assert (Hroots_payload_head :
		            root_env_sctx_roots_named R_payload
		              (sctx_add_params ps_head Σ1)).
		          { subst R_payload.
		            apply root_env_sctx_roots_named_add_params_roots_same;
		              assumption. }
		          assert (Hns_payload_head : root_env_no_shadow R_payload).
		          { subst R_payload.
		            eapply root_env_add_params_roots_same_no_shadow; eauto. }
		          assert (Hns_payload_head_r :
		            root_env_no_shadow R_payload_head_r).
		          { unfold R_payload_head_r.
		            eapply root_env_add_params_roots_same_no_shadow; eauto. }
		          assert (Hnocoll_payload_head :
		            rename_no_collision_on rho_head
		              (root_env_names R_payload)).
		          { subst R_payload.
		            eapply alpha_rename_params_root_env_add_params_roots_same_no_collision_on.
		            - exact Hrename_head_params.
		            - exact Hctx1_r.
		            - exact Hkeys_R1.
			            - assumption.
			            - assumption.
			            - assumption.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hrange_used1. exact Hy.
		            - exact HnocollR1. }
		          assert (Hnocoll_head_output :
		            rename_no_collision_on rho_head
		              (root_env_names R_head_payload)).
		          { eapply alpha_rename_params_root_env_remove_match_params_no_collision_on.
		            - exact Hrename_head_params.
		            - exact Hctx1_r.
		            - eapply typed_env_roots_no_shadow.
		              + eapply typed_env_roots_shadow_safe_roots.
		                match goal with
		                | H : typed_env_roots_shadow_safe env Ω n R_payload
		                      (sctx_add_params ps_head Σ1) e_head T_head
		                      Σ_head_payload R_head_payload roots_head |- _ =>
		                    exact H
		                end.
		              + exact Hns_payload_head.
		            - match goal with
		              | H : typed_env_roots_shadow_safe env Ω n R_payload
		                    (sctx_add_params ps_head Σ1) e_head T_head
		                    Σ_head_payload R_head_payload roots_head |- _ =>
		                  destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                    as [Hkeys_env _];
		                  eapply root_env_sctx_keys_named_same_bindings;
		                  [ apply sctx_same_bindings_sym;
		                    eapply typed_env_structural_same_bindings;
		                    eapply typed_env_roots_structural;
		                    eapply typed_env_roots_shadow_safe_roots; exact H
		                  | eapply Hkeys_env; eassumption ]
		              end.
		            - match goal
		              with H : params_names_nodup_b ps_head = true |- _ =>
		                exact H
		              end.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hctx_used1. exact Hy.
		            - intros y Hy. apply in_or_app. right.
		              apply in_or_app. right.
		              apply Hused_head_pre. apply Hrange_used1. exact Hy.
		            - exact HnocollR'. }
		             destruct (IH env Ω n rho_head R_payload R_payload_head_r
		               (sctx_add_params ps_head Σ1)
		               (sctx_add_params ps_head_r Σr1) e_head e_headr
		               used_head used_head_out T_head Σ_head_payload
		               R_head_payload roots_head)
		               as [Σ_head_payload_r [R_head_payload_r [roots_headr
		                 [Hhead_r [Hctx_head_payload_r
		                   [HnsR_head_payload_r [HRhead_payload_r
		                     Hroots_head]]]]]]].
			             ++ pose proof (expr_size_match_branch_lt e l
			                  (Program.enum_variant_name v_head) binders_head e_head
			                  Hhead_in).
		                simpl in *. lia.
		             ++ match goal with
		                | H : typed_env_roots_shadow_safe env Ω n R_payload
		                      (sctx_add_params ps_head Σ1) e_head T_head
		                      Σ_head_payload R_head_payload roots_head |- _ =>
		                    exact H
		                end.
		             ++ exact Hctx_head_payload.
		             ++ exact Hns_payload_head.
		             ++ exact Hns_payload_head_r.
		             ++ exact HRpayload_head_r.
		             ++ exact Hkeys_payload_head.
		             ++ exact Hroots_payload_head.
		             ++ exact Hnocoll_payload_head.
		             ++ exact Hnocoll_head_output.
		             ++ intros y Hy.
		                unfold sctx_add_params, ctx_add_params in Hy.
		                rewrite ctx_names_app in Hy.
		                apply in_app_or in Hy as [Hy_params | Hy_tail].
		                ** eapply alpha_rename_params_names_in_used.
		                   --- exact Hrename_head_params.
		                   --- exact Hy_params.
		                ** eapply alpha_rename_params_used_extends.
		                   --- exact Hrename_head_params.
		                   --- apply in_or_app. right. apply in_or_app. right.
		                       apply Hused_head_pre. apply Hctx_used1.
		                       exact Hy_tail.
		             ++ intros y Hy.
		                destruct (alpha_rename_params_range_ctx_or_tail
		                  _ _ _ _ _ _ Hrename_head_params _ Hy)
		                  as [Hy_params | Hy_range].
		                ** eapply alpha_rename_params_names_in_used.
		                   --- exact Hrename_head_params.
		                   --- exact Hy_params.
		                ** eapply alpha_rename_params_used_extends.
		                   --- exact Hrename_head_params.
		                   --- apply in_or_app. right. apply in_or_app. right.
		                       apply Hused_head_pre. apply Hrange_used1.
		                       exact Hy_range.
		             ++ intros y Hfree Hrange.
		                destruct (alpha_rename_params_range_ctx_or_tail
		                  _ _ _ _ _ _ Hrename_head_params _ Hrange)
		                  as [Hy_params | Hy_range].
		                ** eapply alpha_rename_params_names_fresh_used.
		                   --- exact Hrename_head_params.
		                   --- exact Hy_params.
		                   --- apply in_or_app. right. apply in_or_app. left.
		                       exact Hfree.
		                ** eapply lookup_expr_branch_disjoint_alpha.
		                   --- match goal with
		                       | H : lookup_expr_branch
		                               (Program.enum_variant_name v_head) l =
		                             Some e_head |- _ => exact H
		                       end.
		                   --- exact Hdisj_branches.
		                   --- exact Hfree.
		                   --- exact Hy_range.
		             ++ exact Hrename_head.
		             ++ pose (R_head_r :=
		                  root_env_remove_match_params ps_head_r
		                    R_head_payload_r).
		                set (Σ_head :=
		                  sctx_remove_params ps_head Σ_head_payload) in *.
		                pose (Σ_head_r :=
		                  sctx_remove_params ps_head_r
		                    Σ_head_payload_r).
		                assert (Hparams_head_ok_r :
		                  params_ok_sctx_b env ps_head_r
		                    Σ_head_payload_r = true).
		                { eapply alpha_rename_params_params_ok_sctx_b_forward_gen.
		                  - exact Hrename_head_params.
		                  - rewrite <- params_ctx_names_param_names.
		                    eapply params_names_nodup_b_sound.
		                    match goal
		                    with H : params_names_nodup_b ps_head = true |- _ =>
		                      exact H
		                    end.
		                  - intros y Hy.
		                    rewrite <- params_ctx_names_param_names in Hy.
		                    match goal with
			                    | H : match_payload_params binders_head lts args
			                            v_head = infer_ok ps_head |- _ =>
			                        rewrite (match_binder_params_names _ _ _ H) in Hy
		                    end.
		                    apply in_or_app. left. exact Hy.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hrange_used1. exact Hy.
		                  - exact Hctx_head_payload_r.
			                  - match goal with
			                    | H : params_ok_sctx_b env ps_head
			                            Σ_head_payload = true |- _ => exact H
			                    end. }
			                assert (Hctx_head_r :
			                  ctx_alpha rho Σ_head Σ_head_r).
		                { subst Σ_head_r.
		                  unfold Σ_head.
		                  eapply alpha_rename_params_ctx_alpha_remove.
		                  - exact Hrename_head_params.
		                  - exact Hctx_head_payload_r. }
		                assert (Hroots_head_named :
		                  root_set_sctx_roots_named roots_head
		                    (sctx_add_params ps_head Σ1)).
		                { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                    as [Hroots_env _].
		                  match goal with
		                  | H : typed_env_roots_shadow_safe env Ω n R_payload
		                        (sctx_add_params ps_head Σ1) e_head T_head
		                        Σ_head_payload R_head_payload roots_head |- _ =>
		                      destruct (Hroots_env R_payload
		                        (sctx_add_params ps_head Σ1) e_head T_head
		                        Σ_head_payload R_head_payload roots_head H
		                        Hns_payload_head) as [_ Hroots_head0]
		                  end.
		                  - exact Hroots_payload_head.
		                  - eapply root_set_sctx_roots_named_same_bindings.
		                    + apply sctx_same_bindings_sym.
		                      eapply typed_env_structural_same_bindings.
		                      eapply typed_env_roots_structural.
		                      eapply typed_env_roots_shadow_safe_roots.
		                      match goal with
		                      | H : typed_env_roots_shadow_safe env Ω n R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head |- _ =>
		                          exact H
		                      end.
		                    + exact Hroots_head0. }
		                assert (Hroots_head_r_outer :
		                  root_set_equiv roots_headr
		                    (root_set_rename rho roots_head)).
		                { eapply root_set_equiv_trans.
		                  - exact Hroots_head.
		                  - eapply alpha_rename_params_root_set_rename_excluded.
		                    + exact Hrename_head_params.
		                    + match goal with
		                      | H : roots_exclude_params ps_head roots_head |- _ =>
		                          exact H
		                      end. }
		                assert (Hns_R_head_payload :
		                  root_env_no_shadow R_head_payload).
		                { eapply typed_env_roots_no_shadow.
		                  - eapply typed_env_roots_shadow_safe_roots.
		                    match goal with
		                    | H : typed_env_roots_shadow_safe env Ω n R_payload
		                          (sctx_add_params ps_head Σ1) e_head T_head
		                          Σ_head_payload R_head_payload roots_head |- _ =>
		                        exact H
		                    end.
		                  - exact Hns_payload_head. }
		                set (R_out :=
		                  root_env_remove_match_params ps_head
		                    R_head_payload) in *.
		                assert (Hkeys_R_head :
		                  root_env_sctx_keys_named R_out
		                    (sctx_add_params ps_head Σ1)).
		                { eapply root_env_sctx_keys_named_add_params_env.
		                  eapply root_env_sctx_keys_named_same_bindings.
		                  - apply sctx_same_bindings_sym.
		                    eapply sctx_same_bindings_remove_added_params.
		                    apply sctx_same_bindings_refl.
			                  - unfold R_out.
			                    eapply root_env_sctx_keys_named_remove_match_params.
		                    + exact Hns_R_head_payload.
		                    + match goal with
		                      | H : typed_env_roots_shadow_safe env Ω n R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head |- _ =>
		                          destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                            as [Hkeys_env _];
		                          eapply root_env_sctx_keys_named_same_bindings;
		                          [ apply sctx_same_bindings_sym;
		                            eapply typed_env_structural_same_bindings;
		                            eapply typed_env_roots_structural;
		                            eapply typed_env_roots_shadow_safe_roots; exact H
		                          | eapply Hkeys_env; eassumption ]
		                      end. }
		                assert (Hroots_R_head :
		                  root_env_sctx_roots_named R_out
		                    (sctx_add_params ps_head Σ1)).
		                { eapply root_env_sctx_roots_named_add_params_env.
		                  eapply root_env_sctx_roots_named_same_bindings.
		                  - apply sctx_same_bindings_sym.
		                    eapply sctx_same_bindings_remove_added_params.
		                    apply sctx_same_bindings_refl.
			                  - unfold R_out.
			                    eapply root_env_sctx_roots_named_remove_match_params.
		                    + exact Hns_R_head_payload.
		                    + match goal with
		                      | H : root_env_excludes_params ps_head R_out |- _ =>
		                          exact H
		                      end.
		                    + match goal with
		                      | H : typed_env_roots_shadow_safe env Ω n R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head |- _ =>
		                          destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Ω n)
		                            as [Hroots_env _];
		                          destruct (Hroots_env R_payload
		                            (sctx_add_params ps_head Σ1) e_head T_head
		                            Σ_head_payload R_head_payload roots_head H
		                            Hns_payload_head) as [Hroots_env_head _];
		                          [ exact Hroots_payload_head
		                          | eapply root_env_sctx_roots_named_same_bindings;
		                            [ apply sctx_same_bindings_sym;
		                              eapply typed_env_structural_same_bindings;
		                              eapply typed_env_roots_structural;
		                              eapply typed_env_roots_shadow_safe_roots; exact H
		                            | exact Hroots_env_head ] ]
		                      end. }
		                assert (Hroot_none_R_head :
		                  root_env_lookup_params_none_b ps_head R_out = true).
		                { unfold R_out.
		                  apply root_env_lookup_params_none_b_remove_match_params.
		                  exact Hns_R_head_payload. }
		                assert (Hnocoll_params_R_head_payload :
		                  forall x, In x (ctx_names (params_ctx ps_head)) ->
		                    rename_no_collision_for rho_head x
		                      (root_env_names R_head_payload)).
		                { intros x Hin.
		                  eapply alpha_rename_params_rename_no_collision_for_params.
		                  - exact Hrename_head_params.
		                  - exact Hctx1_r.
		                  - exact Hns_R_head_payload.
		                  - match goal with
		                    | H : typed_env_roots_shadow_safe env Ω n R_payload
		                          (sctx_add_params ps_head Σ1) e_head T_head
		                          Σ_head_payload R_head_payload roots_head |- _ =>
		                        destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                          as [Hkeys_env _];
		                        eapply root_env_sctx_keys_named_same_bindings;
		                        [ apply sctx_same_bindings_sym;
		                          eapply typed_env_structural_same_bindings;
		                          eapply typed_env_roots_structural;
		                          eapply typed_env_roots_shadow_safe_roots; exact H
		                        | eapply Hkeys_env; eassumption ]
		                    end.
		                  - match goal
		                    with H : params_names_nodup_b ps_head = true |- _ =>
		                      exact H
		                    end.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hctx_used1. exact Hy.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hrange_used1. exact Hy.
		                  - exact Hnocoll_head_output.
		                  - exact Hin. }
		                assert (HRhead_r_branch :
		                  root_env_equiv R_head_r
		                    (root_env_rename rho_head R_out)).
		                { unfold R_head_r. unfold R_out.
		                  eapply alpha_rename_params_root_env_remove_match_params_full_rename_equiv.
		                  - exact Hrename_head_params.
		                  - match goal
		                    with H : params_names_nodup_b ps_head = true |- _ =>
		                      exact H
		                    end.
		                  - exact Hns_R_head_payload.
		                  - exact HnsR_head_payload_r.
		                  - exact HRhead_payload_r.
		                  - exact Hnocoll_head_output.
		                  - exact Hnocoll_params_R_head_payload.
		                  - intros x Hin. reflexivity. }
		                assert (Henv_head_excl_r :
		                  root_env_excludes_params ps_head_r R_head_r).
		                { eapply alpha_rename_params_root_env_excludes_params_rename.
		                  - exact Hrename_head_params.
		                  - exact Hctx1_r.
		                  - match goal with
		                    | H : root_env_no_shadow R_out |- _ => exact H
		                    end.
		                  - exact Hkeys_R_head.
		                  - exact Hroots_R_head.
		                  - exact Hroot_none_R_head.
		                  - match goal with
		                    | H : root_env_excludes_params ps_head R_out |- _ =>
		                        exact H
		                    end.
		                  - exact HRhead_r_branch.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hctx_used1. exact Hy.
		                  - intros y Hy. apply in_or_app. right.
		                    apply in_or_app. right.
		                    apply Hused_head_pre. apply Hrange_used1. exact Hy. }
		                assert (HnsR_head_r :
		                  root_env_no_shadow R_head_r).
		                { unfold R_head_r.
		                  apply root_env_remove_match_params_no_shadow.
		                  exact HnsR_head_payload_r. }
		                assert (HRhead_r_outer :
		                  root_env_equiv R_head_r
		                    (root_env_rename rho R_out)).
		                { eapply root_env_equiv_trans.
		                  - exact HRhead_r_branch.
		                  - eapply alpha_rename_params_root_env_rename_excluded.
		                    + exact Hrename_head_params.
		                    + exact HnsRout.
		                    + exact Hroot_none_R_head.
		                    + match goal with
		                      | H : root_env_excludes_params ps_head R_out |- _ =>
		                          exact H
		                      end. }
		                destruct (alpha_rename_typed_match_tail_roots_shadow_safe_forward
		                  env Ω n rho lts args R1 roots_scrut roots_scrutr
		                  Rr1 Σ1 Σr1 l branchesr used_scrut
		                  used_branches v_tail (ty_core T_head) R_out
		                  R_head_r Σ_tail Ts_tail roots_tail)
		                  as [Σ_tailr [roots_tailr [Htail_r [Hctx_tail_r Hroots_tail]]]].
				                ** intros rho0 R0 R0r Σa Σb used0 variant binders e0 er0 used1 T0
			                     Σa' R0' roots0 Hin Htyped0 Halpha HnsR0 HnsR0r
			                     HR0r Hkeys0 Hroots0 Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
			                   eapply (IH env Ω n rho0 R0 R0r Σa Σb e0 er0 used0
			                     used1 T0 Σa' R0' roots0).
		                   --- pose proof (expr_size_match_branch_lt e l variant binders e0 Hin).
		                       simpl in *. lia.
		                   --- exact Htyped0.
		                   --- exact Halpha.
		                   --- exact HnsR0.
		                   --- exact HnsR0r.
		                   --- exact HR0r.
		                   --- exact Hkeys0.
		                   --- exact Hroots0.
		                   --- exact Hnocoll0.
		                   --- exact Hnocoll0'.
		                   --- exact Hcu.
		                   --- exact Hru.
		                   --- exact Hd.
		                   --- exact Hr.
			                ** match goal with
			                   | H : typed_match_tail_roots_shadow_safe env Ω n
			                         lts args R1 roots_scrut Σ1 l v_tail
			                         (ty_core T_head) R_out Σ_tail Ts_tail
			                         roots_tail |- _ => exact H
			                   end.
		                ** exact Hctx1_r.
		                ** exact HnsR1.
		                ** exact HnsRout.
		                ** exact HnsRr1.
		                ** exact HRr1.
		                ** match goal with
		                   | H : typed_env_roots_shadow_safe env Ω n R Σ e T_scrut
		                         Σ1 R1 roots_scrut |- _ =>
		                       destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Ω n)
		                         as [Hkeys_env _];
		                       eapply Hkeys_env; eassumption
		                   end.
			                ** exact Hroots_R1.
			                ** exact Hroots_scrut_named.
		                ** exact HnocollR1.
		                ** exact HnocollR'.
			                ** exact Hctx_used1.
			                ** exact Hrange_used1.
			                ** exact Hroots_scrut.
			                ** exact Hdisj_branches.
		                ** exact Hbranches.
			                ** exact HRhead_r_outer.
			                ** destruct (ctx_alpha_merge_many_forward rho
			                     Σ_head Σ_head_r Σ_tail Σ_tailr Γ_out)
			                     as [Γ_outr [Hmerge_r Hctx_merge_r]].
		                   --- exact Hctx_head_r.
		                   --- exact Hctx_tail_r.
		                   --- match goal with
		                       | H : ctx_merge_many (ctx_of_sctx Σ_head)
		                             (map ctx_of_sctx Σ_tail) = Some Γ_out |- _ =>
		                           exact H
		                       end.
				                   --- exists (sctx_of_ctx Γ_outr), R_head_r,
			                         (root_sets_union (roots_headr :: roots_tailr)).
				                       split; [| split; [| split; [| split]]].
				                       { eapply TERS_Match.
				                         - exact Hscrut_r.
				                         - match goal with
				                           | H : ty_core T_scrut = TEnum enum_name lts args |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : Program.lookup_enum enum_name env = Some edef |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : Datatypes.length lts = Program.enum_lifetimes edef |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : Datatypes.length args = Program.enum_type_params edef |- _ =>
				                               exact H
				                           end.
				                         - match goal with
				                           | H : check_struct_bounds env (Program.enum_bounds edef) args =
				                                 None |- _ => exact H
				                           end.
				                         - eapply alpha_rename_match_branches_first_unknown_variant_branch; eauto.
					                         - match goal with
					                           | H : Program.enum_variants edef = v_head :: v_tail |- _ =>
					                               exact H
					                           end.
					                         - exact Hbinders_head_r.
						                         - unfold match_payload_params.
						                           exact Hparams_head_r.
					                         - exact Hparams_head_nodup_r.
					                         - exact Hctx_head_none_r.
					                         - exact Hroot_head_none_r.
					                         - exact Hlookup_head_r.
					                         - reflexivity.
					                         - exact Hhead_r.
					                         - exact Hparams_head_ok_r.
					                         - eapply alpha_rename_params_roots_exclude_params_rename.
					                           + exact Hrename_head_params.
					                           + exact Hctx1_r.
					                           + exact Hroots_head_named.
					                           + match goal with
					                             | H : roots_exclude_params ps_head roots_head |- _ =>
					                                 exact H
					                             end.
					                           + exact Hroots_head.
					                           + intros y Hy. apply in_or_app. right.
					                             apply in_or_app. right.
					                             apply Hused_head_pre. apply Hctx_used1.
					                             exact Hy.
					                           + intros y Hy. apply in_or_app. right.
					                             apply in_or_app. right.
					                             apply Hused_head_pre. apply Hrange_used1.
					                             exact Hy.
					                         - reflexivity.
					                         - exact Henv_head_excl_r.
					                         - reflexivity.
					                         - exact Htail_r.
					                         - exact Hmerge_r. }
				                       { unfold sctx_of_ctx. exact Hctx_merge_r. }
				                       { exact HnsR_head_r. }
				                       { exact HRhead_r_outer. }
				                       { eapply root_sets_union_rename_equiv.
				                         simpl. constructor; assumption. }
		      + eapply (alpha_rename_typed_env_roots_replace_shadow_safe_support_forward
		          env Ω n rho R Rr Σ Σr p e er used used' T Σ' R' roots).
	        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_assign_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr p e er used used' T Σ' R' roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply alpha_rename_typed_env_roots_borrow_shadow_safe_support_forward;
          eauto.
      + inversion Htyped; subst; simpl in Hrename; injection Hrename as <- <-.
        * match goal with
          | Hlookup : root_env_lookup ?x0 ?R0 = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_ren :
                root_env_lookup (lookup_rename x0 rho)
                  (root_env_rename rho R0) =
                Some (root_set_rename rho roots));
              [ apply root_env_lookup_rename;
                [ apply HnocollR;
                  eapply root_env_lookup_some_in_names; exact Hlookup
                | exact Hlookup ]
              | destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R0)
                  (lookup_rename x0 rho) (root_set_rename rho roots)
                  HR Hlookup_ren) as [rootsr [Hlookup_r Hroots_r]] ]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowShared.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ eapply place_path_rename_place_some. eassumption.
             ++ exact Hlookup_r.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
        * match goal with
          | Hpath : place_path p = None,
            Hlookup : place_root_lookup ?R0 p = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_root :
                root_env_lookup (root_provenance_place_name p) R0 = Some roots)
                by (rewrite <- (place_root_lookup_indirect R0 p Hpath); exact Hlookup);
              destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
                (root_provenance_place_name p) roots HR HnocollR Hlookup_root)
                as [rootsr [Hlookup_r Hroots_r]]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowShared_Indirect.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ match goal with Hpath : place_path p = None |- _ =>
                  apply place_path_rename_place_none; exact Hpath
                end.
             ++ rewrite (place_root_lookup_indirect Rr (rename_place rho p)).
                ** rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
                ** match goal with Hpath : place_path p = None |- _ =>
                     apply place_path_rename_place_none; exact Hpath
                   end.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
        * match goal with
          | Hlookup : root_env_lookup ?x0 ?R0 = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_ren :
                root_env_lookup (lookup_rename x0 rho)
                  (root_env_rename rho R0) =
                Some (root_set_rename rho roots));
              [ apply root_env_lookup_rename;
                [ apply HnocollR;
                  eapply root_env_lookup_some_in_names; exact Hlookup
                | exact Hlookup ]
              | destruct (root_env_equiv_lookup_r Rr (root_env_rename rho R0)
                  (lookup_rename x0 rho) (root_set_rename rho roots)
                  HR Hlookup_ren) as [rootsr [Hlookup_r Hroots_r]] ]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowUnique.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ eapply place_path_rename_place_some. eassumption.
             ++ eapply ctx_alpha_lookup_mut_forward.
                ** exact Hctx.
                ** match goal with
                   | Hpath : place_path p = Some (?x0, ?path0) |- _ =>
                       rewrite <- (place_path_root p x0 path0 Hpath); exact Hsafe_root
                   end.
                ** eassumption.
             ++ exact Hlookup_r.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
        * match goal with
          | Hpath : place_path p = None,
            Hlookup : place_root_lookup ?R0 p = Some roots,
            HR : root_env_equiv Rr (root_env_rename rho ?R0) |- _ =>
              assert (Hlookup_root :
                root_env_lookup (root_provenance_place_name p) R0 = Some roots)
                by (rewrite <- (place_root_lookup_indirect R0 p Hpath); exact Hlookup);
              destruct (root_env_equiv_rename_lookup_forward rho R0 Rr
                (root_provenance_place_name p) roots HR HnocollR Hlookup_root)
                as [rootsr [Hlookup_r Hroots_r]]
          end.
          assert (Hsafe_root : ~ In (place_root p) (rename_range rho)).
          { rewrite <- place_name_root. apply Hdisj. simpl. left. reflexivity. }
          exists Σr, Rr, rootsr.
          split.
          -- eapply TERS_DerefBorrowUnique_Indirect.
             ++ eapply alpha_rename_typed_place_env_structural_forward; eauto.
             ++ assumption.
             ++ match goal with Hpath : place_path p = None |- _ =>
                  apply place_path_rename_place_none; exact Hpath
                end.
             ++ eapply alpha_rename_place_under_unique_ref_structural_forward; eauto.
             ++ rewrite (place_root_lookup_indirect Rr (rename_place rho p)).
                ** rewrite root_provenance_place_name_rename_place. exact Hlookup_r.
                ** match goal with Hpath : place_path p = None |- _ =>
                     apply place_path_rename_place_none; exact Hpath
                   end.
          -- split; [exact Hctx | split; [exact HnsRr | split; [exact HRr | exact Hroots_r]]].
      + eapply (alpha_rename_typed_env_roots_drop_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots).
        * intros R0 R0r Σa Σb used0 er0 used1 T0 Σa' R0' roots0
            Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0 Hnocoll0
            Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
      + eapply (alpha_rename_typed_env_roots_if_shadow_safe_support_forward
          env Ω n rho R Rr Σ Σr e1 e2 e3 er used used' T Σ' R'
          roots).
        * intros R0 R0r Σa Σb used0 e0 er0 used1 T0 Σa' R0' roots0
            Hlt0 Htyped0 Halpha HnsR0 HnsR0r HR0r Hkeys0 Hroots0
            Hnocoll0 Hnocoll0' Hcu Hru Hd Hr.
          eapply (IH env Ω n rho R0 R0r Σa Σb e0 er0 used0 used1
            T0 Σa' R0' roots0).
          { simpl in *. lia. }
          all: eassumption.
        * exact Htyped.
        * exact Hctx.
        * exact HnsR.
        * exact HnsRr.
        * exact HRr.
        * exact Hkeys.
        * exact Hroots.
        * exact HnocollR.
        * exact HnocollR'.
        * exact Hctx_used.
        * exact Hrange_used.
        * exact Hdisj.
        * exact Hrename.
  }
  intros env Ω n rho R Rr Σ Σr e er used used' T Σ' R' roots
    Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
    Hctx_used Hrange_used Hdisj Hrename.
  eapply (Hsize (S (expr_size e))); eauto.
Qed.

Lemma alpha_rename_fn_def_typed_structural_forward :
  forall env used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params f))) ->
    typed_fn_env_structural env f ->
    typed_fn_env_structural env fr.
Proof.
  intros env used f fr used' Hrename Hnodup Htyped.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  injection Hrename as <- <-.
  unfold typed_fn_env_structural in *. simpl in *.
  destruct Htyped as [T_body [Γ_out [Htyped_body [Hcompat Hparams]]]].
  unfold fn_body_ctx, fn_body_params in Htyped_body.
  simpl in Htyped_body.
  destruct (alpha_rename_typed_env_structural_forward
    (global_env_with_local_bounds env fn_bounds) outs lifetimes ρ
    (sctx_of_ctx (params_ctx (ps ++ captures)))
    (sctx_of_ctx (params_ctx (psr ++ captures)))
    body bodyr used1 used2 T_body (sctx_of_ctx Γ_out))
    as [Σr_out [Htyped_body_r Hctx_out_r]].
  - eapply alpha_rename_params_ctx_alpha_stable_tail. exact Hps.
  - intros x Hin.
    change (ctx_names (sctx_of_ctx (params_ctx (psr ++ captures))))
      with (ctx_names (params_ctx (psr ++ captures))) in Hin.
    rewrite params_ctx_app in Hin.
    rewrite ctx_names_app in Hin.
    rewrite !params_ctx_names_param_names in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_captures].
    + eapply alpha_rename_params_names_in_used.
      * exact Hps.
      * rewrite params_ctx_names_param_names. exact Hin_params.
    + eapply alpha_rename_params_used_extends.
      * exact Hps.
      * apply in_or_app. right.
        apply in_or_app. left. exact Hin_captures.
  - intros x Hin.
    eapply alpha_rename_params_range_in_used_nil.
    + exact Hps.
    + exact Hin.
  - intros x Hfree Hrange.
    eapply alpha_rename_params_range_fresh_used_nil.
    + exact Hps.
    + exact Hrange.
    + apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. left. exact Hfree.
  - exact Hbody.
  - exact Htyped_body.
  - exists T_body, Σr_out. repeat split.
    + exact Htyped_body_r.
    + exact Hcompat.
    + eapply alpha_rename_params_params_ok_env_b_forward.
      * exact Hps.
      * exact Hnodup.
      * intros x Hin.
        apply in_or_app. left. exact Hin.
      * exact Hctx_out_r.
      * exact Hparams.
Qed.
