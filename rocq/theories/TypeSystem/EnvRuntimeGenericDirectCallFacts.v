From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeNarrowSummaryFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition fn_subst_type_params (type_args : list Ty) (f : fn_def) : fn_def :=
  MkFnDef (fn_name f) (fn_lifetimes f) (fn_outlives f)
    (apply_type_params type_args (fn_captures f))
    (apply_type_params type_args (fn_params f))
    (subst_type_params_ty type_args (fn_ret f))
    (subst_type_params_expr type_args (fn_body f))
    (fn_type_params f) (subst_type_params_trait_bounds type_args (fn_bounds f)).

Lemma apply_type_params_app :
  forall type_args ps1 ps2,
    apply_type_params type_args (ps1 ++ ps2) =
    apply_type_params type_args ps1 ++ apply_type_params type_args ps2.
Proof.
  intros type_args ps1 ps2.
  induction ps1 as [| p ps1 IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma fn_body_params_fn_subst_type_params :
  forall type_args f,
    fn_body_params (fn_subst_type_params type_args f) =
    apply_type_params type_args (fn_body_params f).
Proof.
  intros type_args f.
  unfold fn_subst_type_params, fn_body_params. simpl.
  rewrite apply_type_params_app. reflexivity.
Qed.

Lemma fn_body_ctx_fn_subst_type_params :
  forall type_args f,
    fn_body_ctx (fn_subst_type_params type_args f) =
    subst_type_params_ctx type_args (fn_body_ctx f).
Proof.
  intros type_args f.
  unfold fn_body_ctx.
  rewrite fn_body_params_fn_subst_type_params.
  apply params_ctx_apply_type_params.
Qed.

Lemma initial_root_env_for_fn_fn_subst_type_params :
  forall type_args f,
    initial_root_env_for_fn (fn_subst_type_params type_args f) =
    initial_root_env_for_fn f.
Proof.
  intros type_args f.
  unfold initial_root_env_for_fn, fn_subst_type_params. simpl.
  apply initial_root_env_for_params_apply_type_params.
Qed.

Definition callee_body_root_shadow_store_safe_narrow_summary_instantiated
    (env : global_env) (fdef : fn_def) (type_args : list Ty) : Prop :=
  exists T_body Gamma_out R_body roots_body ret_roots,
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
      R_body.

Lemma callee_body_root_shadow_provenance_summary_fn_subst_type_params_of_instantiated_narrow :
  forall env fdef type_args,
    callee_body_root_shadow_provenance_summary env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args ->
    callee_body_root_shadow_provenance_summary env
      (fn_subst_type_params type_args fdef).
Proof.
  intros env fdef type_args Hprov Hnarrow.
  unfold callee_body_root_shadow_provenance_summary in *.
  destruct Hprov as [Hnodup Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as (T_raw & Gamma_raw & R_raw & roots_raw &
    Hprov_body & Htyped_raw & Hcompat_raw & Hexcl_raw & Henv_raw).
  unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated in Hnarrow.
  destruct Hnarrow as (T_body & Gamma_out & R_body & roots_body & ret_roots &
    Hnodup_subst & Hsummary_body & Hcompat_body & Hexcl_roots & Hexcl_env).
  split.
  - unfold fn_subst_type_params. simpl. exact Hnodup_subst.
  - unfold callee_body_root_shadow_provenance_ready_at.
    exists T_body, Gamma_out, R_body, roots_body.
    repeat split; try assumption.
    + simpl. apply provenance_ready_expr_subst_type_params_expr.
      exact Hprov_body.
    + rewrite initial_root_env_for_fn_fn_subst_type_params.
      rewrite fn_body_ctx_fn_subst_type_params.
      simpl.
      eapply expr_root_shadow_store_safe_narrow_summary_typed.
      exact Hsummary_body.
Qed.


Lemma param_names_apply_type_params :
  forall type_args ps,
    param_names (apply_type_params type_args ps) = param_names ps.
Proof.
  intros type_args ps.
  induction ps as [| p ps IH]; simpl; auto.
  destruct p as [m x T]. simpl. rewrite IH. reflexivity.
Qed.

Lemma alpha_rename_params_apply_type_params :
  forall type_args rho used ps psr rhor used',
    alpha_rename_params rho used ps = (psr, rhor, used') ->
    alpha_rename_params rho used (apply_type_params type_args ps) =
      (apply_type_params type_args psr, rhor, used').
Proof.
  intros type_args rho used ps.
  revert rho used.
  induction ps as [| p ps IH]; intros rho used psr rhor used' Hrename;
    simpl in Hrename |- *.
  - injection Hrename as <- <- <-. reflexivity.
  - destruct p as [m x T]. simpl in Hrename |- *.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[psr_tail rhor_tail] used_tail] eqn:Htail.
    injection Hrename as <- <- <-.
    simpl. rewrite (IH _ _ _ _ _ Htail). reflexivity.
Qed.

Lemma alpha_rename_fn_def_subst_type_params :
  forall type_args used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    alpha_rename_fn_def used (fn_subst_type_params type_args f) =
      (fn_subst_type_params type_args fr, used').
Proof.
  intros type_args used f fr used' Hrename.
  unfold alpha_rename_fn_def in Hrename |- *.
  unfold fn_subst_type_params.
  simpl in Hrename |- *.
  repeat rewrite param_names_apply_type_params.
  rewrite expr_names_subst_type_params_expr.
  destruct (alpha_rename_params []
    (param_names (fn_params f) ++ param_names (fn_captures f) ++
      expr_names (fn_body f) ++ used) (fn_params f))
    as [[paramsr rho] used1] eqn:Hparams.
  change (map (apply_type_param type_args) (fn_params f)) with
    (apply_type_params type_args (fn_params f)).
  rewrite (alpha_rename_params_apply_type_params type_args []
    (param_names (fn_params f) ++ param_names (fn_captures f) ++
      expr_names (fn_body f) ++ used)
    (fn_params f) paramsr rho used1 Hparams).
  destruct (alpha_rename_expr rho used1 (fn_body f))
    as [bodyr used2] eqn:Hbody.
  change (free_vars_expr (fn_body f)) with (expr_names (fn_body f)) in Hrename.
  rewrite Hparams in Hrename. rewrite Hbody in Hrename.
  rewrite (alpha_rename_expr_subst_type_params_expr type_args rho used1
    (fn_body f) bodyr used2 Hbody).
  inversion Hrename; subst; clear Hrename.
  reflexivity.
Qed.

Lemma root_env_tail_fresh_names_subst_type_params_expr :
  forall type_args R_tail e,
    root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
    root_env_tail_fresh_names R_tail
      (expr_local_store_names (subst_type_params_expr type_args e)).
Proof.
  intros type_args R_tail e Hfresh.
  rewrite expr_local_store_names_subst_type_params_expr.
  exact Hfresh.
Qed.

Lemma root_env_tail_fresh_names_subst_type_params_expr_inv :
  forall type_args R_tail e,
    root_env_tail_fresh_names R_tail
      (expr_local_store_names (subst_type_params_expr type_args e)) ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e).
Proof.
  intros type_args R_tail e Hfresh.
  rewrite <- (expr_local_store_names_subst_type_params_expr type_args e).
  exact Hfresh.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_tail_frame :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall R_tail,
      root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (R ++ R_tail) Σ e T Σ' (R' ++ R_tail)
        roots ret_roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros R_tail Hfresh; simpl in Hfresh.
  - eapply ERSSN_FunctionValueCall.
    + exact H.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H0.
      * unfold root_env_tail_fresh_names. intros y Hy. contradiction.
    + exact H1.
    + eapply typed_env_roots_shadow_safe_tail_frame; eassumption.
  - eapply ERSSN_TypeGenericFunctionValueCall.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H3.
      * unfold root_env_tail_fresh_names. intros y Hy. contradiction.
    + exact H4.
    + exact H5.
    + eapply typed_env_roots_shadow_safe_tail_frame; eassumption.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ Hfresh) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ Hfresh) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply ERSSN_Let.
    + apply IHHsummary1. exact Hfresh1.
    + exact H.
    + exact H0.
    + rewrite root_env_lookup_app_right by exact H1.
      exact Htail_lookup.
    + exact H2.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply IHHsummary2. exact Hfresh2.
    + exact H4.
    + exact H5.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ Hfresh) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ Hfresh) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply ERSSN_LetInfer.
    + apply IHHsummary1. exact Hfresh1.
    + exact H.
    + rewrite root_env_lookup_app_right by exact H0.
      exact Htail_lookup.
    + exact H1.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply IHHsummary2. exact Hfresh2.
    + exact H3.
    + exact H4.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - eapply ERSSN_BorrowDirect.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H.
      * exact Hfresh.
    + exact H0.
    + exact H1.
  - eapply ERSSN_BorrowUniqueResolvedWritableChain.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H.
      * unfold root_env_tail_fresh_names. intros y Hy. contradiction.
    + exact H0.
    + eapply place_resolved_write_writable_chain_app_left. exact H1.
    + eapply place_resolved_write_target_app_left.
      exact H2.
    + exact H3.
  - apply ERSSN_Unit.
    eapply typed_env_roots_shadow_safe_tail_frame.
    + exact H.
    + unfold root_env_tail_fresh_names. intros y Hy. contradiction.
  - eapply ERSSN_EmptyStructRootless.
    + exact H.
    + exact H0.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H1.
      * exact Hfresh.
    + exact H2.
  - eapply ERSSN_AssignLit.
    eapply typed_env_roots_shadow_safe_tail_frame.
    + exact H.
    + exact Hfresh.
  - eapply ERSSN_AssignGenericDirect.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + exact H6.
    + exact Hsummary.
    + exact H7.
    + exact H8.
    + exact H9.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H10.
      * exact Hfresh.
  - eapply ERSSN_VarNonFunction.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H.
      * unfold root_env_tail_fresh_names. intros y Hy. contradiction.
    + exact H0.
  - eapply ERSSN_DropPlaceDirect.
    + eapply typed_env_roots_shadow_safe_tail_frame.
      * exact H.
      * exact Hfresh.
    + exact H0.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_tail_frame_subst_type_params_expr :
  forall env Omega n R Σ type_args e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ (subst_type_params_expr type_args e) T Σ' R' roots
      ret_roots ->
    forall R_tail,
      root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (R ++ R_tail) Σ (subst_type_params_expr type_args e) T
        Σ' (R' ++ R_tail) roots ret_roots.
Proof.
  intros env Omega n R Σ type_args e T Σ' R' roots ret_roots Hsummary
    R_tail Hfresh.
  eapply expr_root_shadow_store_safe_narrow_summary_tail_frame.
  - exact Hsummary.
  - eapply root_env_tail_fresh_names_subst_type_params_expr.
    exact Hfresh.
Qed.


Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_forward :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    forall rho Rr Σr er used used',
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
      exists Σr' Rr' rootsr ret_rootsr,
        expr_root_shadow_store_safe_narrow_summary
          env Omega n Rr Σr er T Σr' Rr' rootsr ret_rootsr /\
        ctx_alpha rho Σ' Σr' /\
        root_env_no_shadow Rr' /\
        root_env_equiv Rr' (root_env_rename rho R') /\
        root_set_equiv rootsr (root_set_rename rho roots) /\
        root_set_equiv ret_rootsr (root_set_rename rho ret_roots).
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary as
    [ Omega0 n0 R Σ x args T_callee Σ_callee R_callee roots_callee T Σ' R' roots
      Hargs Hcallee Hshape Hcall
    | Omega0 n0 R Σ x type_args args inst_fuel T_callee Σ_callee R_callee
      roots_callee T Σ' R' roots Hargs Hclosed Hno_top Hinstantiated Hcallee Hshape Hcall
    | Omega0 n0 R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2 T2 roots1 roots2
      ret_roots1 ret_roots Hsummary1 IH1 Hcompat Hnonfun Hlookup
      Hexcl_roots1 Hexcl_env1 Hsummary2 IH2 Hcheck Hexcl_roots2
      Hexcl_env2
    | Omega0 n0 R R1 R2 Σ Σ1 Sigma2 m x T1 e1 e2 T2 roots1 roots2
      ret_roots1 ret_roots Hsummary1 IH1 Hnonfun Hlookup
      Hexcl_roots1 Hexcl_env1 Hsummary2 IH2 Hcheck Hexcl_roots2
      Hexcl_env2
    | Omega0 n0 R Σ rk p T Σ' R' roots x path Htyped Hpath Hsingle
    | Omega0 n0 R Σ p T Σ' R' roots x Htyped Hpath Hdirect Htarget Hsingle
    | Omega0 n0 R Σ T Σ' R' roots Htyped
    | Omega0 n0 R Σ name lts args T Σ' R' roots sdef Hlookup_struct Hbounds_struct Htyped Hfree
    | Omega0 n0 R Σ p lit T Σ' R' roots Htyped
    | Omega0 n0 R Σ x fname type_args T Σ' R' roots fcallee T_body Sigma_body
      R_body roots_body ret_roots_body sname lts tys Hin_callee Hname_callee
      Harity Hbounds Hparams Hctx_empty Hbody_shape Hnodup Hsummary_body
      IHbody Hcompat_body Hroots_excl Henv_excl Htyped
    | Omega0 n0 R Σ x T Σ' R' roots Htyped Hnonfun
    | Omega0 n0 R Σ p T Σ' R' roots x path Htyped Hpath ];
    intros rho Rr0 Σr0 er used used' Hctx HnsR HnsRr HRr Hkeys
      Hroots HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename.
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 (ECallExpr (EVar x) args) er used
      used' T Σ' R' roots Hcall Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σcall_r & Rcall_r & roots_r & Hcall_r & Hctx_r &
        HnsR_r & HR_r & Hroots_r).
    assert (Hnocoll_callee :
      rename_no_collision_on rho (root_env_names R_callee)).
    { eapply typed_env_roots_shadow_safe_evar_rename_no_collision_on_output_base;
        eassumption. }
    destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 (EVar x)
      (EVar (lookup_rename x rho)) used used T_callee Σ_callee
      R_callee roots_callee Hcallee Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR Hnocoll_callee Hctx_used Hrange_used
      (disjoint_names_evar_of_call_expr x args (rename_range rho) Hdisj)
      eq_refl)
      as (Σcallee_r & Rcallee_r & roots_callee_r & Hcallee_r & _).
    exists Σcall_r, Rcall_r, roots_r, roots_r.
    split.
    + eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_function_value_call_intro;
        eassumption.
    + split; [exact Hctx_r |].
      split; [exact HnsR_r |].
      split; [exact HR_r |].
      split; [exact Hroots_r | exact Hroots_r].
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0
      (ECallExprGeneric (EVar x) type_args args) er used
      used' T Σ' R' roots H Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σcall_r & Rcall_r & roots_r & Hcall_r & Hctx_r &
        HnsR_r & HR_r & Hroots_r).
    assert (Hnocoll_callee :
      rename_no_collision_on rho (root_env_names R_callee)).
    { eapply typed_env_roots_shadow_safe_evar_rename_no_collision_on_output_base;
        eassumption. }
    destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 (EVar x)
      (EVar (lookup_rename x rho)) used used T_callee Σ_callee
      R_callee roots_callee Hcallee Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR Hnocoll_callee Hctx_used Hrange_used
      (disjoint_names_evar_of_call_expr_generic x type_args args
        (rename_range rho) Hdisj)
      eq_refl)
      as (Σcallee_r & Rcallee_r & roots_callee_r & Hcallee_r & _).
    exists Σcall_r, Rcall_r, roots_r, roots_r.
    split.
    + eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_type_generic_function_value_call_intro.
      * exact Hargs.
      * exact Hclosed.
      * exact Hno_top.
      * exact Hinstantiated.
      * exact Hrename.
      * exact Hcallee_r.
      * exact Hshape.
      * exact Hcall.
      * exact Hcall_r.
    + split; [exact Hctx_r |].
      split; [exact HnsR_r |].
      split; [exact HR_r |].
      split; [exact Hroots_r | exact Hroots_r].
  - simpl in Hrename.
    destruct (disjoint_names_cons_l x
      (free_vars_expr e1 ++ free_vars_expr e2) (rename_range rho) Hdisj)
      as [Hsafe_x Hdisj_tail].
    destruct (disjoint_names_app_l (free_vars_expr e1)
      (free_vars_expr e2) (rename_range rho) Hdisj_tail)
      as [Hdisj1 Hdisj2].
    destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
    set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
    assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1))
      by reflexivity.
    set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
    assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1)
      by reflexivity.
    destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
      as [e2r used3] eqn:He2.
    assert (Htyped1 :
      typed_env_roots_shadow_safe env Omega0 n0 R Σ e1 T1 Σ1 R1 roots1)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1).
    assert (Htyped2 :
      typed_env_roots_shadow_safe env Omega0 n0 (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary2).
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped1.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega0 n0)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [Hroots_env1 _]; eauto. }
    assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [_ Hroots_set1]; eauto. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply typed_env_roots_let_body_no_collision_from_removed.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hlookup.
      - exact HnocollR'. }
    destruct (IH1 rho Rr0 Σr0 e1r used used1 Hctx HnsR HnsRr HRr
      Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used Hdisj1 He1)
      as (Σ1r & R1r & roots1r & ret_roots1r & Hsummary1r &
        Hctx1r & HnsR1r & HR1r & Hroots1r & _).
    assert (Htyped1r :
      typed_env_roots_shadow_safe env Omega0 n0 Rr0 Σr0 e1r T1 Σ1r R1r
        roots1r)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1r).
    assert (Hctx_used1 : forall y, In y (ctx_names Σ1r) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σ1r).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σ1r)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_init_support
      rho R1 R1r roots1 roots1r Σ1 Σ1r xr Hctx1r HnsR1 HnsR1r
      HR1r Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
      as [Hlookup_xr [Hexcl_roots1r Hexcl_env1r]].
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T_hidden m Σ1) (sctx_add xr T_hidden m Σ1r)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hns_add :
      root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hns_add_r :
      root_env_no_shadow (root_env_add xr roots1r R1r))
      by (apply root_env_no_shadow_add; assumption).
    assert (HRadd :
      root_env_equiv (root_env_add xr roots1r R1r)
        (root_env_rename ((x, xr) :: rho)
          (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
    assert (Hroots_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    assert (Hnocoll_add :
      rename_no_collision_on ((x, xr) :: rho)
        (root_env_names (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_no_collision_on;
        eassumption. }
    assert (HnocollR2_cons :
      rename_no_collision_on ((x, xr) :: rho) (root_env_names R2)).
    { eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision_from_summary;
        eassumption. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T_hidden m Σ1r)) -> In y used2).
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
    destruct (IH2 ((x, xr) :: rho) (root_env_add xr roots1r R1r)
      (sctx_add xr T_hidden m Σ1r) e2r used2 used3 Hctx_body
      Hns_add Hns_add_r HRadd Hkeys_add Hroots_add Hnocoll_add
      HnocollR2_cons Hctx_used2 Hrange_used2
      (alpha_rename_let_body_disjoint_forward rho used1 x xr e2 Hxr Hdisj2)
      He2)
      as (Σ2r & R2r & roots2r & ret_roots2r & Hsummary2r &
        Hctx2r & HnsR2r & HR2r_cons & Hroots2r_cons & Hret2r_cons).
    assert (HnsR2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hns_add. }
    assert (HkeysR2 : root_env_sctx_keys_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega0 n0)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR2 : root_env_sctx_roots_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2)
        as [Hroots_env2 _]; eauto. }
    assert (Hroots2_named : root_set_sctx_roots_named roots2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2)
        as [_ Hroots_set2]; eauto. }
    assert (Hsame_body :
      sctx_same_bindings (sctx_add x T_hidden m Σ1) Sigma2).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
    assert (Hnocoll_x :
      rename_no_collision_for ((x, xr) :: rho) x (root_env_names R2)).
    { eapply root_env_sctx_keys_named_added_no_collision_for_head.
      - exact Hctx1r.
      - eapply root_env_sctx_keys_named_same_bindings.
        + apply sctx_same_bindings_sym. exact Hsame_body.
        + exact HkeysR2.
      - exact Hfresh_ctx. }
    assert (HRremove :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename rho (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_equiv;
        eassumption. }
    assert (Hroots2r :
      root_set_equiv roots2r (root_set_rename rho roots2)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hret_roots_excl : roots_exclude x ret_roots).
    { eapply expr_root_shadow_store_safe_narrow_summary_ret_roots_exclude;
        eassumption. }
    assert (Hret2r :
      root_set_equiv ret_roots2r (root_set_rename rho ret_roots)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hroots2r_excl : roots_exclude xr roots2r).
    { eapply roots_exclude_shadow_safe_rename_body.
      - exact Hctx1r.
      - eapply root_set_sctx_roots_named_strip_added_same_bindings.
        + exact Hexcl_roots2.
        + exact Hroots2_named.
        + exact Hsame_body.
      - exact Hfresh_ctx.
      - exact Hroots2r_cons.
      - exact Hexcl_roots2. }
    assert (Hremove_ext :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename ((x, xr) :: rho) (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
        eassumption. }
    assert (Henv2r_excl :
      root_env_excludes xr (root_env_remove xr R2r)).
    { eapply root_env_excludes_shadow_safe_rename_body.
      - exact Hctx1r.
      - apply root_env_no_shadow_remove. exact HnsR2.
      - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
          eassumption.
      - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
          eassumption.
      - exact Hfresh_ctx.
      - exact Hremove_ext.
      - exact Hexcl_env2. }
    change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
      in Hrename.
    change (xr :: x :: free_vars_expr e2 ++ used1) with used2
      in Hrename.
    rewrite He2 in Hrename.
    injection Hrename as <- <-.
    exists (sctx_remove xr Σ2r), (root_env_remove xr R2r), roots2r,
      ret_roots2r.
    split.
    + eapply ERSSN_Let.
      * exact Hsummary1r.
      * exact Hcompat.
      * exact Hnonfun.
      * exact Hlookup_xr.
      * exact Hexcl_roots1r.
      * exact Hexcl_env1r.
      * exact Hsummary2r.
      * assert (Hlookup_xr_rename :
          lookup_rename x ((x, xr) :: rho) = xr)
          by (simpl; rewrite ident_eqb_refl; reflexivity).
        rewrite <- Hlookup_xr_rename.
        eapply ctx_alpha_check_ok_forward.
        -- exact Hctx2r.
        -- eapply alpha_rename_let_bound_safe_forward; eassumption.
        -- exact Hcheck.
      * exact Hroots2r_excl.
      * exact Henv2r_excl.
    + split.
      * eapply ctx_alpha_remove_bound. exact Hctx2r.
      * split.
        -- apply root_env_no_shadow_remove. exact HnsR2r.
        -- split.
           ++ exact HRremove.
           ++ split; [exact Hroots2r | exact Hret2r].
  - simpl in Hrename.
    destruct (disjoint_names_cons_l x
      (free_vars_expr e1 ++ free_vars_expr e2) (rename_range rho) Hdisj)
      as [Hsafe_x Hdisj_tail].
    destruct (disjoint_names_app_l (free_vars_expr e1)
      (free_vars_expr e2) (rename_range rho) Hdisj_tail)
      as [Hdisj1 Hdisj2].
    destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
    set (xr := fresh_ident x (x :: free_vars_expr e2 ++ used1)).
    assert (Hxr : xr = fresh_ident x (x :: free_vars_expr e2 ++ used1))
      by reflexivity.
    set (used2 := xr :: x :: free_vars_expr e2 ++ used1).
    assert (Hused2 : used2 = xr :: x :: free_vars_expr e2 ++ used1)
      by reflexivity.
    destruct (alpha_rename_expr ((x, xr) :: rho) used2 e2)
      as [e2r used3] eqn:He2.
    assert (Htyped1 :
      typed_env_roots_shadow_safe env Omega0 n0 R Σ e1 T1 Σ1 R1 roots1)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1).
    assert (Htyped2 :
      typed_env_roots_shadow_safe env Omega0 n0 (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary2).
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped1.
      - exact HnsR. }
    assert (HkeysR1 : root_env_sctx_keys_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega0 n0)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR1 : root_env_sctx_roots_named R1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [Hroots_env1 _]; eauto. }
    assert (Hroots1_named : root_set_sctx_roots_named roots1 Σ1).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env R Σ e1 T1 Σ1 R1 roots1)
        as [_ Hroots_set1]; eauto. }
    assert (HnocollR1 : rename_no_collision_on rho (root_env_names R1)).
    { eapply typed_env_roots_let_body_no_collision_from_removed.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hlookup.
      - exact HnocollR'. }
    destruct (IH1 rho Rr0 Σr0 e1r used used1 Hctx HnsR HnsRr HRr
      Hkeys Hroots HnocollR HnocollR1 Hctx_used Hrange_used Hdisj1 He1)
      as (Σ1r & R1r & roots1r & ret_roots1r & Hsummary1r &
        Hctx1r & HnsR1r & HR1r & Hroots1r & _).
    assert (Htyped1r :
      typed_env_roots_shadow_safe env Omega0 n0 Rr0 Σr0 e1r T1 Σ1r R1r
        roots1r)
      by (eapply expr_root_shadow_store_safe_narrow_summary_typed;
          exact Hsummary1r).
    assert (Hctx_used1 : forall y, In y (ctx_names Σ1r) -> In y used1).
    { intros y Hy.
      eapply alpha_rename_expr_used_extends.
      - exact He1.
      - apply Hctx_used.
        rewrite <- (sctx_same_bindings_names_alpha Σr0 Σ1r).
        + exact Hy.
        + eapply typed_env_structural_same_bindings.
          eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots. exact Htyped1r. }
    assert (Hrange_used1 : forall y, In y (rename_range rho) -> In y used1).
    { intros y Hy. eapply alpha_rename_expr_used_extends; eauto. }
    assert (Hfresh_ctx : ~ In xr (ctx_names Σ1r)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hctx_used1. exact Hin. }
    assert (Hfresh_range : ~ In xr (rename_range rho)).
    { unfold xr. intro Hin.
      apply (fresh_ident_not_in x (x :: free_vars_expr e2 ++ used1)).
      right. apply in_or_app. right. apply Hrange_used1. exact Hin. }
    destruct (expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_init_support
      rho R1 R1r roots1 roots1r Σ1 Σ1r xr Hctx1r HnsR1 HnsR1r
      HR1r Hroots1r HkeysR1 HrootsR1 Hroots1_named Hfresh_ctx)
      as [Hlookup_xr [Hexcl_roots1r Hexcl_env1r]].
    assert (Hctx_body : ctx_alpha ((x, xr) :: rho)
      (sctx_add x T1 m Σ1) (sctx_add xr T1 m Σ1r)).
    { eapply ctx_alpha_add_fresh_forward; eauto. }
    assert (Hns_add :
      root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hns_add_r :
      root_env_no_shadow (root_env_add xr roots1r R1r))
      by (apply root_env_no_shadow_add; assumption).
    assert (HRadd :
      root_env_equiv (root_env_add xr roots1r R1r)
        (root_env_rename ((x, xr) :: rho)
          (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_equiv; eassumption. }
    assert (Hkeys_add :
      root_env_sctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_keys_named_add_binding. exact HkeysR1. }
    assert (Hroots_add :
      root_env_sctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_sctx_roots_named_add_binding; assumption. }
    assert (Hnocoll_add :
      rename_no_collision_on ((x, xr) :: rho)
        (root_env_names (root_env_add x roots1 R1))).
    { eapply root_env_add_shadow_safe_rename_no_collision_on;
        eassumption. }
    assert (HnocollR2_cons :
      rename_no_collision_on ((x, xr) :: rho) (root_env_names R2)).
    { eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision_from_summary;
        eassumption. }
    assert (Hctx_used2 : forall y,
      In y (ctx_names (sctx_add xr T1 m Σ1r)) -> In y used2).
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
    destruct (IH2 ((x, xr) :: rho) (root_env_add xr roots1r R1r)
      (sctx_add xr T1 m Σ1r) e2r used2 used3 Hctx_body
      Hns_add Hns_add_r HRadd Hkeys_add Hroots_add Hnocoll_add
      HnocollR2_cons Hctx_used2 Hrange_used2
      (alpha_rename_let_body_disjoint_forward rho used1 x xr e2 Hxr Hdisj2)
      He2)
      as (Σ2r & R2r & roots2r & ret_roots2r & Hsummary2r &
        Hctx2r & HnsR2r & HR2r_cons & Hroots2r_cons & Hret2r_cons).
    assert (HnsR2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots. exact Htyped2.
      - exact Hns_add. }
    assert (HkeysR2 : root_env_sctx_keys_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega0 n0)
        as [Hkeys_env _].
      eapply Hkeys_env; eassumption. }
    assert (HrootsR2 : root_env_sctx_roots_named R2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2)
        as [Hroots_env2 _]; eauto. }
    assert (Hroots2_named : root_set_sctx_roots_named roots2 Sigma2).
    { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env Omega0 n0)
        as [Hroots_env _].
      destruct (Hroots_env (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2)
        as [_ Hroots_set2]; eauto. }
    assert (Hsame_body :
      sctx_same_bindings (sctx_add x T1 m Σ1) Sigma2).
    { eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural.
      eapply typed_env_roots_shadow_safe_roots. exact Htyped2. }
    assert (Hnocoll_x :
      rename_no_collision_for ((x, xr) :: rho) x (root_env_names R2)).
    { eapply root_env_sctx_keys_named_added_no_collision_for_head.
      - exact Hctx1r.
      - eapply root_env_sctx_keys_named_same_bindings.
        + apply sctx_same_bindings_sym. exact Hsame_body.
        + exact HkeysR2.
      - exact Hfresh_ctx. }
    assert (HRremove :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename rho (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_equiv;
        eassumption. }
    assert (Hroots2r :
      root_set_equiv roots2r (root_set_rename rho roots2)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hret_roots_excl : roots_exclude x ret_roots).
    { eapply expr_root_shadow_store_safe_narrow_summary_ret_roots_exclude;
        eassumption. }
    assert (Hret2r :
      root_set_equiv ret_roots2r (root_set_rename rho ret_roots)).
    { eapply root_set_shadow_safe_rename_body_equiv; eassumption. }
    assert (Hroots2r_excl : roots_exclude xr roots2r).
    { eapply roots_exclude_shadow_safe_rename_body.
      - exact Hctx1r.
      - eapply root_set_sctx_roots_named_strip_added_same_bindings.
        + exact Hexcl_roots2.
        + exact Hroots2_named.
        + exact Hsame_body.
      - exact Hfresh_ctx.
      - exact Hroots2r_cons.
      - exact Hexcl_roots2. }
    assert (Hremove_ext :
      root_env_equiv (root_env_remove xr R2r)
        (root_env_rename ((x, xr) :: rho) (root_env_remove x R2))).
    { eapply root_env_remove_shadow_safe_rename_body_ext_equiv;
        eassumption. }
    assert (Henv2r_excl :
      root_env_excludes xr (root_env_remove xr R2r)).
    { eapply root_env_excludes_shadow_safe_rename_body.
      - exact Hctx1r.
      - apply root_env_no_shadow_remove. exact HnsR2.
      - eapply root_env_sctx_keys_named_remove_strip_added_same_bindings;
          eassumption.
      - eapply root_env_sctx_roots_named_remove_strip_added_same_bindings;
          eassumption.
      - exact Hfresh_ctx.
      - exact Hremove_ext.
      - exact Hexcl_env2. }
    change (fresh_ident x (x :: free_vars_expr e2 ++ used1)) with xr
      in Hrename.
    change (xr :: x :: free_vars_expr e2 ++ used1) with used2
      in Hrename.
    rewrite He2 in Hrename.
    injection Hrename as <- <-.
    exists (sctx_remove xr Σ2r), (root_env_remove xr R2r), roots2r,
      ret_roots2r.
    split.
    + eapply ERSSN_LetInfer.
      * exact Hsummary1r.
      * exact Hnonfun.
      * exact Hlookup_xr.
      * exact Hexcl_roots1r.
      * exact Hexcl_env1r.
      * exact Hsummary2r.
      * assert (Hlookup_xr_rename :
          lookup_rename x ((x, xr) :: rho) = xr)
          by (simpl; rewrite ident_eqb_refl; reflexivity).
        rewrite <- Hlookup_xr_rename.
        eapply ctx_alpha_check_ok_forward.
        -- exact Hctx2r.
        -- eapply alpha_rename_let_bound_safe_forward; eassumption.
        -- exact Hcheck.
      * exact Hroots2r_excl.
      * exact Henv2r_excl.
    + split.
      * eapply ctx_alpha_remove_bound. exact Hctx2r.
      * split.
        -- apply root_env_no_shadow_remove. exact HnsR2r.
        -- split.
           ++ exact HRremove.
           ++ split; [exact Hroots2r | exact Hret2r].
  - destruct (alpha_rename_typed_env_roots_borrow_shadow_safe_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 rk p er used used' T Σ' R' roots
      Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
      Hctx_used Hrange_used Hdisj Hrename)
      as [Σr' [Rr' [rootsr [Htypedr [Hctxr [Hnsr [HRr' Hrootsr]]]]]]].
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + eapply ERSSN_BorrowDirect.
      * exact Htypedr.
      * eapply RootProvenance.place_path_rename_place_some. exact Hpath.
      * rewrite (singleton_store_root_equiv rootsr
          (root_set_rename rho roots) Hrootsr).
        apply singleton_store_root_rename_some. exact Hsingle.
    + repeat split; try eassumption; try apply Hrootsr.

  - destruct (alpha_rename_typed_env_roots_borrow_shadow_safe_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 RUnique p er used used' T Σ' R' roots
      Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
      Hctx_used Hrange_used Hdisj Hrename)
      as [Σr' [Rr' [rootsr [Htypedr [Hctxr [Hnsr [HRr' Hrootsr]]]]]]].
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + eapply ERSSN_BorrowUniqueResolvedWritableChain.
      * exact Htypedr.
      * eapply RootProvenance.place_path_rename_place_none. exact Hpath.
      * eapply place_resolved_write_writable_chain_rename.
        -- apply root_env_equiv_sym. exact HRr.
        -- exact HnocollR.
        -- exact Hctx.
        -- rewrite <- place_name_root. simpl in Hdisj. apply Hdisj. simpl. left. reflexivity.
        -- exact Hdirect.
      * eapply place_resolved_write_target_equiv.
        -- apply root_env_equiv_sym. exact HRr.
        -- apply place_resolved_write_target_rename.
           ++ exact HnocollR.
           ++ exact Htarget.
      * rewrite (singleton_store_root_equiv rootsr
          (root_set_rename rho roots) Hrootsr).
        apply singleton_store_root_rename_some. exact Hsingle.
    + repeat split; try eassumption; try apply Hrootsr.

  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 EUnit er used used' T Σ' R' roots
      Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
      Hctx_used Hrange_used Hdisj Hrename)
      as (Σr' & Rr' & rootsr & Htypedr & Hctxr & Hnsr & HRr' & Hrootsr).
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + apply ERSSN_Unit. exact Htypedr.
    + repeat split; try eassumption; try apply Hrootsr.
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 (EStruct name lts args []) er used used'
      T Σ' R' roots Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σr' & Rr' & rootsr & Htypedr & Hctxr & Hnsr & HRr' & Hrootsr).
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, [].
    split.
    + eapply ERSSN_EmptyStructRootless; eassumption.
    + repeat split; try eassumption; try apply Hrootsr;
        apply root_set_equiv_refl.
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 (EAssign p (ELit lit)) er used used'
      T Σ' R' roots Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σr' & Rr' & rootsr & Htypedr & Hctxr & Hnsr & HRr' & Hrootsr).
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + eapply ERSSN_AssignLit. exact Htypedr.
    + repeat split; try eassumption; try apply Hrootsr.
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0
      (EAssign (PVar x) (ECallGeneric fname type_args [])) er used used'
      T Σ' R' roots Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σr' & Rr' & rootsr & Htypedr & Hctxr & Hnsr & HRr' & Hrootsr).
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + eapply ERSSN_AssignGenericDirect.
      * exact Hin_callee.
      * exact Hname_callee.
      * exact Harity.
      * exact Hbounds.
      * exact Hparams.
      * exact Hctx_empty.
      * exact Hbody_shape.
      * exact Hnodup.
      * exact Hsummary_body.
      * exact Hcompat_body.
      * exact Hroots_excl.
      * exact Henv_excl.
      * exact Htypedr.
    + repeat split; try eassumption; try apply Hrootsr.
  - destruct (alpha_rename_typed_env_roots_var_shadow_safe_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 x er used used' T Σ' R' roots
      Htyped Hctx HnsR HnsRr HRr Hkeys Hroots HnocollR HnocollR'
      Hctx_used Hrange_used Hdisj Hrename)
      as (Σr' & Rr' & rootsr & Htypedr & Hctxr & Hnsr & HRr' & Hrootsr).
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + eapply ERSSN_VarNonFunction; eassumption.
    + repeat split; try eassumption; try apply Hrootsr.
  - destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
      env Omega0 n0 rho R Rr0 Σ Σr0 (EDrop (EPlace p)) er used used'
      T Σ' R' roots Htyped Hctx HnsR HnsRr HRr Hkeys Hroots
      HnocollR HnocollR' Hctx_used Hrange_used Hdisj Hrename)
      as (Σr' & Rr' & rootsr & Htypedr & Hctxr & Hnsr & HRr' & Hrootsr).
    simpl in Hrename. injection Hrename as <- <-.
    exists Σr', Rr', rootsr, rootsr.
    split.
    + eapply ERSSN_DropPlaceDirect.
      * exact Htypedr.
      * eapply RootProvenance.place_path_rename_place_some. exact Hpath.
    + repeat split; try eassumption; try apply Hrootsr.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_instantiate_fresh :
  forall env Omega n rho R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0 ret_roots0,
        expr_root_shadow_store_safe_narrow_summary
          env Omega n R0 Σ e T Σ' R0' roots0 ret_roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Omega n rho R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros Hfresh R0 HnsR HnsR0 HR0.
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (ECallExpr (EVar x) args) T Σ' R' roots
      R0 H2 Hfresh HnsR HnsR0 HR0)
      as (Rcall0 & roots0 & Htyped_call0 & Hns_call0 & HR_call0 & Hroots0).
    destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EVar x) T_callee Σ_callee R_callee
      roots_callee R0 H0 (root_subst_images_exclude_names_nil rho) HnsR HnsR0 HR0)
      as (Rcallee0 & roots_callee0 & Htyped_callee0 & _ & _ & _).
    exists Rcall0, roots0, roots0. split.
    + eapply ERSSN_FunctionValueCall.
      * exact H.
      * exact Htyped_callee0.
      * exact H1.
      * exact Htyped_call0.
    + split; [exact Hns_call0 |].
      split; [exact HR_call0 |].
      exact Hroots0.
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (ECallExprGeneric (EVar x) type_args args)
      T Σ' R' roots R0 H6 Hfresh HnsR HnsR0 HR0)
      as (Rcall0 & roots0 & Htyped_call0 & Hns_call0 & HR_call0 & Hroots0).
    destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EVar x) T_callee Σ_callee R_callee
      roots_callee R0 H3 (root_subst_images_exclude_names_nil rho) HnsR HnsR0 HR0)
      as (Rcallee0 & roots_callee0 & Htyped_callee0 & _ & _ & _).
    exists Rcall0, roots0, roots0. split.
    + eapply ERSSN_TypeGenericFunctionValueCall.
      * exact H.
      * exact H0.
      * exact H1.
      * exact H2.
      * exact Htyped_callee0.
      * exact H4.
      * exact H5.
      * exact Htyped_call0.
    + split; [exact Hns_call0 |].
      split; [exact HR_call0 |].
      exact Hroots0.
  - destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHHsummary1 Hfresh1 R0 HnsR HnsR0 HR0)
      as (R10 & roots10 & ret_roots10 & Hsummary10 & HnsR10 & HR10 & Hroots10).
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None)
      by (apply root_env_lookup_instantiate_none; exact H1).
    assert (Hlookup_R10_none : root_env_lookup x R10 = None)
      by (eapply root_env_equiv_lookup_none_r; eassumption).
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10))
      by (apply root_env_no_shadow_add; assumption).
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHHsummary2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 H1)
      Hns_add Heq_add)
      as (R20 & roots20 & ret_roots20 & Hsummary20 & HnsR20 & HR20 & Hroots20).
    exists (root_env_remove x R20), roots20, ret_roots20. split.
    + eapply ERSSN_Let.
      * exact Hsummary10.
      * exact H.
      * exact H0.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact Hsummary20.
      * exact H4.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + split.
      * apply root_env_no_shadow_remove. exact HnsR20.
      * split.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_remove.
              ** exact HnsR20.
              ** apply root_env_instantiate_no_shadow. exact Hns_R2.
              ** exact HR20.
           ++ apply root_env_equiv_sym.
              apply root_env_instantiate_remove_equiv.
              ** exact Hns_R2.
              ** exact Hns_R2.
              ** apply root_env_equiv_refl.
        -- exact Hroots20.
  - destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHHsummary1 Hfresh1 R0 HnsR HnsR0 HR0)
      as (R10 & roots10 & ret_roots10 & Hsummary10 & HnsR10 & HR10 & Hroots10).
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None)
      by (apply root_env_lookup_instantiate_none; exact H0).
    assert (Hlookup_R10_none : root_env_lookup x R10 = None)
      by (eapply root_env_equiv_lookup_none_r; eassumption).
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary1.
      - exact HnsR. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - eapply typed_env_roots_shadow_safe_roots.
        eapply expr_root_shadow_store_safe_narrow_summary_typed.
        exact Hsummary2.
      - apply root_env_no_shadow_add; assumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10))
      by (apply root_env_no_shadow_add; assumption).
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hexcl_roots10 : roots_exclude x roots10).
    { eapply roots_exclude_equiv.
      - apply root_set_equiv_sym. exact Hroots10.
      - eapply root_set_instantiate_excludes_images; eassumption. }
    assert (Hexcl_env10 : root_env_excludes x R10).
    { eapply root_env_excludes_equiv.
      - apply root_env_equiv_sym. exact HR10.
      - eapply root_env_instantiate_excludes_images; eassumption. }
    destruct (IHHsummary2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 H0)
      Hns_add Heq_add)
      as (R20 & roots20 & ret_roots20 & Hsummary20 & HnsR20 & HR20 & Hroots20).
    exists (root_env_remove x R20), roots20, ret_roots20. split.
    + eapply ERSSN_LetInfer.
      * exact Hsummary10.
      * exact H.
      * exact Hlookup_R10_none.
      * exact Hexcl_roots10.
      * exact Hexcl_env10.
      * exact Hsummary20.
      * exact H3.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + split.
      * apply root_env_no_shadow_remove. exact HnsR20.
      * split.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_remove.
              ** exact HnsR20.
              ** apply root_env_instantiate_no_shadow. exact Hns_R2.
              ** exact HR20.
           ++ apply root_env_equiv_sym.
              apply root_env_instantiate_remove_equiv.
              ** exact Hns_R2.
              ** exact Hns_R2.
              ** apply root_env_equiv_refl.
        -- exact Hroots20.
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EBorrow rk p) T Σ' R' roots
      R0 H Hfresh HnsR HnsR0 HR0)
      as (Rborrow0 & roots0 & Htyped0 & Hns0 & HRborrow0 & Hroots0).
    exists Rborrow0, roots0, roots0. split.
    + eapply ERSSN_BorrowDirect.
      * exact Htyped0.
      * exact H0.
      * rewrite (singleton_store_root_equiv roots0
          (root_set_instantiate rho roots) Hroots0).
        apply root_set_instantiate_singleton_store_root. exact H1.
    + split; [exact Hns0 | split; [exact HRborrow0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EBorrow RUnique p) T Σ' R' roots
      R0 H Hfresh HnsR HnsR0 HR0)
      as (Rborrow0 & roots0 & Htyped0 & Hns0 & HRborrow0 & Hroots0).
    exists Rborrow0, roots0, roots0. split.
    + eapply ERSSN_BorrowUniqueResolvedWritableChain.
      * exact Htyped0.
      * exact H0.
      * eapply place_resolved_write_writable_chain_equiv.
        -- apply root_env_equiv_sym. exact HR0.
        -- apply place_resolved_write_writable_chain_instantiate. exact H1.
      * eapply place_resolved_write_target_equiv.
        -- apply root_env_equiv_sym. exact HR0.
        -- apply place_resolved_write_target_instantiate. exact H2.
      * rewrite (singleton_store_root_equiv roots0
          (root_set_instantiate rho roots) Hroots0).
        apply root_set_instantiate_singleton_store_root. exact H3.
    + split; [exact Hns0 | split; [exact HRborrow0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ EUnit T Σ' R' roots
      R0 H Hfresh HnsR HnsR0 HR0)
      as (Runit0 & roots0 & Htyped0 & Hns0 & HRunit0 & Hroots0).
    exists Runit0, roots0, roots0. split.
    + apply ERSSN_Unit. exact Htyped0.
    + split; [exact Hns0 | split; [exact HRunit0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EStruct name lts args []) T Σ' R' roots
      R0 H1 Hfresh HnsR HnsR0 HR0)
      as (Rstruct0 & roots0 & Htyped0 & Hns0 & HRstruct0 & Hroots0).
    exists Rstruct0, roots0, []. split.
    + eapply ERSSN_EmptyStructRootless; eassumption.
    + split; [exact Hns0 | split; [exact HRstruct0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EAssign p (ELit lit)) T Σ' R' roots
      R0 H Hfresh HnsR HnsR0 HR0)
      as (Rassign0 & roots0 & Htyped0 & Hns0 & HRassign0 & Hroots0).
    exists Rassign0, roots0, roots0. split.
    + eapply ERSSN_AssignLit. exact Htyped0.
    + split; [exact Hns0 | split; [exact HRassign0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EAssign (PVar x) (ECallGeneric fname type_args []))
      T Σ' R' roots R0 H10 Hfresh HnsR HnsR0 HR0)
      as (Rassign0 & roots0 & Htyped0 & Hns0 & HRassign0 & Hroots0).
    exists Rassign0, roots0, roots0. split.
    + eapply ERSSN_AssignGenericDirect.
      * exact H.
      * exact H0.
      * exact H1.
      * exact H2.
      * exact H3.
      * exact H4.
      * exact H5.
      * exact H6.
      * exact Hsummary.
      * exact H7.
      * exact H8.
      * exact H9.
      * exact Htyped0.
    + split; [exact Hns0 | split; [exact HRassign0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EVar x) T Σ' R' roots
      R0 H Hfresh HnsR HnsR0 HR0)
      as (Rvar0 & roots0 & Htyped0 & Hns0 & HRvar0 & Hroots0).
    exists Rvar0, roots0, roots0. split.
    + eapply ERSSN_VarNonFunction; eassumption.
    + split; [exact Hns0 | split; [exact HRvar0 | exact Hroots0]].
  - destruct (typed_env_roots_shadow_safe_instantiate_fresh
      env Omega n rho R Σ (EDrop (EPlace p)) T Σ' R' roots
      R0 H Hfresh HnsR HnsR0 HR0)
      as (Rdrop0 & roots0 & Htyped0 & Hns0 & HRdrop0 & Hroots0).
    exists Rdrop0, roots0, roots0. split.
    + eapply ERSSN_DropPlaceDirect; eassumption.
    + split; [exact Hns0 | split; [exact HRdrop0 | exact Hroots0]].

Qed.


