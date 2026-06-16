From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectCallFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma typed_env_roots_shadow_safe_borrow_direct_singleton_store_root :
  forall env Omega n R Σ rk p T Σ' R' roots x path,
    typed_env_roots_shadow_safe env Omega n R Σ (EBorrow rk p)
      T Σ' R' roots ->
    place_path p = Some (x, path) ->
    singleton_store_root roots = Some x.
Proof.
  intros env Omega n R Σ rk p T Σ' R' roots x path Htyped Hpath.
  inversion Htyped; subst; try congruence.
  - rewrite (root_of_place_direct p x path Hpath). reflexivity.
  - match goal with
    | H1 : place_path ?p0 = Some (x, path),
      H2 : place_path ?p0 = Some (x0, ?path0) |- _ =>
        rewrite H1 in H2; inversion H2; subst; reflexivity
    end.
Qed.

Lemma value_has_type_vref_store_name :
  forall env s x path T,
    value_has_type env s (VRef x path) T ->
    In x (store_names s).
Proof.
  intros env s x path T Hvalue.
  remember (VRef x path) as v eqn:Hv.
  induction Hvalue; inversion Hv; subst.
  - eapply store_lookup_some_in_names; eassumption.
  - eapply IHHvalue; reflexivity.
  - eapply IHHvalue; reflexivity.
Qed.

Lemma value_has_type_ref_target_expected :
  forall env s x path T_actual u la rk T_expected,
    value_has_type env s (VRef x path) T_actual ->
    ty_lifetime_equiv T_actual (MkTy u (TRef la rk T_expected)) ->
    exists se v_target T_target,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v_target /\
      type_lookup_path env (se_ty se) path = Some T_target /\
      (value_has_type env s v_target T_target ->
       value_has_type env s v_target T_expected).
Proof.
  intros env s x path T_actual u la rk T_expected Htyped.
  remember (VRef x path) as v eqn:Hvref.
  revert x path u la rk T_expected Hvref.
  induction Htyped; intros x0 path0 u_ref la_ref rk_ref T_expected0 Hvref Heq;
    inversion Hvref; subst; try discriminate.
  - inversion Heq; subst.
    exists se, v, T. repeat split; try assumption.
    intros Hv. eapply VHT_LifetimeEquiv; eassumption.
  - inversion Heq; subst.
    inversion H; subst; try discriminate.
    + destruct (IHHtyped x0 path0 _ _ _ _ eq_refl (ty_lifetime_equiv_refl _))
        as [se0 [v0 [T0 [Hlookup [Hvalue [Htype Hcast]]]]]].
      exists se0, v0, T0. repeat split; try assumption.
      intros Hv0.
      match goal with
      | Hinner : ty_lifetime_equiv ?T_mid T_expected0 |- _ =>
          eapply VHT_LifetimeEquiv; [exact (Hcast Hv0) | exact Hinner]
      end.
    + destruct (IHHtyped x0 path0 _ _ _ _ eq_refl (ty_lifetime_equiv_refl _))
        as [se0 [v0 [T0 [Hlookup [Hvalue [Htype Hcast]]]]]].
      exists se0, v0, T0. repeat split; try assumption.
      intros Hv0.
      match goal with
      | Hcompat : ty_compatible _ ?T_inner_actual ?T_inner_expected,
        Hinner : ty_lifetime_equiv ?T_inner_expected T_expected0 |- _ =>
          eapply VHT_LifetimeEquiv;
          [ eapply VHT_Compatible; [exact (Hcast Hv0) | exact Hcompat]
          | exact Hinner ]
      end.
    + destruct (IHHtyped x0 path0 _ _ _ _ eq_refl (ty_lifetime_equiv_refl _))
        as [se0 [v0 [T0 [Hlookup [Hvalue [Htype Hcast]]]]]].
      exists se0, v0, T0. repeat split; try assumption.
      intros Hv0.
      match goal with
      | Hinner : ty_lifetime_equiv ?T_mid T_expected0 |- _ =>
          eapply VHT_LifetimeEquiv; [exact (Hcast Hv0) | exact Hinner]
      end.
  - destruct (IHHtyped x0 path0 u_ref la_ref rk_ref T_expected0 eq_refl
      (ty_lifetime_equiv_trans _ _ _ H Heq))
      as [se0 [v0 [T0 [Hlookup [Hvalue [Htype Hcast]]]]]].
    exists se0, v0, T0. repeat split; try assumption.
Qed.

Lemma eval_place_deref_runtime_target_has_type_from_ref :
  forall env Sigma s T u la rk x path,
    store_typed env s Sigma ->
    value_has_type env s (VRef x path) (MkTy u (TRef la rk T)) ->
    exists se v T_eval,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v /\
      type_lookup_path env (se_ty se) path = Some T_eval /\
      value_has_type env s v T.
Proof.
  intros env Sigma s T u la rk x path Hstore Href.
  destruct (value_has_type_ref_target_expected
    env s x path (MkTy u (TRef la rk T)) u la rk T
    Href (ty_lifetime_equiv_refl _))
    as [se_target [v_target [T_target [Hlookup_target
      [Hvalue_target [Htype_target Hcast_target]]]]]].
  destruct (store_typed_lookup env s Sigma x se_target
    Hstore Hlookup_target)
    as [T_root [st [m [Hsigma [Hname [Hse_ty [Hstate Hv_root]]]]]]].
  assert (Hv_root_actual : value_has_type env s (se_val se_target)
    (se_ty se_target)).
  { eapply VHT_LifetimeEquiv.
    - exact Hv_root.
    - apply ty_lifetime_equiv_sym. exact Hse_ty. }
  assert (Hv_target : value_has_type env s v_target T_target).
  { eapply value_lookup_path_has_type; eassumption. }
  exists se_target, v_target, T_target.
  repeat split; try assumption.
  exact (Hcast_target Hv_target).
Qed.

Lemma eval_place_typed_runtime_target_has_type :
  forall env Sigma s p T u la rk x path,
    store_typed env s Sigma ->
    typed_place_env_structural env Sigma p (MkTy u (TRef la rk T)) ->
    value_has_type env s (VRef x path) (MkTy u (TRef la rk T)) ->
    exists se v T_eval,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v /\
      type_lookup_path env (se_ty se) path = Some T_eval /\
      value_has_type env s v T.
Proof.
  intros env Sigma s p T u la rk x path Hstore _ Href.
  eapply eval_place_deref_runtime_target_has_type_from_ref; eassumption.
Qed.

Lemma value_lookup_path_app_inv_exists :
  forall v p q v_final,
    value_lookup_path v (p ++ q) = Some v_final ->
    exists v_mid,
      value_lookup_path v p = Some v_mid /\
      value_lookup_path v_mid q = Some v_final.
Proof.
  intros v p.
  revert v.
  induction p as [|seg rest IH]; intros v q v_final Hlookup.
  - exists v. simpl. split; [reflexivity | exact Hlookup].
  - simpl in Hlookup.
    destruct v as [|z|fl|b|sname fields|ename variant lts tys vals|x path|fname captured];
      try discriminate.
    destruct ((fix lookup (fields0 : list (string * value)) : option value :=
      match fields0 with
      | [] => None
      | (name, fv) :: tail =>
          if String.eqb seg name then Some fv else lookup tail
      end) fields) as [field_value |] eqn:Hfield; try discriminate.
    destruct (IH field_value q v_final Hlookup) as [v_mid [Hmid Hfinal]].
    exists v_mid. simpl. rewrite Hfield. split; assumption.
Qed.

Lemma eval_place_type_runtime_target_value_has_type :
  forall env Sigma s p T x path se v,
    store_typed env s Sigma ->
    typed_place_type_env_structural env Sigma p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    value_lookup_path (se_val se) path = Some v ->
    value_has_type env s v T.
Proof.
  intros env Sigma s p T x path se v Hstore Htyped.
  revert x path se v.
  induction Htyped; intros x_eval path_eval se_eval v_eval Heval Hlookup Hvalue.
  - inversion Heval; subst.
    simpl in Hvalue. inversion Hvalue; subst v_eval.
    destruct (store_typed_lookup env s Sigma x_eval se_eval Hstore Hlookup) as
      [T_store [st_store [m_store [Hsigma [Hname [Heq_ty [_ Hv]]]]]]].
    match goal with
    | Hsctx_lookup : sctx_lookup x_eval Sigma = Some (?T_static, ?st_static) |- _ =>
        rewrite Hsctx_lookup in Hsigma;
        inversion Hsigma; subst T_store st_store;
        exact Hv
    end.
  - inversion Heval; subst.
    assert (Href : value_has_type env s (VRef x_eval path_eval) (MkTy u (TRef la rk T))).
    { eapply IHHtyped; eassumption. }
    destruct (eval_place_deref_runtime_target_has_type_from_ref
      env Sigma s T u la rk x_eval path_eval Hstore Href) as
      [se_target [v_target [T_target [Hlookup_target
        [Hvalue_target [Htype_target Hv_target]]]]]].
    rewrite Hlookup in Hlookup_target.
    inversion Hlookup_target; subst se_target.
    rewrite Hvalue in Hvalue_target.
    inversion Hvalue_target; subst v_target.
    exact Hv_target.
  - inversion Heval; subst.
    destruct (value_lookup_path_app_inv_exists
      (se_val se_eval) path [field_name fdef] v_eval Hvalue)
      as [v_parent [Hvalue_parent Hvalue_field]].
    assert (Hv_parent : value_has_type env s v_parent T_parent).
    { eapply IHHtyped; eassumption. }
    assert (Hfield_type :
      type_lookup_path env T_parent [field_name fdef] =
        Some (instantiate_struct_field_ty lts args fdef)).
    { simpl. rewrite H. rewrite H0. rewrite H1. reflexivity. }
    destruct (value_has_type_path_exists env s v_parent T_parent
      [field_name fdef] (instantiate_struct_field_ty lts args fdef)
      Hv_parent Hfield_type) as [v_field [Hvalue_field' Hv_field]].
    rewrite Hvalue_field in Hvalue_field'.
    inversion Hvalue_field'; subst v_field.
    exact Hv_field.
Qed.

Lemma eval_place_runtime_target_value_has_type :
  forall env Sigma s p T x path se v,
    store_typed env s Sigma ->
    typed_place_env_structural env Sigma p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    value_lookup_path (se_val se) path = Some v ->
    value_has_type env s v T.
Proof.
  intros env Sigma s p T x path se v Hstore Htyped Heval Hlookup Hvalue.
  eapply eval_place_type_runtime_target_value_has_type.
  - exact Hstore.
  - apply typed_place_env_structural_to_type_env_structural. exact Htyped.
  - exact Heval.
  - exact Hlookup.
  - exact Hvalue.
Qed.

Lemma check_expr_root_shadow_store_safe_narrow_summary_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_narrow_summary_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_store_safe_narrow_summary_fuel] in Hcheck.
    rewrite Hinfer in Hcheck.
    destruct e; try discriminate.
    + pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ EUnit T Σ' R' roots Hinfer)
        as Htyped_unit.
      exists roots.
      apply ERSSN_Unit. exact Htyped_unit.
    + match goal with
      | Hinfer_lit : infer_core_env_state_fuel_roots_shadow_safe _ _ _ _ _ _
            ?expr_lit = _ |- _ =>
          pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
            (S fuel') env Omega n R Σ expr_lit T Σ' R' roots Hinfer_lit)
            as Htyped_lit
      end.
      exists roots.
      apply ERSSN_Lit. exact Htyped_lit.
    + simpl in Hcheck.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (EVar i) T Σ' R' roots Hinfer)
        as Htyped_var.
      destruct (non_function_value_ty_b T) eqn:Hnonfn; try discriminate.
      exists roots.
      eapply ERSSN_VarNonFunction; eassumption.
    + simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
        try discriminate.
      destruct (non_function_value_ty_b t) eqn:Hnonfn;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2 Sigma2] R2] roots2] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[Hsctx_ok Hroots2] Henv2] Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i t m Σ1) e2 T2 Sigma2 R2 roots2 Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_ok, Hroots2, Henv2 in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSSN_Let.
      all: try eassumption.
      all: try (apply roots_exclude_b_sound; assumption).
      all: try (apply root_env_excludes_b_sound; assumption).
      Unshelve.
      all: try eassumption.
      all: try (apply roots_exclude_b_sound; assumption).
      all: try (apply root_env_excludes_b_sound; assumption).
    + simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (non_function_value_ty_b T1) eqn:Hnonfn;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i T1 m Σ1) e2)
        as [[[[T2 Sigma2] R2] roots2] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[Hsctx_ok Hroots2] Henv2] Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i T1 m Σ1) e2 T2 Sigma2 R2 roots2 Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_ok, Hroots2, Henv2 in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSSN_LetInfer.
      all: try eassumption.
      all: try (apply roots_exclude_b_sound; assumption).
      all: try (apply root_env_excludes_b_sound; assumption).
      Unshelve.
      all: try eassumption.
      all: try (apply roots_exclude_b_sound; assumption).
      all: try (apply root_env_excludes_b_sound; assumption).
    + apply andb_true_iff in Hcheck as [Hready_args Hsupported].
      pose proof
        (check_supported_non_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hinfer_callee & Hcallee_shape).
      subst e.
      pose proof (infer_core_env_roots_shadow_safe_sound
        env Omega n R (ctx_of_sctx Σ) (EVar x) T_callee Gamma_callee
        R_callee roots_callee Hinfer_callee) as Htyped_callee.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (ECallExpr (EVar x) l) T Σ' R'
        roots Hinfer) as Htyped_call.
      exists roots.
      eapply ERSSN_FunctionValueCall.
      * apply store_safe_function_value_call_args_b_sound. exact Hready_args.
      * exact Htyped_callee.
      * exact Hcallee_shape.
      * exact Htyped_call.
    + apply andb_true_iff in Hcheck as [Hready_supported _Hinstantiated_all].
      apply andb_true_iff in Hready_supported as [Hready_args Hsupported].
      pose proof
        (check_supported_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l l0 Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hclosed & Hno_top & Hinfer_callee & Harity_shape & Hcallee_shape).
      subst e.
      pose proof (infer_core_env_roots_shadow_safe_sound
        env Omega n R (ctx_of_sctx Σ) (EVar x) T_callee Gamma_callee
        R_callee roots_callee Hinfer_callee) as Htyped_callee.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (ECallExprGeneric (EVar x) l l0) T Σ' R'
        roots Hinfer) as Htyped_call.
      exists roots.
      eapply ERSSN_TypeGenericFunctionValueCall.
      * apply store_safe_function_value_call_args_b_sound. exact Hready_args.
      * exact Hclosed.
      * exact Hno_top.
      * exact _Hinstantiated_all.
      * exact Htyped_callee.
      * exact Hcallee_shape.
      * intros type_params bounds body Hcore.
        destruct Harity_shape as
          (u0 & type_params0 & body0 & HT_callee & Harity).
        subst T_callee. simpl in Hcore.
        pose proof Harity as Hlen.
        dependent destruction Hcore. exact Hlen.
      * exact Htyped_call.
    + simpl in Hcheck.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (EStruct s l l0 l1) T Σ' R' roots Hinfer)
        as Htyped_struct.
      destruct l1; try discriminate.
      destruct (lookup_struct s env) as [sdef |] eqn:Hlookup; try discriminate.
      destruct (struct_bounds sdef) eqn:Hbounds; try discriminate.
      destruct (capture_ref_free_ty_b env T) eqn:Hfree; try discriminate.
      exists [].
      eapply ERSSN_EmptyStructRootless; eassumption.
    + simpl in Hcheck.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (EAssign p e) T Σ' R' roots Hinfer)
        as Htyped_assign.
      destruct e; simpl in Hcheck; try (destruct p; discriminate).
      * exists roots.
        eapply ERSSN_AssignLit.
        exact Htyped_assign.
      * destruct p; try discriminate.
        destruct l0; try discriminate.
        destruct (lookup_fn_b i (env_fns env)) as [fcallee |] eqn:Hlookup;
          try discriminate.
        destruct (fn_bounds fcallee) eqn:Hbounds; try discriminate.
        destruct (fn_params fcallee) eqn:Hparams; try discriminate.
        apply andb_true_iff in Hcheck as [Harity Hcheck].
        apply Nat.eqb_eq in Harity.
        set (body_ctx := subst_type_params_ctx l (fn_body_ctx fcallee)) in *.
        set (body := subst_type_params_expr l (fn_body fcallee)) in *.
        destruct body_ctx as [| ctx_head ctx_tail] eqn:Hbody_ctx; try discriminate.
        destruct body as [| | | | | | | | | | | | sname lts tys fields | | | | | | | |]
          eqn:Hbody_shape_eq; try discriminate.
        destruct fields as [| field fields_tail] eqn:Hfields.
        2: discriminate.
        destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env
          (fn_outlives fcallee) (fn_lifetimes fcallee)
          (initial_root_env_for_fn fcallee) (sctx_of_ctx [])
          (EStruct sname lts tys []))
          as [[[[T_body Sigma_body] R_body] roots_body] | err_body]
          eqn:Hbody_infer; try discriminate.
        destruct (infer_env_roots_shadow_safe env fcallee
          (initial_root_env_for_fn fcallee)) as [Gamma_env | err_env]
          eqn:Henv; try discriminate.
        destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R Σ
          (ECallGeneric i l [])) as [[[[T_rhs Sigma_rhs] R_rhs] roots_rhs] | err_rhs]
          eqn:Hrhs_infer; try discriminate.
        destruct (infer_place_sctx env Σ (PVar i0)) as [T_old | err_place]
          eqn:Hplace_infer.
        2: unfold infer_place_sctx in Hplace_infer; simpl in Hplace_infer;
           rewrite Hplace_infer in Hcheck; discriminate.
        unfold infer_place_sctx in Hplace_infer. simpl in Hplace_infer.
        rewrite Hplace_infer in Hcheck.
        repeat rewrite andb_true_iff in Hcheck.
        destruct Hcheck as [[[[Hbody_check Hcompat_body] Hroots_excl] Henv_excl]
          Hcompat_assign].
        destruct (IH env (fn_outlives fcallee) (fn_lifetimes fcallee)
          (initial_root_env_for_fn fcallee) (sctx_of_ctx [])
          (EStruct sname lts tys []) T_body Sigma_body R_body roots_body
          Hbody_infer Hbody_check) as [ret_roots_body Hsummary_body].
        apply lookup_fn_b_sound in Hlookup as [Hin_callee Hname_callee].
        assert (Hsummary_assign :
          expr_root_shadow_store_safe_narrow_summary env Omega n R Σ
            (EAssign (PVar i0) (ECallGeneric i l [])) T Σ' R' roots roots).
        { eapply ERSSN_AssignGenericDirect with
            (fcallee := fcallee) (T_body := T_body)
            (Sigma_body := Sigma_body) (R_body := R_body)
            (roots_body := roots_body) (ret_roots_body := ret_roots_body)
            (sname := sname) (lts := lts) (tys := tys).
          - exact Hin_callee.
          - exact Hname_callee.
          - exact Harity.
          - exact Hbounds.
          - exact Hparams.
          - unfold body_ctx in Hbody_ctx. exact Hbody_ctx.
          - unfold body in Hbody_shape_eq. exact Hbody_shape_eq.
          - rewrite Hparams. simpl. constructor.
          - unfold body_ctx in Hbody_ctx.
            unfold body in Hbody_shape_eq.
            rewrite Hbody_ctx. rewrite Hbody_shape_eq.
            exact Hsummary_body.
          - exact Hcompat_body.
          - rewrite Hparams. apply fn_params_roots_exclude_b_sound. exact Hroots_excl.
          - rewrite Hparams. apply fn_params_root_env_excludes_b_sound. exact Henv_excl.
          - exact Htyped_assign. }
        exists roots. exact Hsummary_assign.
    + simpl in Hcheck.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (EBorrow r p) T Σ' R' roots Hinfer)
        as Htyped_borrow.
      destruct (place_path p) as [[x path] |] eqn:Hpath.
      * exists roots.
        eapply ERSSN_BorrowDirect.
        -- exact Htyped_borrow.
        -- exact Hpath.
        -- eapply typed_env_roots_shadow_safe_borrow_direct_singleton_store_root;
             eassumption.
      * destruct r; cbn in Hcheck.
        -- discriminate.
        -- apply andb_true_iff in Hcheck as [Hchain Hcheck].
           destruct (place_resolved_write_target R p) as [root_x |] eqn:Htarget;
             try discriminate.
           destruct (singleton_store_root roots) as [root_y |] eqn:Hsingle;
             try discriminate.
           destruct (ident_eqb root_x root_y) eqn:Heq; try discriminate.
           apply ident_eqb_eq in Heq. subst root_y.
           exists roots.
           exact (ERSSN_BorrowUniqueResolvedWritableChain env Omega n R Σ p T Σ' R' roots root_x
             Htyped_borrow Hpath
             (place_resolved_write_writable_chain_b_sound env R Σ p Hchain)
             Htarget Hsingle).
    + simpl in Hcheck.
      pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
        (S fuel') env Omega n R Σ (EDrop e) T Σ' R' roots Hinfer)
        as Htyped_drop.
      destruct e; try discriminate.
      destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      exists roots.
      eapply ERSSN_DropPlaceDirect; eassumption.
Qed.

Lemma check_expr_root_shadow_store_safe_narrow_summary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_narrow_summary
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_narrow_summary,
    infer_core_env_roots_shadow_safe.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Omega n R
    (sctx_of_ctx Gamma) e) as [[[[T0 Sigma0] R0] roots0] | err]
    eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_narrow_summary_fuel_sound;
    eassumption.
Qed.



Lemma infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    infer_core_env_state_fuel_roots_shadow_safe_checked fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots_for_checked_result env T roots).
Proof.
  intros fuel env Omega n R Σ e T Σ' R' roots Hinfer.
  destruct fuel as [| fuel'];
    cbn [infer_core_env_state_fuel_roots_shadow_safe
         infer_core_env_state_fuel_roots_shadow_safe_checked] in *;
    try discriminate;
    try rewrite Hinfer;
    reflexivity.
Qed.

Lemma infer_core_env_state_fuel_roots_shadow_safe_checked_safe_ok :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    infer_core_env_state_fuel_roots_shadow_safe_checked fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots_for_checked_result env T roots).
Proof.
  intros. eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe.
  eassumption.
Qed.

Lemma infer_core_env_state_fuel_roots_shadow_safe_checked_capture_free_ok :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    capture_ref_free_ty_b env T = true ->
    infer_core_env_state_fuel_roots_shadow_safe_checked fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', []).
Proof.
  intros fuel env Omega n R Σ e T Σ' R' roots Hinfer Hfree.
  rewrite (infer_core_env_state_fuel_roots_shadow_safe_checked_safe_ok
    fuel env Omega n R Σ e T Σ' R' roots Hinfer).
  unfold roots_for_checked_result. rewrite Hfree. reflexivity.
Qed.

Lemma check_expr_root_shadow_store_safe_narrow_summary_checked_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe_checked
      fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - cbn [infer_core_env_state_fuel_roots_shadow_safe_checked] in Hinfer.
    discriminate.
  - cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel]
      in Hcheck.
    destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel
      (S fuel') env Omega n R Σ e) eqn:Hnarrow.
    + pose proof Hnarrow as Hnarrow_full.
      cbn [check_expr_root_shadow_store_safe_narrow_summary_fuel] in Hnarrow.
      cbn [infer_core_env_state_fuel_roots_shadow_safe_checked] in Hinfer.
      destruct (infer_core_env_state_fuel_roots_shadow_safe
        (S fuel') env Omega n R Σ e)
        as [[[[T0 Σ0] R0] roots0] | err] eqn:Hun.
      * unfold roots_for_checked_result in Hinfer.
        destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel_sound
          (S fuel') env Omega n R Σ e T0 Σ0 R0 roots0 Hun Hnarrow_full)
          as [ret_roots Hsummary].
        destruct (capture_ref_free_ty_b env T0) eqn:Hfree;
          inversion Hinfer; subst; clear Hinfer.
        -- exists ret_roots.
           eapply ERSSNC_CaptureRefFreeResult; eassumption.
        -- exists ret_roots.
           apply ERSSNC_Conservative. exact Hsummary.
      * discriminate Hnarrow.
    + cbn [infer_core_env_state_fuel_roots_shadow_safe_checked] in Hinfer.
      destruct (infer_core_env_state_fuel_roots_shadow_safe
        (S fuel') env Omega n R Σ e)
        as [[[[Ttop Sigmatop] Rtop] roots_top] | err_top]
        eqn:Hun_top.
      * destruct e as [|lit|xv|mlet xlet t e1 e2|mlet xlet e1 e2|fn|fn caps|p|f args|f tys args|callee args|callee tys args|sn ls tys fields|en variant ls tys args|scrut branches|p e1|p e1|rk p|ed|e1|e1 e2 e3]; try discriminate.
        -- cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel] in Hcheck.
           try rewrite Hun_top in Hcheck.
           cbn [infer_core_env_state_fuel_roots_shadow_safe] in Hun_top.
           destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R Σ e1)
             as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1; try discriminate.
           destruct (ty_compatible_b Omega T1 t) eqn:Hcompat; try discriminate.
           destruct (root_env_lookup xlet R1) as [roots_x |] eqn:Hlookup_x; try discriminate.
           destruct (roots_exclude_b xlet roots1 && root_env_excludes_b xlet R1)
             eqn:Hroots_env; try discriminate.
           apply andb_true_iff in Hroots_env as [Hroots1 Henv1].
           destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
             (root_env_add xlet roots1 R1) (sctx_add xlet t mlet Σ1) e2)
             as [[[[T2 Sigma2] R2] roots2] | err2] eqn:He2; try discriminate.
           destruct (sctx_check_ok env xlet t Sigma2 && roots_exclude_b xlet roots2 &&
             root_env_excludes_b xlet (root_env_remove xlet R2)) eqn:Hbody_ok; try discriminate.
           repeat rewrite andb_true_iff in Hbody_ok.
           destruct Hbody_ok as [[Hsctx_ok Hroots2] Henv2].
           inversion Hun_top; subst Ttop Sigmatop Rtop roots_top; clear Hun_top.
           destruct (non_function_value_ty_b t) eqn:Hnonfn; try discriminate.
           destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel fuel' env Omega n R Σ e1)
             eqn:He1_narrow.
           ++ destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel_sound
                fuel' env Omega n R Σ e1 T1 Σ1 R1 roots1 He1 He1_narrow)
                as [ret_roots1 Hsummary1_legacy].
              pose proof (ERSSNC_Conservative env Omega n R Σ e1 T1 Σ1 R1
                roots1 ret_roots1 Hsummary1_legacy) as Hsummary1.
              assert (Hsummary1_case :
                expr_root_shadow_store_safe_narrow_summary_checked
                  env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 \/
                (typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1 /\
                 expr_root_shadow_store_safe_narrow_summary_checked
                   env Omega n R Σ e1 T1 Σ1 R1 [] ret_roots1 /\
                 capture_ref_free_ty_b env T1 = true)) by (left; exact Hsummary1).
              try rewrite He1 in Hcheck. try rewrite Hcompat in Hcheck. try rewrite Hnonfn in Hcheck. try rewrite He1_narrow in Hcheck. try rewrite Hlookup_x in Hcheck.
              try rewrite Hroots1 in Hcheck. try rewrite Henv1 in Hcheck. try rewrite He2 in Hcheck. try rewrite Hsctx_ok in Hcheck. try rewrite Henv2 in Hcheck.
              simpl in Hcheck.
              destruct (capture_ref_free_ty_b env T2) eqn:Hfree; try discriminate.
              destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet t mlet Σ1) e2)
                eqn:He2_check; try discriminate.
              assert (He2_checked : infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet t mlet Σ1) e2 =
                infer_ok (T2, Sigma2, R2, roots_for_checked_result env T2 roots2)).
              { eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe. exact He2. }
              destruct (IH env Omega n (root_env_add xlet roots1 R1)
                (sctx_add xlet t mlet Σ1) e2 T2 Sigma2 R2
                (roots_for_checked_result env T2 roots2) He2_checked He2_check)
                as [ret_roots Hsummary2].
              unfold roots_for_checked_result in Hinfer. rewrite Hfree in Hinfer.
              inversion Hinfer; subst; clear Hinfer.
              exists ret_roots.
              destruct Hsummary1_case as [Hsummary1_final | [Htyped1 [Hsummary1_final Hfree1]]].
              ** eapply ERSSNC_Let_CaptureRefFreeResult;
                   eauto using roots_exclude_b_sound, root_env_excludes_b_sound.
              ** eapply ERSSNC_Let_BoundCheckedCaptureRefFreeResult;
                   eauto using roots_exclude_b_sound, root_env_excludes_b_sound.
           ++ try rewrite He1 in Hcheck. try rewrite Hcompat in Hcheck. try rewrite Hnonfn in Hcheck. try rewrite He1_narrow in Hcheck. try rewrite Hlookup_x in Hcheck.
              try rewrite Hroots1 in Hcheck. try rewrite Henv1 in Hcheck. try rewrite He2 in Hcheck. try rewrite Hsctx_ok in Hcheck. try rewrite Henv2 in Hcheck.
              simpl in Hcheck.
              destruct (capture_ref_free_ty_b env T1) eqn:Hfree1; try discriminate.
              destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel' env Omega n R Σ e1)
                eqn:He1_checked_check; try discriminate.
              destruct (capture_ref_free_ty_b env T2) eqn:Hfree; try discriminate.
              destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet t mlet Σ1) e2)
                eqn:He2_check; try discriminate.
              assert (He1_checked : infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Omega n R Σ e1 =
                infer_ok (T1, Σ1, R1, [])).
              { replace [] with (roots_for_checked_result env T1 roots1).
                - eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe.
                  exact He1.
                - unfold roots_for_checked_result. rewrite Hfree1. reflexivity. }
              destruct (IH env Omega n R Σ e1 T1 Σ1 R1 [] He1_checked He1_checked_check)
                as [ret_roots1 Hsummary1].
              pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
                fuel' env Omega n R Σ e1 T1 Σ1 R1 roots1 He1) as Htyped1.
              assert (He2_checked : infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet t mlet Σ1) e2 =
                infer_ok (T2, Sigma2, R2, roots_for_checked_result env T2 roots2)).
              { eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe. exact He2. }
              destruct (IH env Omega n (root_env_add xlet roots1 R1)
                (sctx_add xlet t mlet Σ1) e2 T2 Sigma2 R2
                (roots_for_checked_result env T2 roots2) He2_checked He2_check)
                as [ret_roots Hsummary2].
              unfold roots_for_checked_result in Hinfer. rewrite Hfree in Hinfer.
              inversion Hinfer; subst; clear Hinfer.
              exists ret_roots.
              eapply ERSSNC_Let_BoundCheckedCaptureRefFreeResult;
                eauto using roots_exclude_b_sound, root_env_excludes_b_sound.
        -- cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel] in Hcheck.
           try rewrite Hun_top in Hcheck.
           cbn [infer_core_env_state_fuel_roots_shadow_safe] in Hun_top.
           destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R Σ e1)
             as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1; try discriminate.
           destruct (root_env_lookup xlet R1) as [roots_x |] eqn:Hlookup_x; try discriminate.
           destruct (roots_exclude_b xlet roots1 && root_env_excludes_b xlet R1)
             eqn:Hroots_env; try discriminate.
           apply andb_true_iff in Hroots_env as [Hroots1 Henv1].
           destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
             (root_env_add xlet roots1 R1) (sctx_add xlet T1 mlet Σ1) e2)
             as [[[[T2 Sigma2] R2] roots2] | err2] eqn:He2; try discriminate.
           destruct (sctx_check_ok env xlet T1 Sigma2 && roots_exclude_b xlet roots2 &&
             root_env_excludes_b xlet (root_env_remove xlet R2)) eqn:Hbody_ok; try discriminate.
           repeat rewrite andb_true_iff in Hbody_ok.
           destruct Hbody_ok as [[Hsctx_ok Hroots2] Henv2].
           inversion Hun_top; subst Ttop Sigmatop Rtop roots_top; clear Hun_top.
           destruct (non_function_value_ty_b T1) eqn:Hnonfn; try discriminate.
           destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel fuel' env Omega n R Σ e1)
             eqn:He1_narrow.
           ++ destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel_sound
                fuel' env Omega n R Σ e1 T1 Σ1 R1 roots1 He1 He1_narrow)
                as [ret_roots1 Hsummary1_legacy].
              pose proof (ERSSNC_Conservative env Omega n R Σ e1 T1 Σ1 R1
                roots1 ret_roots1 Hsummary1_legacy) as Hsummary1.
              try rewrite He1 in Hcheck. try rewrite Hnonfn in Hcheck. try rewrite He1_narrow in Hcheck. try rewrite Hlookup_x in Hcheck.
              try rewrite Hroots1 in Hcheck. try rewrite Henv1 in Hcheck. try rewrite He2 in Hcheck. try rewrite Hsctx_ok in Hcheck. try rewrite Henv2 in Hcheck.
              simpl in Hcheck.
              destruct (capture_ref_free_ty_b env T2) eqn:Hfree; try discriminate.
              destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet T1 mlet Σ1) e2)
                eqn:He2_check; try discriminate.
              assert (He2_checked : infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet T1 mlet Σ1) e2 =
                infer_ok (T2, Sigma2, R2, roots_for_checked_result env T2 roots2)).
              { eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe. exact He2. }
              destruct (IH env Omega n (root_env_add xlet roots1 R1)
                (sctx_add xlet T1 mlet Σ1) e2 T2 Sigma2 R2
                (roots_for_checked_result env T2 roots2) He2_checked He2_check)
                as [ret_roots Hsummary2].
              unfold roots_for_checked_result in Hinfer. rewrite Hfree in Hinfer.
              inversion Hinfer; subst; clear Hinfer.
              exists ret_roots.
              eapply ERSSNC_LetInfer_CaptureRefFreeResult;
                eauto using roots_exclude_b_sound, root_env_excludes_b_sound.
           ++ try rewrite He1 in Hcheck. try rewrite Hnonfn in Hcheck. try rewrite He1_narrow in Hcheck. try rewrite Hlookup_x in Hcheck.
              try rewrite Hroots1 in Hcheck. try rewrite Henv1 in Hcheck. try rewrite He2 in Hcheck. try rewrite Hsctx_ok in Hcheck. try rewrite Henv2 in Hcheck.
              simpl in Hcheck.
              destruct (capture_ref_free_ty_b env T1) eqn:Hfree1; try discriminate.
              destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel' env Omega n R Σ e1)
                eqn:He1_checked_check; try discriminate.
              destruct (capture_ref_free_ty_b env T2) eqn:Hfree; try discriminate.
              destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet T1 mlet Σ1) e2)
                eqn:He2_check; try discriminate.
              assert (He1_checked : infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Omega n R Σ e1 =
                infer_ok (T1, Σ1, R1, [])).
              { replace [] with (roots_for_checked_result env T1 roots1).
                - eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe.
                  exact He1.
                - unfold roots_for_checked_result. rewrite Hfree1. reflexivity. }
              destruct (IH env Omega n R Σ e1 T1 Σ1 R1 [] He1_checked He1_checked_check)
                as [ret_roots1 Hsummary1].
              pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
                fuel' env Omega n R Σ e1 T1 Σ1 R1 roots1 He1) as Htyped1.
              assert (He2_checked : infer_core_env_state_fuel_roots_shadow_safe_checked fuel' env Omega n
                (root_env_add xlet roots1 R1) (sctx_add xlet T1 mlet Σ1) e2 =
                infer_ok (T2, Sigma2, R2, roots_for_checked_result env T2 roots2)).
              { eapply infer_core_env_state_fuel_roots_shadow_safe_checked_from_safe. exact He2. }
              destruct (IH env Omega n (root_env_add xlet roots1 R1)
                (sctx_add xlet T1 mlet Σ1) e2 T2 Sigma2 R2
                (roots_for_checked_result env T2 roots2) He2_checked He2_check)
                as [ret_roots Hsummary2].
              unfold roots_for_checked_result in Hinfer. rewrite Hfree in Hinfer.
              inversion Hinfer; subst; clear Hinfer.
              exists ret_roots.
              eapply ERSSNC_LetInfer_BoundCheckedCaptureRefFreeResult;
                eauto using roots_exclude_b_sound, root_env_excludes_b_sound.
        -- try rewrite Hun_top in Hcheck.
           destruct fields; try discriminate.
           destruct (capture_ref_free_ty_b env Ttop) eqn:Hfree_top;
             try discriminate.
           unfold roots_for_checked_result in Hinfer.
           rewrite Hfree_top in Hinfer.
           inversion Hinfer; subst; clear Hinfer.
           exists [].
           refine (ERSSNC_EmptyStruct_CaptureRefFreeResult env Omega n R Σ
             sn ls tys T Σ' R' roots_top _ Hfree_top).
           eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
           exact Hun_top.
        -- try rewrite Hun_top in Hcheck.
           destruct ed; try discriminate.
           destruct r; try discriminate.
           destruct (capture_ref_free_ty_b env Ttop) eqn:Hfree_top;
             try discriminate.
           unfold roots_for_checked_result in Hinfer.
           rewrite Hfree_top in Hinfer.
           inversion Hinfer; subst; clear Hinfer.
           exists [].
           refine (ERSSNC_DerefBorrowShared_CaptureRefFreeResult env Omega n R Σ
             p T Σ' R' roots_top _ Hfree_top).
           eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
           exact Hun_top.
      * destruct fuel' as [| fuel''].
        { destruct e; cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
            infer_core_env_state_fuel_roots_shadow_safe
            infer_core_env_state_fuel_roots_shadow_safe_checked]
            in Hcheck; discriminate. }
        destruct e as [|lit|xv|mlet xlet t e1 e2|mlet xlet e1 e2|fn|fn caps|p|f args|f tys args|callee args|callee tys args|sn ls tys fields|en variant ls tys args|scrut branches|p e1|p e1|rk p|e1|e1|e1 e2 e3];
          cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel]
            in Hcheck; try discriminate.
        -- destruct (infer_core_env_state_fuel_roots_shadow_safe
            (S fuel'') env Omega n R Σ e1)
            as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1;
            try discriminate.
          destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
            try discriminate.
          destruct (non_function_value_ty_b t) eqn:Hnonfn;
            try discriminate.
          apply andb_true_iff in Hcheck as [He1_check Hcheck].
          assert (Hsummary1_pack : exists ret_roots1,
            expr_root_shadow_store_safe_narrow_summary_checked
              env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 \/
            (typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1 /\
             expr_root_shadow_store_safe_narrow_summary_checked
               env Omega n R Σ e1 T1 Σ1 R1 [] ret_roots1 /\
             capture_ref_free_ty_b env T1 = true)).
          { destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel
              (S fuel'') env Omega n R Σ e1) eqn:He1_narrow.
            - destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel_sound
                (S fuel'') env Omega n R Σ e1 T1 Σ1 R1 roots1 He1 He1_narrow)
                as [ret_roots1 Hsummary1_legacy].
              pose proof (ERSSNC_Conservative env Omega n R Σ e1 T1 Σ1 R1
                roots1 ret_roots1 Hsummary1_legacy) as Hsummary1.
              exists ret_roots1. left. exact Hsummary1.
            - simpl in He1_check.
              apply andb_true_iff in He1_check as [Hfree1 He1_checked_check].
              assert (He1_checked :
                infer_core_env_state_fuel_roots_shadow_safe_checked
                  (S fuel'') env Omega n R Σ e1 =
                infer_ok (T1, Σ1, R1, [])).
              { eapply infer_core_env_state_fuel_roots_shadow_safe_checked_capture_free_ok; eassumption. }
              assert (He1_checked_check_full :
                check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                  (S fuel'') env Omega n R Σ e1 = true).
              { cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel].
                rewrite He1_narrow. rewrite He1. exact He1_checked_check. }
              destruct (IH env Omega n R Σ e1 T1 Σ1 R1 [] He1_checked
                He1_checked_check_full) as [ret_roots1 Hsummary1].
              pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
                (S fuel'') env Omega n R Σ e1 T1 Σ1 R1 roots1 He1) as Htyped1.
              exists ret_roots1. right. repeat split; assumption. }
          destruct Hsummary1_pack as [ret_roots1 Hsummary1_case].
          destruct (root_env_lookup xlet R1) as [roots_x |] eqn:Hlookup_x;
            try discriminate.
          apply andb_true_iff in Hcheck as [Hroots1 Hcheck].
          apply andb_true_iff in Hroots1 as [Hroots1 Henv1].
          destruct (infer_core_env_state_fuel_roots_shadow_safe_checked
            (S fuel'') env Omega n (root_env_add xlet roots1 R1)
            (sctx_add xlet t mlet Σ1) e2)
            as [[[[T2 Sigma2] R2] roots2] | err2] eqn:He2;
            try discriminate.
          repeat rewrite andb_true_iff in Hcheck.
          destruct Hcheck as [[[Hsctx_ok Hfree] Henv2] He2_check].
          destruct (IH env Omega n (root_env_add xlet roots1 R1)
            (sctx_add xlet t mlet Σ1) e2 T2 Sigma2 R2 roots2 He2
            He2_check) as [ret_roots Hsummary2].
          simpl in Hinfer.
          try rewrite He1 in Hinfer.
          try rewrite Hcompat in Hinfer.
          try rewrite Hlookup_x in Hinfer.
          try rewrite Hroots1 in Hinfer.
          try rewrite Henv1 in Hinfer.
          try rewrite He2 in Hinfer.
          try rewrite Hsctx_ok in Hinfer.
          try rewrite Hfree in Hinfer.
          try rewrite Henv2 in Hinfer.
          unfold roots_for_checked_result in Hinfer.
          rewrite Hfree in Hinfer.
          inversion Hinfer; subst; clear Hinfer.
          exists ret_roots.
          destruct Hsummary1_case as [Hsummary1 | [Htyped1 [Hsummary1 Hfree1]]].
          { eapply ERSSNC_Let_CaptureRefFreeResult;
              eauto using roots_exclude_b_sound, root_env_excludes_b_sound. }
          { eapply ERSSNC_Let_BoundCheckedCaptureRefFreeResult;
              eauto using roots_exclude_b_sound, root_env_excludes_b_sound. }
        -- destruct (infer_core_env_state_fuel_roots_shadow_safe
            (S fuel'') env Omega n R Σ e1)
            as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1;
            try discriminate.
          destruct (non_function_value_ty_b T1) eqn:Hnonfn;
            try discriminate.
          apply andb_true_iff in Hcheck as [He1_check Hcheck].
          assert (Hsummary1_pack : exists ret_roots1,
            expr_root_shadow_store_safe_narrow_summary_checked
              env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 \/
            (typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1 /\
             expr_root_shadow_store_safe_narrow_summary_checked
               env Omega n R Σ e1 T1 Σ1 R1 [] ret_roots1 /\
             capture_ref_free_ty_b env T1 = true)).
          { destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel
              (S fuel'') env Omega n R Σ e1) eqn:He1_narrow.
            - destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel_sound
                (S fuel'') env Omega n R Σ e1 T1 Σ1 R1 roots1 He1 He1_narrow)
                as [ret_roots1 Hsummary1_legacy].
              pose proof (ERSSNC_Conservative env Omega n R Σ e1 T1 Σ1 R1
                roots1 ret_roots1 Hsummary1_legacy) as Hsummary1.
              exists ret_roots1. left. exact Hsummary1.
            - simpl in He1_check.
              apply andb_true_iff in He1_check as [Hfree1 He1_checked_check].
              assert (He1_checked :
                infer_core_env_state_fuel_roots_shadow_safe_checked
                  (S fuel'') env Omega n R Σ e1 =
                infer_ok (T1, Σ1, R1, [])).
              { eapply infer_core_env_state_fuel_roots_shadow_safe_checked_capture_free_ok; eassumption. }
              assert (He1_checked_check_full :
                check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                  (S fuel'') env Omega n R Σ e1 = true).
              { cbn [check_expr_root_shadow_store_safe_narrow_summary_checked_fuel].
                rewrite He1_narrow. rewrite He1. exact He1_checked_check. }
              destruct (IH env Omega n R Σ e1 T1 Σ1 R1 [] He1_checked
                He1_checked_check_full) as [ret_roots1 Hsummary1].
              pose proof (infer_core_env_state_fuel_roots_shadow_safe_sound
                (S fuel'') env Omega n R Σ e1 T1 Σ1 R1 roots1 He1) as Htyped1.
              exists ret_roots1. right. repeat split; assumption. }
          destruct Hsummary1_pack as [ret_roots1 Hsummary1_case].
          destruct (root_env_lookup xlet R1) as [roots_x |] eqn:Hlookup_x;
            try discriminate.
          apply andb_true_iff in Hcheck as [Hroots1 Hcheck].
          apply andb_true_iff in Hroots1 as [Hroots1 Henv1].
          destruct (infer_core_env_state_fuel_roots_shadow_safe_checked
            (S fuel'') env Omega n (root_env_add xlet roots1 R1)
            (sctx_add xlet T1 mlet Σ1) e2)
            as [[[[T2 Sigma2] R2] roots2] | err2] eqn:He2;
            try discriminate.
          repeat rewrite andb_true_iff in Hcheck.
          destruct Hcheck as [[[Hsctx_ok Hfree] Henv2] He2_check].
          destruct (IH env Omega n (root_env_add xlet roots1 R1)
            (sctx_add xlet T1 mlet Σ1) e2 T2 Sigma2 R2 roots2 He2
            He2_check) as [ret_roots Hsummary2].
          simpl in Hinfer.
          try rewrite He1 in Hinfer.
          try rewrite Hlookup_x in Hinfer.
          try rewrite Hroots1 in Hinfer.
          try rewrite Henv1 in Hinfer.
          try rewrite He2 in Hinfer.
          try rewrite Hsctx_ok in Hinfer.
          try rewrite Hfree in Hinfer.
          try rewrite Henv2 in Hinfer.
          unfold roots_for_checked_result in Hinfer.
          rewrite Hfree in Hinfer.
          inversion Hinfer; subst; clear Hinfer.
          exists ret_roots.
          destruct Hsummary1_case as [Hsummary1 | [Htyped1 [Hsummary1 Hfree1]]].
          { eapply ERSSNC_LetInfer_CaptureRefFreeResult;
              eauto using roots_exclude_b_sound, root_env_excludes_b_sound. }
          { eapply ERSSNC_LetInfer_BoundCheckedCaptureRefFreeResult;
              eauto using roots_exclude_b_sound, root_env_excludes_b_sound. }
Qed.

Lemma check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel_exact_sound :
  forall fuel env fdef type_args,
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
      check_expr_root_shadow_store_safe_narrow_summary_fuel fuel env fdef
      type_args = true ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated
      env fdef type_args.
Proof.
  intros fuel env fdef type_args Hcheck.
  destruct fuel as [| fuel']; [simpl in Hcheck; discriminate |].
  cbn [check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel]
    in Hcheck.
  remember (subst_type_params_ctx type_args (fn_body_ctx fdef)) as body_ctx.
  remember (subst_type_params_expr type_args (fn_body fdef)) as body.
  remember (apply_type_params type_args (fn_params fdef)) as params.
  remember (global_env_with_local_bounds env
    (subst_type_params_trait_bounds type_args (fn_bounds fdef))) as body_env.
  destruct (infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef))
    as [[[[T_env Gamma_env] R_env] roots_env] | err_env] eqn:Henv;
    try discriminate.
  destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' body_env
    (fn_outlives fdef) (fn_lifetimes fdef) (initial_root_env_for_fn fdef)
    (sctx_of_ctx body_ctx) body)
    as [[[[T_body Sigma_out] R_body] roots_body] | err_body] eqn:Hbody;
    try discriminate.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[Hexpr Hcompat] Hroots] Hroot_env].
  subst body_ctx body params body_env.
  destruct (check_expr_root_shadow_store_safe_narrow_summary_fuel_sound
    fuel' (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
    (fn_outlives fdef) (fn_lifetimes fdef) (initial_root_env_for_fn fdef)
    (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
    (subst_type_params_expr type_args (fn_body fdef))
    T_body Sigma_out R_body roots_body Hbody Hexpr)
    as [ret_roots Hsummary].
  unfold callee_body_root_shadow_store_safe_narrow_summary_instantiated.
  exists T_body, (ctx_of_sctx Sigma_out), R_body, roots_body, ret_roots.
  repeat split.
  - rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    eapply infer_env_roots_shadow_safe_params_nodup. exact Henv.
  - unfold ctx_of_sctx, sctx_of_ctx in *. exact Hsummary.
  - exact Hcompat.
  - apply fn_params_roots_exclude_b_sound. exact Hroots.
  - apply fn_params_root_env_excludes_b_sound. exact Hroot_env.
Qed.

Lemma check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_sound :
  forall fuel env type_args,
    check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
      check_expr_root_shadow_store_safe_narrow_summary_fuel fuel env type_args = true ->
    forall fdef,
      In fdef (env_fns env) ->
      Datatypes.length type_args = fn_type_params fdef ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fdef type_args.
Proof.
  intros fuel env type_args Hall fdef Hin Harity.
  unfold check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel in Hall.
  rewrite forallb_forall in Hall.
  specialize (Hall fdef Hin).
  rewrite Harity in Hall.
  rewrite Nat.eqb_refl in Hall.
  eapply check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel_exact_sound.
  exact Hall.
Qed.

Lemma lookup_fn_in :
  forall fname fns fdef,
    lookup_fn fname fns = Some fdef ->
    In fdef fns.
Proof.
  intros fname fns.
  induction fns as [| f fns IH]; intros fdef Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (ident_eqb fname (fn_name f)) eqn:Hname.
    + inversion Hlookup; subst. left. reflexivity.
    + right. eapply IH. exact Hlookup.
Qed.

Lemma check_expr_root_shadow_store_safe_narrow_summary_checked_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe_checked env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_narrow_summary_checked
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_narrow_summary_checked,
    infer_core_env_roots_shadow_safe_checked.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe_checked 10000
    env Omega n R (sctx_of_ctx Gamma) e)
    as [[[[T0 Sigma0] R0] roots0] | err] eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_narrow_summary_checked_fuel_sound;
    eassumption.
Qed.

