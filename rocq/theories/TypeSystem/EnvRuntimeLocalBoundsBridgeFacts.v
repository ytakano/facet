From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeFunctionValueRuntimeFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition callee_body_root_shadow_store_safe_narrow_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists T_body Gamma_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_store_safe_narrow_summary env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma store_safe_function_value_call_arg_global_env_with_local_bounds :
  forall env bounds arg,
    store_safe_function_value_call_arg env arg ->
    store_safe_function_value_call_arg
      (global_env_with_local_bounds env bounds) arg.
Proof.
  intros env bounds arg Harg.
  destruct Harg as [| lit | x | fname fdef Hin Hname Hsummary | name lts tys sdef Hlookup Hbounds].
  - constructor.
  - constructor.
  - constructor.
  - eapply SSFVCArg_Fn.
    + exact Hin.
    + exact Hname.
    + apply callee_body_root_shadow_provenance_summary_global_env_with_local_bounds.
      exact Hsummary.
  - eapply SSFVCArg_EmptyStruct.
    + change (lookup_struct name (global_env_with_local_bounds env bounds))
        with (lookup_struct name env). exact Hlookup.
    + exact Hbounds.
Qed.

Lemma store_safe_function_value_call_args_global_env_with_local_bounds :
  forall env bounds args,
    store_safe_function_value_call_args env args ->
    store_safe_function_value_call_args
      (global_env_with_local_bounds env bounds) args.
Proof.
  intros env bounds args Hargs.
  induction Hargs.
  - constructor.
  - constructor.
    + eapply store_safe_function_value_call_arg_global_env_with_local_bounds.
      exact H.
    + exact IHHargs.
Qed.

Lemma typed_place_env_structural_pvar_global_env_with_local_bounds :
  forall env bounds Sigma x T,
    typed_place_env_structural env Sigma (PVar x) T ->
    typed_place_env_structural
      (global_env_with_local_bounds env bounds) Sigma (PVar x) T.
Proof.
  intros env bounds Sigma x T Hplace.
  inversion Hplace; subst.
  eapply TPES_Var; eassumption.
Qed.

Lemma typed_env_roots_shadow_safe_evar_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma x T Sigma' R' roots,
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (EVar x) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma x T Sigma' R' roots Htyped.
  dependent destruction Htyped.
  - eapply TERS_Var_Copy.
    + match goal with
      | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
          eapply typed_place_env_structural_pvar_global_env_with_local_bounds;
          exact Hplace
      end.
    + assumption.
    + assumption.
  - eapply TERS_Var_Move.
    + match goal with
      | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
          eapply typed_place_env_structural_pvar_global_env_with_local_bounds;
          exact Hplace
      end.
    + assumption.
    + assumption.
    + assumption.
Qed.

Lemma typed_env_roots_shadow_safe_efn_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma fname T Sigma' R' roots,
    typed_env_roots_shadow_safe env Omega n R Sigma (EFn fname) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (EFn fname) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma fname T Sigma' R' roots Htyped.
  dependent destruction Htyped.
  change (env_fns (global_env_with_local_bounds env bounds)) with (env_fns env).
  eapply TERS_Fn.
  - match goal with
    | Hin : In _ (env_fns env) |- _ => exact Hin
    end.
  - reflexivity.
  - match goal with
    | Hcaps : fn_captures _ = [] |- _ => exact Hcaps
    end.
Qed.

Lemma typed_env_roots_shadow_safe_store_safe_arg_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma arg T Sigma' R' roots,
    store_safe_function_value_call_arg env arg ->
    typed_env_roots_shadow_safe env Omega n R Sigma arg T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      arg T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma arg T Sigma' R' roots Hsafe Htyped.
  inversion Hsafe; subst.
  - dependent destruction Htyped. constructor.
  - dependent destruction Htyped; constructor.
  - eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds.
    exact Htyped.
  - eapply typed_env_roots_shadow_safe_efn_global_env_with_local_bounds.
    exact Htyped.
  - dependent destruction Htyped.
    match goal with
    | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ [] _ _ _ _ |- _ =>
        dependent destruction Hfields
    end.
    eapply TERS_Struct.
    + change (lookup_struct name (global_env_with_local_bounds env bounds))
        with (lookup_struct name env). exact H.
    + exact H0.
    + exact H1.
    + match goal with
      | Hlookup_typed : lookup_struct name env = Some sdef,
        Hlookup_safe : lookup_struct name env = Some ?sdef_safe,
        Hbounds_safe : struct_bounds ?sdef_safe = [] |- _ =>
          rewrite Hlookup_typed in Hlookup_safe;
          inversion Hlookup_safe; subst;
          rewrite Hbounds_safe; reflexivity
      end.
    + rewrite <- x. constructor.
Qed.

Lemma typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma args ps Sigma' R' roots,
    store_safe_function_value_call_args env args ->
    typed_args_roots_shadow_safe env Omega n R Sigma args ps Sigma' R' roots ->
    typed_args_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      args ps Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma args ps Sigma' R' roots Hsafe Htyped.
  revert bounds Hsafe.
  induction Htyped; intros bounds Hsafe.
  - constructor.
  - inversion Hsafe; subst.
    eapply TERSArgs_Cons.
    + eapply typed_env_roots_shadow_safe_store_safe_arg_global_env_with_local_bounds;
        eassumption.
    + exact H0.
    + apply IHHtyped. exact H4.
Qed.


Lemma typed_env_roots_store_safe_arg_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma arg T Sigma' R' roots,
    store_safe_function_value_call_arg env arg ->
    typed_env_roots env Omega n R Sigma arg T Sigma' R' roots ->
    typed_env_roots
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      arg T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma arg T Sigma' R' roots Hsafe Htyped.
  inversion Hsafe; subst.
  - dependent destruction Htyped. constructor.
  - dependent destruction Htyped; constructor.
  - dependent destruction Htyped.
    + eapply TER_Var_Copy.
      * eapply typed_place_env_structural_pvar_global_env_with_local_bounds;
          eassumption.
      * exact H0.
      * exact H1.
    + eapply TER_Var_Move.
      * eapply typed_place_env_structural_pvar_global_env_with_local_bounds;
          eassumption.
      * exact H0.
      * exact H1.
      * exact H2.
  - dependent destruction Htyped.
    change (env_fns (global_env_with_local_bounds env bounds))
      with (env_fns env).
    eapply TER_Fn; eassumption.
  - dependent destruction Htyped.
    match goal with
    | Hfields : typed_fields_roots _ _ _ _ _ _ _ [] _ _ _ _ |- _ =>
        dependent destruction Hfields
    end.
    eapply TER_Struct.
    + change (lookup_struct name (global_env_with_local_bounds env bounds))
        with (lookup_struct name env). exact H.
    + exact H0.
    + exact H1.
    + match goal with
      | Hlookup_typed : lookup_struct name env = Some sdef,
        Hlookup_safe : lookup_struct name env = Some ?sdef_safe,
        Hbounds_safe : struct_bounds ?sdef_safe = [] |- _ =>
          rewrite Hlookup_typed in Hlookup_safe;
          inversion Hlookup_safe; subst;
          rewrite Hbounds_safe; reflexivity
      end.
    + rewrite <- x. constructor.
Qed.

Lemma typed_args_roots_store_safe_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma args ps Sigma' R' roots,
    store_safe_function_value_call_args env args ->
    typed_args_roots env Omega n R Sigma args ps Sigma' R' roots ->
    typed_args_roots
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      args ps Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma args ps Sigma' R' roots Hsafe Htyped.
  revert bounds Hsafe.
  induction Htyped; intros bounds Hsafe.
  - constructor.
  - inversion Hsafe; subst.
    eapply TERArgs_Cons.
    + eapply typed_env_roots_store_safe_arg_global_env_with_local_bounds;
        eassumption.
    + exact H0.
    + apply IHHtyped. exact H4.
Qed.

Lemma typed_env_roots_shadow_safe_evar_ty_eq :
  forall env Omega n R Sigma x T1 Sigma1 R1 roots1 T2 Sigma2 R2 roots2,
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x) T1 Sigma1 R1 roots1 ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x) T2 Sigma2 R2 roots2 ->
    T1 = T2.
Proof.
  intros env Omega n R Sigma x T1 Sigma1 R1 roots1 T2 Sigma2 R2 roots2 H1 H2.
  inversion H1; subst; inversion H2; subst;
    match goal with
    | Hplace1 : typed_place_env_structural _ _ (PVar _) _,
      Hplace2 : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace1; subst; inversion Hplace2; subst;
        match goal with
        | Hlookup1 : sctx_lookup _ _ = Some (_, _),
          Hlookup2 : sctx_lookup _ _ = Some (_, _) |- _ =>
            rewrite Hlookup1 in Hlookup2; inversion Hlookup2; reflexivity
        end
    end.
Qed.

Lemma typed_env_roots_shadow_safe_evar_call_store_safe_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma x args T_callee Sigma_callee R_callee
      roots_callee T Sigma' R' roots,
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      T_callee Sigma_callee R_callee roots_callee ->
    supported_non_type_generic_function_value_call_callee_shape T_callee ->
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ECallExpr (EVar x) args) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (ECallExpr (EVar x) args) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma x args T_callee Sigma_callee R_callee
    roots_callee T Sigma' R' roots Hsafe Hcallee Hshape Hcall.
  dependent destruction Hcall.
  - eapply TERS_CallExpr_Fn.
    + exact H.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds;
        eassumption.
    + eapply typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds;
        eassumption.
  - assert (Heq :
        MkTy u (TClosure env_lt param_tys ret) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee. inversion Hshape; subst; simpl in *; discriminate.
  - assert (Heq :
        MkTy u (TTypeForall type_params bounds0 body_ty) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee. inversion Hshape; subst; simpl in *; discriminate.
  - assert (Heq :
        MkTy u
          (TForall m bounds0
            (MkTy u_body (TTypeForall type_params type_bounds body_ty))) =
        T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee.
    inversion Hshape as [T0 param_tys0 ret0 Hcore_shape
      | T0 m0 bounds_shape body_shape param_tys0 ret0 Hcore_shape Hbody_shape];
      subst.
    + simpl in Hcore_shape. discriminate.
    + simpl in Hcore_shape. inversion Hcore_shape; subst.
      simpl in Hbody_shape. discriminate.
  - eapply TERS_CallExpr_Forall_Fn.
    + exact H.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds;
        eassumption.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + eapply typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds;
        eassumption.
  - assert (Heq :
        MkTy u (TForall m bounds0 body_ty) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee.
    inversion Hshape as [T0 param_tys0 ret0 Hcore_shape
      | T0 m0 bounds_shape body_shape param_tys0 ret0 Hcore_shape Hbody_shape];
      subst.
    + simpl in Hcore_shape. discriminate.
    + simpl in Hcore_shape. inversion Hcore_shape; subst. congruence.
Qed.

Lemma typed_env_roots_shadow_safe_evar_call_generic_empty_type_bounds_store_safe_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma x type_args args T_callee Sigma_callee
      R_callee roots_callee T Sigma' R' roots,
    store_safe_function_value_call_args env args ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EVar x)
      T_callee Sigma_callee R_callee roots_callee ->
    supported_type_generic_function_value_call_callee_shape T_callee ->
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ECallExprGeneric (EVar x) type_args args) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (ECallExprGeneric (EVar x) type_args args) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma x type_args args T_callee Sigma_callee
    R_callee roots_callee T Sigma' R' roots Hsafe Hcallee Hshape Hcall.
  dependent destruction Hcall.
  - assert (Heq :
        MkTy u (TTypeForall type_params bounds0 body_ty) = T_callee)
      by (eapply typed_env_roots_shadow_safe_evar_ty_eq; eassumption).
    subst T_callee.
    inversion Hshape as [T0 type_params0 body0 param_tys0 ret0 Hcore_shape Hbody_shape];
      subst.
    simpl in Hcore_shape. inversion Hcore_shape; subst.
    eapply TERS_CallExprGeneric_TypeForall.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds;
        eassumption.
    + exact H.
    + reflexivity.
    + eapply typed_args_roots_shadow_safe_store_safe_global_env_with_local_bounds;
        eassumption.
Qed.


Lemma place_path_root_provenance_place_name :
  forall p x path,
    place_path p = Some (x, path) ->
    root_provenance_place_name p = x.
Proof.
  induction p; intros x path Hpath; simpl in Hpath.
  - inversion Hpath; reflexivity.
  - discriminate.
  - simpl. destruct (place_path p) as [[y ppath] |] eqn:Hp; try discriminate.
    inversion Hpath; subst x path. apply IHp with (path := ppath). reflexivity.
Qed.

Lemma typed_place_type_env_structural_global_env_with_local_bounds :
  forall env bounds Sigma p T,
    typed_place_type_env_structural env Sigma p T ->
    typed_place_type_env_structural
      (global_env_with_local_bounds env bounds) Sigma p T.
Proof.
  intros env bounds Sigma p T Htyped.
  induction Htyped.
  - eapply TPTES_Var; eassumption.
  - eapply TPTES_Deref; eassumption.
  - eapply TPTES_Field.
    + exact IHHtyped.
    + exact H.
    + change (lookup_struct sname (global_env_with_local_bounds env bounds))
        with (lookup_struct sname env). exact H0.
    + exact H1.
Qed.

Lemma typed_place_env_structural_global_env_with_local_bounds :
  forall env bounds Sigma p T,
    typed_place_env_structural env Sigma p T ->
    typed_place_env_structural
      (global_env_with_local_bounds env bounds) Sigma p T.
Proof.
  intros env bounds Sigma p T Htyped.
  induction Htyped.
  - eapply TPES_Var; eassumption.
  - eapply TPES_Deref; eassumption.
  - eapply TPES_Field.
    + eapply typed_place_type_env_structural_global_env_with_local_bounds.
      exact H.
    + exact H0.
    + change (lookup_struct sname (global_env_with_local_bounds env bounds))
        with (lookup_struct sname env). exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
  - eapply TPES_Field_Indirect.
    + eapply typed_place_type_env_structural_global_env_with_local_bounds.
      exact H.
    + exact H0.
    + change (lookup_struct sname (global_env_with_local_bounds env bounds))
        with (lookup_struct sname env). exact H1.
    + exact H2.
    + exact H3.
Qed.

Lemma writable_place_env_structural_global_env_with_local_bounds :
  forall env bounds Sigma p,
    writable_place_env_structural env Sigma p ->
    writable_place_env_structural
      (global_env_with_local_bounds env bounds) Sigma p.
Proof.
  intros env bounds Sigma p H.
  induction H.
  - eapply WPES_Var; eassumption.
  - eapply WPES_Deref.
    eapply typed_place_env_structural_global_env_with_local_bounds.
    exact H.
  - eapply WPES_Field.
    + exact IHwritable_place_env_structural.
    + eapply typed_place_type_env_structural_global_env_with_local_bounds.
      exact H0.
    + exact H1.
    + change (lookup_struct sname (global_env_with_local_bounds env bounds))
        with (lookup_struct sname env). exact H2.
    + exact H3.
    + exact H4.
Qed.

Lemma place_resolved_write_writable_chain_global_env_with_local_bounds :
  forall env bounds R Sigma p,
    place_resolved_write_writable_chain env R Sigma p ->
    place_resolved_write_writable_chain
      (global_env_with_local_bounds env bounds) R Sigma p.
Proof.
  intros env bounds R Sigma p H.
  induction H.
  - apply PRWWC_Direct. exact H.
  - eapply PRWWC_Deref.
    + exact IHplace_resolved_write_writable_chain.
    + eapply writable_place_env_structural_global_env_with_local_bounds.
      exact H0.
    + exact H1.
    + exact H2.
Qed.

Lemma place_under_unique_ref_structural_global_env_with_local_bounds :
  forall env bounds Sigma p,
    place_under_unique_ref_structural env Sigma p ->
    place_under_unique_ref_structural
      (global_env_with_local_bounds env bounds) Sigma p.
Proof.
  intros env bounds Sigma p H.
  induction H.
  - eapply PUURS_Deref.
    eapply typed_place_env_structural_global_env_with_local_bounds.
    exact H.
  - eapply PUURS_Field.
    exact IHplace_under_unique_ref_structural.
Qed.

Lemma typed_env_roots_shadow_safe_lit_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma lit T Sigma' R' roots,
    typed_env_roots_shadow_safe env Omega n R Sigma (ELit lit) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (ELit lit) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma lit T Sigma' R' roots H.
  inversion H; subst; try congruence; constructor.
Qed.

Lemma typed_env_roots_shadow_safe_call_generic_empty_no_bounds_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma fname type_args T Sigma' R' roots fcallee,
    fn_env_unique_by_name env ->
    In fcallee (env_fns env) ->
    fn_name fcallee = fname ->
    fn_bounds fcallee = [] ->
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ECallGeneric fname type_args []) T Sigma' R' roots ->
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env bounds) Omega n R Sigma
      (ECallGeneric fname type_args []) T Sigma' R' roots.
Proof.
  intros env bounds Omega n R Sigma fname type_args T Sigma' R' roots fcallee
    Hunique Hin_callee Hname_callee Hbounds_callee Htyped.
  destruct (typed_env_roots_shadow_safe_call_generic_typed_args_roots
    _ _ _ _ _ _ _ _ _ _ _ _ Htyped)
    as (fdef & sigma & arg_roots & Hin & Hname & Hcaps & Harity & Hbounds &
        Hargs & Houtlives & Hret & Hroots).
  assert (Heq_fdef : fdef = fcallee).
  { eapply Hunique.
    - exact Hin.
    - exact Hin_callee.
    - rewrite Hname. symmetry. exact Hname_callee. }
  subst fdef T roots.
  eapply TERS_CallGeneric.
  - change (env_fns (global_env_with_local_bounds env bounds)) with (env_fns env).
    exact Hin_callee.
  - exact Hname_callee.
  - exact Hcaps.
  - exact Harity.
  - rewrite Hbounds_callee. reflexivity.
  - dependent destruction Hargs. rewrite <- x. constructor.
  - exact Houtlives.
Qed.

Lemma params_ok_sctx_b_global_env_with_local_bounds :
  forall env bounds ps Sigma,
    params_ok_sctx_b (global_env_with_local_bounds env bounds) ps Sigma =
    params_ok_sctx_b env ps Sigma.
Proof.
  intros env bounds ps.
  induction ps as [| p ps IH]; intros Sigma.
  - reflexivity.
  - simpl. rewrite sctx_check_ok_global_env_with_local_bounds.
    rewrite IH. reflexivity.
Qed.

Lemma params_ok_env_b_global_env_with_local_bounds :
  forall env bounds ps Gamma,
    params_ok_env_b (global_env_with_local_bounds env bounds) ps Gamma =
    params_ok_env_b env ps Gamma.
Proof.
  intros env bounds ps Gamma.
  unfold params_ok_env_b.
  apply params_ok_sctx_b_global_env_with_local_bounds.
Qed.

Lemma infer_env_roots_shadow_safe_global_env_with_local_bounds :
  forall env bounds f R0,
    infer_env_roots_shadow_safe (global_env_with_local_bounds env bounds) f R0 =
    infer_env_roots_shadow_safe env f R0.
Proof.
  intros env bounds f R0.
  unfold infer_env_roots_shadow_safe.
  change (global_env_with_local_bounds
    (global_env_with_local_bounds env bounds) (fn_bounds f))
    with (global_env_with_local_bounds env (fn_bounds f)).
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f))
    (fn_outlives f))); try reflexivity.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try reflexivity.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try reflexivity.
  destruct (infer_core_env_roots_shadow_safe
    (global_env_with_local_bounds env (fn_bounds f)) (fn_outlives f)
    (fn_lifetimes f) R0 (fn_body_ctx f) (fn_body f))
    as [[[[T_body Gamma_out] R_out] roots] | err]; try reflexivity.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try reflexivity.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f));
    try reflexivity.
  rewrite params_ok_env_b_global_env_with_local_bounds.
  reflexivity.
Qed.

Lemma check_fn_root_shadow_provenance_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    check_fn_root_shadow_provenance_summary
      (global_env_with_local_bounds env bounds) fdef =
    check_fn_root_shadow_provenance_summary env fdef.
Proof.
  intros env bounds fdef.
  unfold check_fn_root_shadow_provenance_summary.
  rewrite infer_env_roots_shadow_safe_global_env_with_local_bounds.
  reflexivity.
Qed.

Lemma store_safe_function_value_call_args_b_global_env_with_local_bounds :
  forall env bounds args,
    store_safe_function_value_call_args_b
      (global_env_with_local_bounds env bounds) args =
    store_safe_function_value_call_args_b env args.
Proof.
  intros env bounds args.
  induction args as [| arg rest IH]; simpl; try reflexivity.
  destruct arg; try exact IH; try reflexivity.
  change (env_fns (global_env_with_local_bounds env bounds))
    with (env_fns env).
  destruct (lookup_fn_b i (env_fns env)); try reflexivity.
  rewrite check_fn_root_shadow_provenance_summary_global_env_with_local_bounds.
  rewrite IH. reflexivity.
  + destruct l1 as [| field fields]; try reflexivity.
  change (lookup_struct s (global_env_with_local_bounds env bounds))
    with (lookup_struct s env).
  destruct (lookup_struct s env) as [sdef |]; try reflexivity.
  destruct (struct_bounds sdef); try reflexivity.
  rewrite capture_ref_free_ty_b_global_env_with_local_bounds.
  rewrite IH. reflexivity.
Qed.

Lemma check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel_global_env_with_local_bounds :
  forall check_expr fuel env bounds fdef type_args,
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
      check_expr fuel (global_env_with_local_bounds env bounds) fdef
      type_args =
    check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
      check_expr fuel env fdef type_args.
Proof.
  intros check_expr fuel env bounds fdef type_args.
  destruct fuel as [| fuel']; [reflexivity |].
  cbn [check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel].
  rewrite infer_env_roots_shadow_safe_global_env_with_local_bounds.
  change (global_env_with_local_bounds
    (global_env_with_local_bounds env bounds)
      (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
    with (global_env_with_local_bounds env
      (subst_type_params_trait_bounds type_args (fn_bounds fdef))).
  reflexivity.
Qed.

Lemma check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds :
  forall check_expr fuel env bounds type_args,
    check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
      check_expr fuel (global_env_with_local_bounds env bounds) type_args =
    check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
      check_expr fuel env type_args.
Proof.
  intros check_expr fuel env bounds type_args.
  unfold check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel.
  change (env_fns (global_env_with_local_bounds env bounds)) with (env_fns env).
  induction (env_fns env) as [| fdef fns IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)).
    + rewrite check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel_global_env_with_local_bounds.
      rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds :
  forall env bounds Omega n R Sigma e T Sigma' R' roots ret_roots,
    fn_env_unique_by_name env ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Sigma e T Sigma' R' roots ret_roots ->
    expr_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env bounds)
      Omega n R Sigma e T Sigma' R' roots ret_roots.
Proof.
  intros env bounds Omega n R Sigma e T Sigma' R' roots ret_roots Hunique Hsummary.
  induction Hsummary.
  - eapply ERSSN_FunctionValueCall.
    + eapply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact H.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds.
      exact H0.
    + exact H1.
    + eapply typed_env_roots_shadow_safe_evar_call_store_safe_global_env_with_local_bounds;
        eassumption.
  - eapply ERSSN_TypeGenericFunctionValueCall.
    + eapply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact H.
    + exact H0.
    + exact H1.
    + rewrite check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
      exact H2.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds.
      exact H3.
    + exact H4.
    + exact H5.
    + eapply typed_env_roots_shadow_safe_evar_call_generic_empty_type_bounds_store_safe_global_env_with_local_bounds;
        eassumption.
  - eapply ERSSN_Let.
    + exact IHHsummary1.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact IHHsummary2.
    + rewrite sctx_check_ok_global_env_with_local_bounds. exact H4.
    + exact H5.
    + exact H6.
  - eapply ERSSN_LetInfer.
    + exact IHHsummary1.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact IHHsummary2.
    + rewrite sctx_check_ok_global_env_with_local_bounds. exact H3.
    + exact H4.
    + exact H5.
  - inversion H; subst; try congruence.
    + eapply ERSSN_BorrowDirect.
      * eapply TERS_BorrowShared.
        eapply typed_place_env_structural_global_env_with_local_bounds.
        eassumption.
      * exact H0.
      * exact H1.
    + eapply ERSSN_BorrowDirect.
      * eapply TERS_BorrowUnique.
        -- eapply typed_place_env_structural_global_env_with_local_bounds.
           eassumption.
        -- exact H7.
        -- exact H12.
      * exact H0.
      * exact H1.
  - eapply ERSSN_BorrowUniqueResolvedWritableChain.
    + inversion H; subst; try congruence.
      * eapply TERS_BorrowUnique_Indirect; try eassumption.
        -- eapply typed_place_env_structural_global_env_with_local_bounds.
           eassumption.
        -- eapply place_under_unique_ref_structural_global_env_with_local_bounds.
           eassumption.
      * eapply TERS_BorrowUnique_Resolved; try eassumption.
        -- eapply typed_place_env_structural_global_env_with_local_bounds.
           eassumption.
        -- eapply place_under_unique_ref_structural_global_env_with_local_bounds.
           eassumption.
      * eapply TERS_BorrowUnique_ResolvedTarget; try eassumption.
        -- eapply typed_place_env_structural_global_env_with_local_bounds.
           eassumption.
        -- eapply place_under_unique_ref_structural_global_env_with_local_bounds.
           eassumption.
        -- eapply place_resolved_write_writable_chain_global_env_with_local_bounds.
           eassumption.
    + exact H0.
    + eapply place_resolved_write_writable_chain_global_env_with_local_bounds.
      exact H1.
    + exact H2.
    + exact H3.
  - apply ERSSN_Unit.
    inversion H; subst; try congruence.
    constructor.
  - eapply ERSSN_EmptyStructRootless.
    + change (lookup_struct name (global_env_with_local_bounds env bounds))
        with (lookup_struct name env). exact H.
    + exact H0.
    + inversion H1; subst; try congruence.
      match goal with
      | Hlookup : lookup_struct name env = Some ?sdef0 |- _ =>
          rewrite H in Hlookup; inversion Hlookup; subst sdef0
      end.
      match goal with
      | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          dependent destruction Hfields
      end.
      eapply TERS_Struct.
      * change (lookup_struct name (global_env_with_local_bounds env bounds))
          with (lookup_struct name env). exact H.
      * eassumption.
      * eassumption.
      * rewrite H0. reflexivity.
      * rewrite <- x. constructor.
    + rewrite capture_ref_free_ty_b_global_env_with_local_bounds.
      exact H2.
  - eapply ERSSN_AssignLit.
    inversion H; subst; try congruence.
    + eapply TERS_Assign_Path; eauto using
        typed_place_env_structural_global_env_with_local_bounds,
        writable_place_env_structural_global_env_with_local_bounds,
        typed_env_roots_shadow_safe_lit_global_env_with_local_bounds.
    + eapply TERS_Assign_Resolved; eauto using
        typed_place_env_structural_global_env_with_local_bounds,
        writable_place_env_structural_global_env_with_local_bounds,
        place_resolved_write_writable_chain_global_env_with_local_bounds,
        typed_env_roots_shadow_safe_lit_global_env_with_local_bounds.
  - eapply ERSSN_AssignGenericDirect.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + exact H6.
    + exact IHHsummary.
    + exact H7.
    + exact H8.
    + exact H9.
    + pose proof H as Hin_summary_callee.
      pose proof H0 as Hname_summary_callee.
      pose proof H2 as Hbounds_summary_callee.
      inversion H10; subst; simpl in *; try congruence.
      * eapply TERS_Assign_Path.
        -- eapply typed_place_env_structural_global_env_with_local_bounds;
             eassumption.
        -- eassumption.
        -- eassumption.
        -- eapply writable_place_env_structural_global_env_with_local_bounds;
             eassumption.
        -- eapply typed_env_roots_shadow_safe_call_generic_empty_no_bounds_global_env_with_local_bounds
             with (env := env) (bounds := bounds) (fcallee := fcallee).
           ++ exact Hunique.
           ++ exact Hin_summary_callee.
           ++ exact Hname_summary_callee.
           ++ exact Hbounds_summary_callee.
           ++ eassumption.
        -- eassumption.
        -- eassumption.
        -- eassumption.
  - eapply ERSSN_VarNonFunction.
    + eapply typed_env_roots_shadow_safe_evar_global_env_with_local_bounds.
      exact H.
    + exact H0.
  - eapply ERSSN_DropPlaceDirect.
    + inversion H; subst; try congruence.
      eapply TERS_Drop.
      inversion H4; subst; try congruence.
      * eapply TERS_Place_Copy; eauto using
          typed_place_env_structural_global_env_with_local_bounds.
      * eapply TERS_Place_Move; eauto using
          typed_place_env_structural_global_env_with_local_bounds.
    + exact H0.
Qed.

Lemma callee_body_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_store_safe_narrow_summary env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef Hunique Hsummary.
  unfold callee_body_root_shadow_store_safe_narrow_summary in *.
  destruct Hsummary as
    (T_body & Gamma_out & R_body & roots_body & ret_roots &
      Hnodup & Hexpr & Hcompat & Hroots & Henv).
  exists T_body, Gamma_out, R_body, roots_body, ret_roots.
  repeat split; try assumption.
  apply expr_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds.
  - exact Hunique.
  - exact Hexpr.
Qed.


Lemma eval_args_root_tail_fresh_names_for_fresh_call_prefix_ctx :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_sctx_keys_named R Σ ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_env_tail_fresh_names (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hctx_roots Hctx_keys Htyped_args Hrename x Hin.
  destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Htyped_args)
    as [Hstore_args [_ [_ [_ [_ [_ Hrn_args]]]]]].
  destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Ω n))
              R Σ args ps_typed Σ_args R_args arg_roots Htyped_args Hrn
              Hctx_roots)
    as [Hctx_roots_args _].
  pose proof (proj1 (proj2 (typed_roots_ctx_keys_named_mutual env Ω n))
                R Σ args ps_typed Σ_args R_args arg_roots Htyped_args Hrn
                Hctx_keys) as Hctx_keys_args.
  assert (Harg_roots_named : root_env_store_roots_named R_args s_args).
  { eapply root_env_ctx_roots_named_store_typed_prefix; eassumption. }
  assert (Harg_keys_named : root_env_store_keys_named R_args s_args).
  { eapply root_env_ctx_keys_named_store_typed_prefix; eassumption. }
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names s_args) fdef fcall used' Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes.
    + eapply typed_args_roots_no_shadow; eassumption.
    + exact Hexcl.
Qed.


Lemma eval_args_root_tail_fresh_names_for_fresh_call_prefix_named :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    store_safe_function_value_call_args env args ->
    eval_args env s args s_args vs ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_env_tail_fresh_names (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Hsafe_args Heval_args Htyped_args Hrn Hnamed Hkeys
    Hrename x Hin.
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args ps_typed Σ_args R_args arg_roots
              s s_args vs Hsafe_args Htyped_args Heval_args Hnamed Hkeys)
    as [Hnamed_args [_ Hkeys_args]].
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names s_args) fdef fcall used' Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes.
    + eapply typed_args_roots_no_shadow; eassumption.
    + exact Hexcl.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_ctx :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_ctx_roots_named R Sigma ->
      root_env_sctx_keys_named R Sigma ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hctx_roots Hctx_keys
    Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Gamma_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply ctx_alpha_nodup_names; eassumption.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
              env s args s_args vs Heval_args Omega n R Sigma
              (params_of_tys param_tys) Sigma_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
      as [Hstore_args _].
    destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Omega n))
              R Sigma args (params_of_tys param_tys) Sigma_args R_args
              arg_roots Htyped_args Hrn Hctx_roots)
      as [_ Harg_roots_ctx_named].
    eapply Forall_impl; [| exact Harg_roots_ctx_named].
    intros roots_i Hctx_named_i.
    eapply root_set_ctx_roots_named_store_typed_prefix.
    - exact Hstore_args.
    - exact Hctx_named_i. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call_prefix_ctx;
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - assert (Hstore_args : store_typed_prefix env s_args Sigma_args).
      { destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
                  env s args s_args vs Heval_args Omega n R Sigma
                  (params_of_tys param_tys) Sigma_args R_args arg_roots
                  Hprov_args Hstore Hroots Hshadow Hrn Htyped_args)
          as [Hstore_args _].
        exact Hstore_args. }
      assert (Hctx_roots_args : root_env_ctx_roots_named R_args Sigma_args).
      { destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Omega n))
                  R Sigma args (params_of_tys param_tys) Sigma_args R_args
                  arg_roots Htyped_args Hrn Hctx_roots)
          as [Hctx_roots_args _].
        exact Hctx_roots_args. }
      assert (Hnamed_args : root_env_store_roots_named R_args s_args).
      { eapply root_env_ctx_roots_named_store_typed_prefix; eassumption. }
      eapply root_env_store_roots_named_excludes_params; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite Hbounds;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.


Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args fdef fcall
    param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Hsafe_args Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Gamma_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq [Hret [_ Hbounds]]]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Gamma_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Gamma_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Gamma_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Gamma_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { pose proof (typed_args_roots_arg_roots_length
                  env Omega n R Sigma args (params_of_tys param_tys)
                  Sigma_args R_args arg_roots Htyped_args) as Hlen_args.
    rewrite params_of_tys_length in Hlen_args.
    pose proof
      (runtime_tfn_signature_bridge_params_length
        (map param_ty (fn_params fdef)) (fn_ret fdef) param_tys ret_ty
        Hbridge) as Hlen_bridge.
    rewrite length_map in Hlen_bridge.
    rewrite Hlen_args. symmetry. exact Hlen_bridge. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Omega n R Sigma args (params_of_tys param_tys) Sigma_args
              R_args arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys) as [_ [Harg_roots_named _]].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              (global_env_with_local_bounds env (fn_bounds fdef))
              (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Gamma_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call_prefix_named;
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Gamma_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - destruct (store_safe_function_value_call_args_typed_roots_store_named
                  env Omega n R Sigma args (params_of_tys param_tys) Sigma_args
                  R_args arg_roots s s_args vs Hsafe_args Htyped_args
                  Heval_args Hnamed Hkeys) as [Hnamed_args _].
      eapply root_env_store_roots_named_excludes_params; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply typed_env_roots_shadow_safe_root_set_no_store_of_excludes_params;
      eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply typed_env_roots_shadow_safe_instantiated_roots_subset_union;
      eassumption. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Gamma_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite Hbounds;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.




Lemma callee_body_root_shadow_provenance_summary_fn_subst_type_params :
  forall env fdef type_args,
    callee_body_root_shadow_provenance_summary env fdef ->
    provenance_ready_expr (subst_type_params_expr type_args (fn_body fdef)) ->
    (forall T_body Gamma_out R_body roots_body,
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (sctx_of_ctx (fn_body_ctx fdef))
        (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists T_body_subst Gamma_out_subst,
        typed_env_roots_shadow_safe
          (global_env_with_local_bounds env
            (subst_type_params_trait_bounds type_args (fn_bounds fdef)))
          (fn_outlives fdef) (fn_lifetimes fdef)
          (initial_root_env_for_fn fdef)
          (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fdef)))
          (subst_type_params_expr type_args (fn_body fdef))
          T_body_subst (sctx_of_ctx Gamma_out_subst) R_body roots_body /\
        ty_compatible_b (fn_outlives fdef) T_body_subst
          (subst_type_params_ty type_args (fn_ret fdef)) = true) ->
    callee_body_root_shadow_provenance_summary env
      (fn_subst_type_params type_args fdef).
Proof.
  intros env fdef type_args Hsummary Hprov_subst Htransport.
  unfold callee_body_root_shadow_provenance_summary in *.
  destruct Hsummary as [Hnodup Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as (T_body & Gamma_out & R_body & roots_body &
    Hprov & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
  destruct (Htransport T_body Gamma_out R_body roots_body Htyped)
    as (T_body_subst & Gamma_out_subst & Htyped_subst & Hcompat_subst).
  split.
  - unfold fn_subst_type_params. simpl.
    rewrite params_ctx_apply_type_params.
    rewrite ctx_names_subst_type_params_ctx.
    exact Hnodup.
  - unfold callee_body_root_shadow_provenance_ready_at.
    exists T_body_subst, Gamma_out_subst, R_body, roots_body.
    repeat split; try assumption.
    + rewrite initial_root_env_for_fn_fn_subst_type_params.
      rewrite fn_body_ctx_fn_subst_type_params.
      simpl. exact Htyped_subst.
    + simpl. apply roots_exclude_params_apply_type_params. exact Hexcl_roots.
    + simpl. apply root_env_excludes_params_apply_type_params. exact Hexcl_env.
Qed.


Lemma generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_subst_summary_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args type_args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env
        (fn_subst_type_params type_args fdef) ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (apply_type_params type_args (fn_params fdef)))
        (subst_type_params_ty type_args (fn_ret fdef)) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env
        (fn_subst_type_params type_args fcall)
        (call_param_root_env
          (apply_type_params type_args (fn_params fcall)) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args type_args
    fdef fcall param_tys ret_ty s s_args vs used' Hsummary Hcaps Hbridge
    Hsafe_args Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename.
  set (fdefT := fn_subst_type_params type_args fdef).
  set (fcallT := fn_subst_type_params type_args fcall).
  assert (HcapsT : fn_captures fdefT = []).
  { subst fdefT. simpl. rewrite Hcaps. reflexivity. }
  assert (HrenameT :
    alpha_rename_fn_def (store_names s_args) fdefT = (fcallT, used')).
  { subst fdefT fcallT.
    apply alpha_rename_fn_def_subst_type_params. exact Hrename. }
  subst fdefT fcallT.
  eapply direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset_prefix_named;
    eassumption.
Qed.

Lemma generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_instantiated_narrow_tfn_with_result_subset_prefix_named :
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots args type_args fdef fcall param_tys ret_ty s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      callee_body_root_shadow_store_safe_narrow_summary_instantiated
        env fdef type_args ->
      fn_captures fdef = [] ->
      runtime_tfn_signature_bridge
        (map param_ty (apply_type_params type_args (fn_params fdef)))
        (subst_type_params_ty type_args (fn_ret fdef)) param_tys ret_ty ->
      store_safe_function_value_call_args env args ->
      typed_args_roots env Omega n R Sigma args
        (params_of_tys param_tys) Sigma_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed_prefix env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env
        (fn_subst_type_params type_args fcall)
        (call_param_root_env
          (apply_type_params type_args (fn_params fcall)) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Omega n R Sigma Sigma_args R_args arg_roots args type_args
    fdef fcall param_tys ret_ty s s_args vs used' Hsummary Hnarrow Hcaps
    Hbridge Hsafe_args Htyped_args Heval_args Hprov_args Hstore Hroots
    Hshadow Hrn Hnamed Hkeys Hrename.
  assert (Hsummary_subst :
      callee_body_root_shadow_provenance_summary env
        (fn_subst_type_params type_args fdef)).
  { eapply callee_body_root_shadow_provenance_summary_fn_subst_type_params_of_instantiated_narrow;
      eassumption. }
  eapply generic_direct_call_callee_body_root_shadow_provenance_summary_bridge_of_subst_summary_tfn_with_result_subset_prefix_named;
    eassumption.
Qed.


