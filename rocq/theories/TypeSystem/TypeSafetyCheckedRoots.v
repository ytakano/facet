From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRoots TypeSafetyRootFacts TypeSafetyRootedPackages
  TypeSafetyProvenanceReady TypeSafetyRootsReadyMutual.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition provenance_ready_leaf_expr (e : expr) : Prop :=
  (exists x, e = EVar x) \/
  e = EUnit \/
  (exists lit, e = ELit lit) \/
  (exists p, e = EPlace p) \/
  (exists rk p, e = EBorrow rk p) \/
  (exists p, e = EDrop (EPlace p)) \/
  (exists rk p, e = EDeref (EBorrow rk p)).

Lemma provenance_ready_args_In :
  forall args e,
    provenance_ready_args args ->
    In e args ->
    provenance_ready_expr e.
Proof.
  intros args e Hready Hin.
  induction Hready as [| e_hd rest Hready_hd _ IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. exact Hready_hd.
    + apply IH. exact Hin.
Qed.

Lemma provenance_ready_fields_lookup_b :
  forall fields name e,
    provenance_ready_fields fields ->
    lookup_field_b name fields = Some e ->
    provenance_ready_expr e.
Proof.
  intros fields name e Hready Hlookup.
  apply (provenance_ready_fields_lookup fields name e Hready).
  rewrite <- lookup_field_b_lookup_expr_field. exact Hlookup.
Qed.

Lemma lookup_field_b_subst_type_params_fields :
  forall type_args fields name e,
    lookup_field_b name fields = Some e ->
    lookup_field_b name
      (map (fun '(field_name, field_expr) =>
        (field_name, subst_type_params_expr type_args field_expr)) fields) =
      Some (subst_type_params_expr type_args e).
Proof.
  intros type_args fields name e Hlookup.
  induction fields as [| [field_name field_expr] rest IH]; simpl in *.
  - discriminate.
  - destruct (String.eqb name field_name) eqn:Hname.
    + inversion Hlookup; subst. reflexivity.
    + apply IH. exact Hlookup.
Qed.

Lemma typed_env_roots_shadow_safe_provenance_ready_leaf_subst_type_params_compat_package :
  forall env Omega n R Sigma e T Sigma' R' roots type_args,
    provenance_ready_expr e ->
    typed_env_roots_shadow_safe env Omega n R Sigma e T Sigma' R' roots ->
    (exists x, e = EVar x) \/
    e = EUnit \/
    (exists lit, e = ELit lit) \/
    (exists p, e = EPlace p) \/
    (exists rk p, e = EBorrow rk p) \/
    (exists p, e = EDrop (EPlace p)) \/
    (exists rk p, e = EDeref (EBorrow rk p)) ->
    (forall T0, ty_compatible_b Omega T0 T0 = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args e)
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args T) = true.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots type_args
    _ Htyped Hleaf Hcompat_refl.
  pose proof
    (typed_env_roots_shadow_safe_leaf_subst_type_params_ctx
      env Omega n R Sigma e T Sigma' R' roots type_args Htyped Hleaf)
    as Htyped_subst.
  exists (subst_type_params_ty type_args T),
    (subst_type_params_ctx type_args Sigma').
  split.
  - change (subst_type_params_ctx type_args Sigma') with
      (sctx_of_ctx (subst_type_params_ctx type_args Sigma')).
    exact Htyped_subst.
  - apply Hcompat_refl.
Qed.

Lemma typed_env_roots_shadow_safe_efn_subst_type_params_compat_package :
  forall env Omega n R Sigma fname T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma (EFn fname)
      T Sigma' R' roots ->
    (forall fdef,
        In fdef (Program.env_fns env) ->
        fn_name fdef = fname ->
        fn_captures fdef = [] ->
        ty_compatible_b Omega (fn_value_ty fdef)
          (subst_type_params_ty type_args (fn_value_ty fdef)) = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (EFn fname))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args T) = true.
Proof.
  intros env Omega n R Sigma fname T Sigma' R' roots type_args
    Htyped Hcompat_result.
  inversion Htyped; subst; try discriminate.
  match goal with
  | |- exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe _ _ _ _ ?Sigma_sub _ _ _ _ _ /\ _ =>
      exists (fn_value_ty fdef), Sigma_sub
  end.
  split.
  - simpl. eapply TERS_Fn; eauto.
  - eapply Hcompat_result; eauto.
Qed.

Lemma typed_args_roots_shadow_safe_provenance_ready_leaf_subst_type_params_package :
  forall env Omega n R Sigma args param_tys Sigma' R' roots type_args,
    provenance_ready_args args ->
    typed_args_roots_shadow_safe env Omega n R Sigma args
      (params_of_tys param_tys) Sigma' R' roots ->
    Forall provenance_ready_leaf_expr args ->
    (forall T_actual T_expected,
        ty_compatible_b Omega T_actual T_expected = true ->
        ty_compatible_b Omega (subst_type_params_ty type_args T_actual)
          (subst_type_params_ty type_args T_expected) = true) ->
    typed_args_roots_shadow_safe env Omega n R
      (subst_type_params_ctx type_args Sigma)
      (map (subst_type_params_expr type_args) args)
      (params_of_tys (map (subst_type_params_ty type_args) param_tys))
      (subst_type_params_ctx type_args Sigma') R' roots.
Proof.
  intros env Omega n R Sigma args param_tys Sigma' R' roots type_args
    Hready Htyped Hleaf Hcompat_subst.
  eapply typed_args_roots_shadow_safe_subst_type_params_expr_params_of_tys.
  - exact Htyped.
  - intros R0 Sigma0 e T0 Sigma0' R0' roots0 Hin Htyped_e.
    eapply typed_env_roots_shadow_safe_leaf_subst_type_params_ctx.
    + exact Htyped_e.
    + eapply Forall_forall in Hleaf; eauto.
  - exact Hcompat_subst.
Qed.

Lemma typed_fields_roots_shadow_safe_provenance_ready_leaf_subst_type_params_package :
  forall env Omega n lts struct_type_args R Sigma fields defs Sigma' R'
      roots type_args,
    provenance_ready_fields fields ->
    typed_fields_roots_shadow_safe env Omega n lts struct_type_args R Sigma
      fields defs Sigma' R' roots ->
    (forall name e,
        lookup_field_b name fields = Some e ->
        provenance_ready_leaf_expr e) ->
    (forall T_actual T_expected,
        ty_compatible_b Omega T_actual T_expected = true ->
        ty_compatible_b Omega (subst_type_params_ty type_args T_actual)
          (subst_type_params_ty type_args T_expected) = true) ->
    compose_type_params type_args struct_type_args =
      map (subst_type_params_ty type_args) struct_type_args ->
    typed_fields_roots_shadow_safe env Omega n lts
      (map (subst_type_params_ty type_args) struct_type_args) R
      (subst_type_params_ctx type_args Sigma)
      (map (fun '(field_name, field_expr) =>
        (field_name, subst_type_params_expr type_args field_expr)) fields)
      defs (subst_type_params_ctx type_args Sigma') R' roots.
Proof.
  intros env Omega n lts struct_type_args R Sigma fields defs Sigma' R'
    roots type_args Hready Htyped.
  induction Htyped as
    [lts0 args0 R0 Sigma0 fields0
    |lts0 args0 R0 R1 R2 Sigma0 Sigma1 Sigma2 fields0 f rest
      e_field T_field roots_field roots_rest Hlookup Htyped_field Hcompat
      Htyped_rest IH];
    intros Hleaf_lookup Hcompat_subst Hcompose; simpl.
  - constructor.
  - eapply TERSFields_Cons.
    + eapply lookup_field_b_subst_type_params_fields. exact Hlookup.
    + eapply typed_env_roots_shadow_safe_leaf_subst_type_params_ctx.
      * exact Htyped_field.
      * apply Hleaf_lookup with (name := field_name f). exact Hlookup.
    + rewrite <- Hcompose.
      rewrite <- instantiate_struct_field_ty_type_subst_compose.
      apply Hcompat_subst. exact Hcompat.
    + eapply IH; eauto.
Qed.

Lemma typed_env_roots_shadow_safe_struct_provenance_ready_leaf_subst_type_params_package :
  forall env Omega n R Sigma sname lts struct_type_args fields
      sdef Sigma' R' roots type_args,
    provenance_ready_fields fields ->
    Program.lookup_struct sname env = Some sdef ->
    Datatypes.length lts = Program.struct_lifetimes sdef ->
    Datatypes.length struct_type_args = Program.struct_type_params sdef ->
    check_struct_bounds env (Program.struct_bounds sdef) struct_type_args = None ->
    check_struct_bounds env (Program.struct_bounds sdef)
      (map (subst_type_params_ty type_args) struct_type_args) = None ->
    typed_fields_roots_shadow_safe env Omega n lts struct_type_args R Sigma
      fields (Program.struct_fields sdef) Sigma' R' roots ->
    (forall name e,
        lookup_field_b name fields = Some e ->
        provenance_ready_leaf_expr e) ->
    (forall T_actual T_expected,
        ty_compatible_b Omega T_actual T_expected = true ->
        ty_compatible_b Omega (subst_type_params_ty type_args T_actual)
          (subst_type_params_ty type_args T_expected) = true) ->
    ty_compatible_b Omega
      (instantiate_struct_instance_ty sdef lts
        (map (subst_type_params_ty type_args) struct_type_args))
      (subst_type_params_ty type_args
        (instantiate_struct_instance_ty sdef lts struct_type_args)) = true ->
    compose_type_params type_args struct_type_args =
      map (subst_type_params_ty type_args) struct_type_args ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args
          (EStruct sname lts struct_type_args fields))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args
          (instantiate_struct_instance_ty sdef lts struct_type_args)) = true.
Proof.
  intros env Omega n R Sigma sname lts struct_type_args fields
    sdef Sigma' R' roots type_args Hready Hlookup Hlen_lts Hlen_args
    _ Hbounds_subst Htyped_fields Hleaf_lookup Hcompat_subst Hcompat_result
    Hcompose.
  exists (instantiate_struct_instance_ty sdef lts
      (map (subst_type_params_ty type_args) struct_type_args)),
    (subst_type_params_ctx type_args Sigma').
  split.
  - simpl.
    rewrite subst_type_params_fields_go_map.
    eapply TERS_Struct; eauto.
    + rewrite length_map. exact Hlen_args.
    + change (sctx_of_ctx (subst_type_params_ctx type_args Sigma')) with
        (subst_type_params_ctx type_args Sigma').
      eapply typed_fields_roots_shadow_safe_provenance_ready_leaf_subst_type_params_package;
        eauto.
  - exact Hcompat_result.
Qed.

Lemma typed_env_roots_shadow_safe_enum_provenance_ready_leaf_subst_type_params_package :
  forall env Omega n R Sigma enum_name variant_name lts enum_type_args
      payloads edef vdef Sigma' R' payload_roots type_args,
    provenance_ready_args payloads ->
    Program.lookup_enum enum_name env = Some edef ->
    Program.lookup_enum_variant variant_name (Program.enum_variants edef) =
      Some vdef ->
    Datatypes.length lts = Program.enum_lifetimes edef ->
    Datatypes.length enum_type_args = Program.enum_type_params edef ->
    check_struct_bounds env (Program.enum_bounds edef) enum_type_args = None ->
    check_struct_bounds env (Program.enum_bounds edef)
      (map (subst_type_params_ty type_args) enum_type_args) = None ->
    typed_args_roots_shadow_safe env Omega n R Sigma payloads
      (params_of_tys
        (map (instantiate_enum_variant_field_ty lts enum_type_args)
          (Program.enum_variant_fields vdef))) Sigma' R' payload_roots ->
    Forall provenance_ready_leaf_expr payloads ->
    (forall T_actual T_expected,
        ty_compatible_b Omega T_actual T_expected = true ->
        ty_compatible_b Omega (subst_type_params_ty type_args T_actual)
          (subst_type_params_ty type_args T_expected) = true) ->
    ty_compatible_b Omega
      (instantiate_enum_ty edef lts
        (map (subst_type_params_ty type_args) enum_type_args))
      (subst_type_params_ty type_args
        (instantiate_enum_ty edef lts enum_type_args)) = true ->
    compose_type_params type_args enum_type_args =
      map (subst_type_params_ty type_args) enum_type_args ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args
          (EEnum enum_name variant_name lts enum_type_args payloads))
        T_subst (sctx_of_ctx Gamma_out_subst) R'
        (root_sets_union payload_roots) /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args
          (instantiate_enum_ty edef lts enum_type_args)) = true.
Proof.
  intros env Omega n R Sigma enum_name variant_name lts enum_type_args
    payloads edef vdef Sigma' R' payload_roots type_args Hready Hlookup
    Hlookup_variant Hlen_lts Hlen_args _ Hbounds_subst Htyped_payloads
    Hleaf Hcompat_subst Hcompat_result Hcompose.
  exists (instantiate_enum_ty edef lts
      (map (subst_type_params_ty type_args) enum_type_args)),
    (subst_type_params_ctx type_args Sigma').
  split.
  - simpl. rewrite subst_type_params_expr_list_go_map.
    eapply TERS_Enum; eauto.
    + rewrite length_map. exact Hlen_args.
    + assert (Hpayload_tys :
        map (subst_type_params_ty type_args)
          (map (instantiate_enum_variant_field_ty lts enum_type_args)
            (Program.enum_variant_fields vdef)) =
        map (instantiate_enum_variant_field_ty lts
          (map (subst_type_params_ty type_args) enum_type_args))
          (Program.enum_variant_fields vdef)).
      { rewrite <- Hcompose.
        rewrite map_map.
        apply map_ext. intro T.
        apply instantiate_enum_variant_field_ty_type_subst_compose. }
      rewrite <- Hpayload_tys.
      change (sctx_of_ctx (subst_type_params_ctx type_args Sigma')) with
        (subst_type_params_ctx type_args Sigma').
      eapply typed_args_roots_shadow_safe_provenance_ready_leaf_subst_type_params_package;
        eauto.
  - exact Hcompat_result.
Qed.

Lemma typed_env_roots_shadow_safe_edrop_provenance_ready_subst_type_params_compat_package :
  forall env Omega n R Sigma e Sigma' R' roots type_args,
    provenance_ready_expr e ->
    typed_env_roots_shadow_safe env Omega n R Sigma (EDrop e)
      (MkTy UUnrestricted TUnits) Sigma' R' roots ->
    (forall T_inner Sigma_inner R_inner roots_inner,
        typed_env_roots_shadow_safe env Omega n R Sigma e
          T_inner Sigma_inner R_inner roots_inner ->
        exists T_inner_subst Gamma_inner_subst,
          typed_env_roots_shadow_safe env Omega n R
            (subst_type_params_ctx type_args Sigma)
            (subst_type_params_expr type_args e)
            T_inner_subst (sctx_of_ctx Gamma_inner_subst)
            R_inner roots_inner /\
          ty_compatible_b Omega T_inner_subst
            (subst_type_params_ty type_args T_inner) = true) ->
    (forall T0, ty_compatible_b Omega T0 T0 = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (EDrop e))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args (MkTy UUnrestricted TUnits)) = true.
Proof.
  intros env Omega n R Sigma e Sigma' R' roots type_args
    _ Htyped Htransport Hcompat_refl.
  inversion Htyped; subst.
  match goal with
  | Hinner : typed_env_roots_shadow_safe env Omega n R Sigma e
      ?T_inner ?Sigma_inner ?R_inner ?roots_inner |- _ =>
      pose proof (Htransport T_inner Sigma_inner R_inner roots_inner Hinner)
        as [T_inner_subst [Gamma_inner_subst [Htyped_inner_subst _]]]
  end.
  exists (MkTy UUnrestricted TUnits), Gamma_inner_subst.
  split.
  - simpl. eapply TERS_Drop. exact Htyped_inner_subst.
  - simpl. apply Hcompat_refl.
Qed.

Inductive typed_env_roots_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERC_Conservative : forall R Σ e T Σ' R' roots,
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_checked env Ω n R Σ e T Σ' R' roots
  | TERC_CaptureRefFreeResult : forall R Σ e T Σ' R' roots,
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      typed_env_roots_checked env Ω n R Σ e T Σ' R' []
  | TERC_Let_CaptureRefFreeResult : forall R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2,
      typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      ty_compatible_b Ω T1 T = true ->
      root_env_lookup x R1 = None ->
      typed_env_roots_checked env Ω n (root_env_add x roots1 R1)
        (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T Σ2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      capture_ref_free_ty_b env T2 = true ->
      typed_env_roots_checked env Ω n R Σ (ELet m x T e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) []
  | TERC_LetInfer_CaptureRefFreeResult : forall R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2,
      typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      root_env_lookup x R1 = None ->
      typed_env_roots_checked env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      capture_ref_free_ty_b env T2 = true ->
      typed_env_roots_checked env Ω n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) [].

Inductive typed_env_roots_shadow_safe_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERSC_Conservative : forall R Σ e T Σ' R' roots,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots
  | TERSC_CaptureRefFreeResult : forall R Σ e T Σ' R' roots,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' []
  | TERSC_Let_CaptureRefFreeResult : forall R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      ty_compatible_b Ω T1 T = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      typed_env_roots_shadow_safe_checked env Ω n (root_env_add x roots1 R1)
        (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T Σ2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      capture_ref_free_ty_b env T2 = true ->
      typed_env_roots_shadow_safe_checked env Ω n R Σ (ELet m x T e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) []
  | TERSC_LetInfer_CaptureRefFreeResult : forall R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2,
      typed_env_roots_shadow_safe env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      typed_env_roots_shadow_safe_checked env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      capture_ref_free_ty_b env T2 = true ->
      typed_env_roots_shadow_safe_checked env Ω n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) [].

Lemma typed_env_roots_checked_of_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped.
  apply TERC_Conservative. exact Htyped.
Qed.

Lemma typed_env_roots_checked_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped Hfree.
  eapply TERC_CaptureRefFreeResult; eassumption.
Qed.

Lemma typed_env_roots_checked_underlying_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
    exists roots0,
      typed_env_roots_checked env Ω n R Σ e T Σ' R' roots0 /\
      (roots = roots0 \/
        (roots = [] /\ capture_ref_free_ty_b env T = true)).
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  exists roots. split; [exact Hchecked | left; reflexivity].
Qed.

Lemma typed_env_roots_checked_prune_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked Hfree.
  destruct Hchecked as
    [R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped
    |R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped _
    |R0 R1 R2 Σ0 Σ1 Σ2 m x Tann T1 e1 e2 T2 roots1 roots2
      Htyped1 Hcompat Hlookup Htyped2 Hcheck Hexcl _
    |R0 R1 R2 Σ0 Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      Htyped1 Hlookup Htyped2 Hcheck Hexcl _].
  - eapply TERC_CaptureRefFreeResult; eassumption.
  - eapply TERC_CaptureRefFreeResult; eassumption.
  - eapply TERC_Let_CaptureRefFreeResult; eassumption.
  - eapply TERC_LetInfer_CaptureRefFreeResult; eassumption.
Qed.

Lemma typed_env_roots_shadow_safe_checked_of_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped.
  apply TERSC_Conservative. exact Htyped.
Qed.

Lemma typed_env_roots_shadow_safe_checked_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped Hfree.
  eapply TERSC_CaptureRefFreeResult; eassumption.
Qed.

Lemma typed_env_roots_shadow_safe_checked_underlying_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots ->
    exists roots0,
      typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots0 /\
      (roots = roots0 \/
        (roots = [] /\ capture_ref_free_ty_b env T = true)).
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  exists roots. split; [exact Hchecked | left; reflexivity].
Qed.

Lemma typed_env_roots_shadow_safe_checked_prune_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked Hfree.
  destruct Hchecked as
    [R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped
    |R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped _
    |R0 R1 R2 Σ0 Σ1 Σ2 m x Tann T1 e1 e2 T2 roots1 roots2
      Htyped1 Hcompat Hlookup Hroots1 Hexcl1 Htyped2 Hcheck Hexcl _
    |R0 R1 R2 Σ0 Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      Htyped1 Hlookup Hroots1 Hexcl1 Htyped2 Hcheck Hexcl _].
  - eapply TERSC_CaptureRefFreeResult; eassumption.
  - eapply TERSC_CaptureRefFreeResult; eassumption.
  - eapply TERSC_Let_CaptureRefFreeResult; eassumption.
  - eapply TERSC_LetInfer_CaptureRefFreeResult; eassumption.
Qed.

Lemma typed_env_roots_checked_empty_of_shadow_safe_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped Hfree.
  eapply typed_env_roots_checked_capture_ref_free.
  - eapply typed_env_roots_shadow_safe_roots. exact Htyped.
  - exact Hfree.
Qed.

Lemma typed_env_roots_checked_structural :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  induction Hchecked.
  - eauto using typed_env_roots_structural.
  - eauto using typed_env_roots_structural.
  - eapply TES_Let; eauto using typed_env_roots_structural.
  - eapply TES_LetInfer; eauto using typed_env_roots_structural.
Qed.

Lemma typed_env_roots_shadow_safe_checked_checked :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  induction Hchecked.
  - apply TERC_Conservative.
    eauto using typed_env_roots_shadow_safe_roots.
  - eapply TERC_CaptureRefFreeResult; eauto using typed_env_roots_shadow_safe_roots.
  - eapply TERC_Let_CaptureRefFreeResult; eauto using typed_env_roots_shadow_safe_roots.
  - eapply TERC_LetInfer_CaptureRefFreeResult; eauto using typed_env_roots_shadow_safe_roots.
Qed.

Theorem eval_preserves_roots_ready_prefix_checked_expr :
  eval_preserves_typing_ready_prefix_for_roots_ready_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s'.
Proof.
  intros Hpres env s e s' v Heval Ω n R Σ T Σ' R' roots
    Hprov Hready Hstore Hroots Hshadow Hrn Hchecked.
  destruct Hchecked as
    [R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped
    |R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped Hfree
    |R0 R1 R2 Σ0 Σ1 Σ2 m x Tann T1 e1 e2 T2 roots1 roots2
      Htyped1 Hcompat Hlookup Htyped2 Hcheck Hexcl Hfree
    |R0 R1 R2 Σ0 Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      Htyped1 Hlookup Htyped2 Hcheck Hexcl Hfree].
  - eapply (proj1 (eval_preserves_roots_ready_prefix_mutual_with_preservation_core
      Hpres)); eassumption.
  - destruct (proj1 Hpres env s e0 s' v Heval Ω n Σ0 T0 Σ0'
        Hready Hstore
        (typed_env_roots_structural env Ω n R0 Σ0 e0 T0 Σ0' R0' roots0
          Htyped)) as [Hstore' [Hv_typed Hrefs]].
    destruct (proj1 eval_preserves_roots_ready_mutual env s e0 s' v Heval
        Ω n R0 Σ0 T0 Σ0' R0' roots0 Hprov Hroots Hshadow Hrn Htyped)
      as [Hroots' [_ [Hshadow' Hrn']]].
    repeat split; try assumption.
    eapply value_has_type_runtime_rootless_empty_roots.
    + exact Hv_typed.
    + eapply capture_ref_free_ty_b_runtime_rootless. exact Hfree.
  - inversion Hready.
  - inversion Hready.
Qed.
