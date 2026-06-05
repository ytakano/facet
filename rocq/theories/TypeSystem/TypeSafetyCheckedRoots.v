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

Lemma lookup_expr_branch_subst_type_params_match_branches :
  forall type_args branches name e,
    lookup_expr_branch name branches = Some e ->
    lookup_expr_branch name
      (map (fun '(branch_name, binders, branch_expr) =>
        (branch_name, binders, subst_type_params_expr type_args branch_expr))
        branches) = Some (subst_type_params_expr type_args e).
Proof.
  intros type_args branches name e Hlookup.
  induction branches as [| [[branch_name binders] branch_expr] rest IH];
    simpl in *.
  - discriminate.
  - destruct (String.eqb name branch_name) eqn:Hname.
    + inversion Hlookup; subst. reflexivity.
    + apply IH. exact Hlookup.
Qed.

Lemma lookup_expr_branch_binders_subst_type_params_match_branches :
  forall type_args branches name binders,
    lookup_expr_branch_binders name branches = Some binders ->
    lookup_expr_branch_binders name
      (map (fun '(branch_name, branch_binders, branch_expr) =>
        (branch_name, branch_binders,
          subst_type_params_expr type_args branch_expr)) branches) =
      Some binders.
Proof.
  intros type_args branches name binders Hlookup.
  induction branches as [| [[branch_name branch_binders] branch_expr] rest IH];
    simpl in *.
  - discriminate.
  - destruct (String.eqb name branch_name) eqn:Hname.
    + exact Hlookup.
    + apply IH. exact Hlookup.
Qed.

Lemma first_unknown_variant_branch_subst_type_params_match_branches :
  forall type_args branches variants,
    first_unknown_variant_branch branches variants = None ->
    first_unknown_variant_branch
      (map (fun '(branch_name, binders, branch_expr) =>
        (branch_name, binders, subst_type_params_expr type_args branch_expr))
        branches) variants = None.
Proof.
  intros type_args branches variants Hunknown.
  induction branches as [| [[branch_name binders] branch_expr] rest IH];
    simpl in *.
  - reflexivity.
  - destruct (lookup_enum_variant branch_name variants); try discriminate.
    apply IH. exact Hunknown.
Qed.

Lemma typed_match_tail_roots_shadow_safe_subst_type_params_package :
  forall env Omega n lts enum_type_args R roots_scrut Sigma branches variants
      expected_core R_out Sigmas Ts roots_list type_args,
    typed_match_tail_roots_shadow_safe env Omega n lts enum_type_args R
      roots_scrut Sigma branches variants expected_core R_out Sigmas Ts
      roots_list ->
    (forall v rest e T Sigma_v_payload Rv_payload roots Sigma_v
        Sigmas_tail Ts_tail roots_tail binders ps,
        lookup_expr_branch_binders (Program.enum_variant_name v) branches =
          Some binders ->
        match_payload_params binders lts enum_type_args v = infer_ok ps ->
        params_names_nodup_b ps = true ->
        ctx_lookup_params_none_b ps Sigma = true ->
        root_env_lookup_params_none_b ps R = true ->
        lookup_expr_branch (Program.enum_variant_name v) branches = Some e ->
        typed_env_roots_shadow_safe env Omega n
          (root_env_add_params_roots_same ps roots_scrut R)
          (sctx_add_params ps Sigma) e T Sigma_v_payload Rv_payload roots ->
        params_ok_sctx_b env ps Sigma_v_payload = true ->
        roots_exclude_params ps roots ->
        Sigma_v = sctx_remove_params ps Sigma_v_payload ->
        ty_core T = expected_core ->
        root_env_equiv (root_env_remove_match_params ps Rv_payload) R_out ->
        typed_match_tail_roots_shadow_safe env Omega n lts enum_type_args R
          roots_scrut Sigma branches rest expected_core R_out Sigmas_tail
          Ts_tail roots_tail ->
        exists ps_subst,
          match_payload_params binders lts
            (map (subst_type_params_ty type_args) enum_type_args) v =
            infer_ok ps_subst /\
          params_names_nodup_b ps_subst = true /\
          ctx_lookup_params_none_b ps_subst
            (subst_type_params_ctx type_args Sigma) = true /\
          root_env_lookup_params_none_b ps_subst R = true /\
          typed_env_roots_shadow_safe env Omega n
            (root_env_add_params_roots_same ps_subst roots_scrut R)
            (sctx_add_params ps_subst
              (subst_type_params_ctx type_args Sigma))
            (subst_type_params_expr type_args e)
            (subst_type_params_ty type_args T)
            (subst_type_params_ctx type_args Sigma_v_payload)
            Rv_payload roots /\
          params_ok_sctx_b env ps_subst
            (subst_type_params_ctx type_args Sigma_v_payload) = true /\
          roots_exclude_params ps_subst roots /\
          root_env_excludes_params ps_subst
            (root_env_remove_match_params ps_subst Rv_payload) /\
          subst_type_params_ctx type_args Sigma_v =
            sctx_remove_params ps_subst
              (subst_type_params_ctx type_args Sigma_v_payload) /\
          ty_core (subst_type_params_ty type_args T) = expected_core /\
          root_env_equiv
            (root_env_remove_match_params ps_subst Rv_payload) R_out) ->
    typed_match_tail_roots_shadow_safe env Omega n lts
      (map (subst_type_params_ty type_args) enum_type_args) R roots_scrut
      (subst_type_params_ctx type_args Sigma)
      (map (fun '(branch_name, binders, branch_expr) =>
        (branch_name, binders, subst_type_params_expr type_args branch_expr))
        branches)
      variants expected_core R_out
      (map (subst_type_params_ctx type_args) Sigmas)
      (map (subst_type_params_ty type_args) Ts) roots_list.
Proof.
  intros env Omega n lts enum_type_args R roots_scrut Sigma branches variants
    expected_core R_out Sigmas Ts roots_list type_args Htail Hbranch.
  induction Htail.
  - simpl. constructor.
  - simpl.
    subst R_payload Rv.
    destruct (Hbranch v rest e T Σv_payload Rv_payload roots Σv
      Σs Ts rootss binders ps H H0 H1 H2 H3 H4 H6 H7 H8 H11 H12 H13 Htail)
      as (ps_subst & Hparams_subst & Hnodup_subst & Hctx_none_subst &
        Hroot_none_subst & Htyped_subst & Hparams_ok_subst &
        Hroots_exclude_subst & Hroot_excludes_subst & Hremove_subst &
        Hcore_subst & Hroot_equiv_subst).
    eapply TERSMatchTail_Cons
      with (ps := ps_subst)
           (R_payload :=
              root_env_add_params_roots_same ps_subst roots_scrut R)
           (Σv_payload := subst_type_params_ctx type_args Σv_payload)
           (Rv_payload := Rv_payload)
           (Rv := root_env_remove_match_params ps_subst Rv_payload).
    + eapply lookup_expr_branch_binders_subst_type_params_match_branches.
      exact H.
    + exact Hparams_subst.
    + exact Hnodup_subst.
    + exact Hctx_none_subst.
    + exact Hroot_none_subst.
    + eapply lookup_expr_branch_subst_type_params_match_branches. exact H4.
    + reflexivity.
    + exact Htyped_subst.
    + exact Hparams_ok_subst.
    + exact Hroots_exclude_subst.
    + reflexivity.
    + exact Hroot_excludes_subst.
    + exact Hremove_subst.
    + exact Hcore_subst.
    + exact Hroot_equiv_subst.
    + apply IHHtail.
Unshelve.
  all: eauto.
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

Lemma typed_env_roots_shadow_safe_eif_subst_type_params_compat_package :
  forall env Omega n R Sigma e1 e2 e3 T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma (EIf e1 e2 e3)
      T Sigma' R' roots ->
    (forall T_cond Sigma1 R1 roots_cond,
        typed_env_roots_shadow_safe env Omega n R Sigma e1
          T_cond Sigma1 R1 roots_cond ->
        exists T_cond_subst,
          typed_env_roots_shadow_safe env Omega n R
            (subst_type_params_ctx type_args Sigma)
            (subst_type_params_expr type_args e1)
            T_cond_subst (subst_type_params_ctx type_args Sigma1)
            R1 roots_cond /\
          ty_compatible_b Omega T_cond_subst
            (subst_type_params_ty type_args T_cond) = true) ->
    (forall Sigma1 R1 T2 Sigma2 R2 roots2,
        typed_env_roots_shadow_safe env Omega n R1 Sigma1 e2
          T2 Sigma2 R2 roots2 ->
        exists T2_subst,
          typed_env_roots_shadow_safe env Omega n R1
            (subst_type_params_ctx type_args Sigma1)
            (subst_type_params_expr type_args e2)
            T2_subst (subst_type_params_ctx type_args Sigma2) R2 roots2 /\
          ty_compatible_b Omega T2_subst
            (subst_type_params_ty type_args T2) = true) ->
    (forall Sigma1 R1 T3 Sigma3 R3 roots3,
        typed_env_roots_shadow_safe env Omega n R1 Sigma1 e3
          T3 Sigma3 R3 roots3 ->
        exists T3_subst,
          typed_env_roots_shadow_safe env Omega n R1
            (subst_type_params_ctx type_args Sigma1)
            (subst_type_params_expr type_args e3)
            T3_subst (subst_type_params_ctx type_args Sigma3) R3 roots3 /\
          ty_compatible_b Omega T3_subst
            (subst_type_params_ty type_args T3) = true) ->
    (forall T_cond T_cond_subst,
        ty_compatible_b Omega T_cond_subst
          (subst_type_params_ty type_args T_cond) = true ->
        ty_core T_cond = TBooleans ->
        ty_core T_cond_subst = TBooleans) ->
    (forall T2 T3 T2_subst T3_subst,
        ty_compatible_b Omega T2_subst
          (subst_type_params_ty type_args T2) = true ->
        ty_compatible_b Omega T3_subst
          (subst_type_params_ty type_args T3) = true ->
        ty_core T2 = ty_core T3 ->
        ty_core T2_subst = ty_core T3_subst) ->
    (forall Sigma2 Sigma3 Sigma4,
        ctx_merge (ctx_of_sctx Sigma2) (ctx_of_sctx Sigma3) =
          Some Sigma4 ->
        ctx_merge (ctx_of_sctx (subst_type_params_ctx type_args Sigma2))
          (ctx_of_sctx (subst_type_params_ctx type_args Sigma3)) =
          Some (subst_type_params_ctx type_args Sigma4)) ->
    (forall T2 T3 T2_subst T3_subst,
        ty_compatible_b Omega T2_subst
          (subst_type_params_ty type_args T2) = true ->
        ty_compatible_b Omega T3_subst
          (subst_type_params_ty type_args T3) = true ->
        ty_compatible_b Omega
          (MkTy (usage_max (ty_usage T2_subst) (ty_usage T3_subst))
            (ty_core T2_subst))
          (subst_type_params_ty type_args
            (MkTy (usage_max (ty_usage T2) (ty_usage T3))
              (ty_core T2))) = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (EIf e1 e2 e3))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args T) = true.
Proof.
  intros env Omega n R Sigma e1 e2 e3 T Sigma' R' roots type_args
    Htyped Htransport_cond Htransport_then Htransport_else Hcond_core
    Hbranch_core Hmerge_subst Hcompat_result.
  inversion Htyped; subst.
  match goal with
  | Hcond : typed_env_roots_shadow_safe env Omega n R Sigma e1
      ?T_cond ?Sigma1 ?R1 ?roots_cond |- _ =>
      pose proof (Htransport_cond T_cond Sigma1 R1 roots_cond Hcond)
        as [T_cond_subst [Htyped_cond_subst Hcompat_cond]]
  end.
  match goal with
  | Hthen : typed_env_roots_shadow_safe env Omega n ?R1 ?Sigma1 e2
      ?T2 ?Sigma2 ?R2 ?roots2 |- _ =>
      pose proof (Htransport_then Sigma1 R1 T2 Sigma2 R2 roots2 Hthen)
        as [T2_subst [Htyped_then_subst Hcompat_then]]
  end.
  match goal with
  | Helse : typed_env_roots_shadow_safe env Omega n ?R1 ?Sigma1 e3
      ?T3 ?Sigma3 ?R3 ?roots3 |- _ =>
      pose proof (Htransport_else Sigma1 R1 T3 Sigma3 R3 roots3 Helse)
        as [T3_subst [Htyped_else_subst Hcompat_else]]
  end.
  exists (MkTy (usage_max (ty_usage T2_subst) (ty_usage T3_subst))
      (ty_core T2_subst)), (subst_type_params_ctx type_args Sigma').
  split.
  - simpl. eapply TERS_If.
    + exact Htyped_cond_subst.
    + eapply Hcond_core; eauto.
    + exact Htyped_then_subst.
    + exact Htyped_else_subst.
    + eapply Hbranch_core; eauto.
    + eapply Hmerge_subst; eauto.
    + assumption.
  - eapply Hcompat_result; eauto.
Qed.

Lemma typed_env_roots_shadow_safe_elet_subst_type_params_compat_package :
  forall env Omega n R Sigma m x T_ann e1 e2 T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ELet m x T_ann e1 e2) T Sigma' R' roots ->
    (forall T1 Sigma1 R1 roots1,
        typed_env_roots_shadow_safe env Omega n R Sigma e1
          T1 Sigma1 R1 roots1 ->
        exists T1_subst,
          typed_env_roots_shadow_safe env Omega n R
            (subst_type_params_ctx type_args Sigma)
            (subst_type_params_expr type_args e1)
            T1_subst (subst_type_params_ctx type_args Sigma1)
            R1 roots1 /\
          ty_compatible_b Omega T1_subst
            (subst_type_params_ty type_args T1) = true) ->
    (forall T1 T1_subst,
        ty_compatible_b Omega T1_subst
          (subst_type_params_ty type_args T1) = true ->
        ty_compatible_b Omega T1 T_ann = true ->
        ty_compatible_b Omega T1_subst
          (subst_type_params_ty type_args T_ann) = true) ->
    (forall T1 T1_subst Sigma1 R1 roots1 T2 Sigma2 R2 roots2,
        typed_env_roots_shadow_safe env Omega n
          (root_env_add x roots1 R1) (sctx_add x T_ann m Sigma1)
          e2 T2 Sigma2 R2 roots2 ->
        ty_compatible_b Omega T1_subst
          (subst_type_params_ty type_args T1) = true ->
        ty_compatible_b Omega T1 T_ann = true ->
        ty_compatible_b Omega T1_subst
          (subst_type_params_ty type_args T_ann) = true ->
        exists T2_subst,
          typed_env_roots_shadow_safe env Omega n
            (root_env_add x roots1 R1)
            (sctx_add x (subst_type_params_ty type_args T_ann) m
              (subst_type_params_ctx type_args Sigma1))
            (subst_type_params_expr type_args e2)
            T2_subst (subst_type_params_ctx type_args Sigma2)
            R2 roots2 /\
          ty_compatible_b Omega T2_subst
            (subst_type_params_ty type_args T2) = true) ->
    (forall Sigma2,
        sctx_check_ok env x T_ann Sigma2 = true ->
        sctx_check_ok env x (subst_type_params_ty type_args T_ann)
          (subst_type_params_ctx type_args Sigma2) = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (ELet m x T_ann e1 e2))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args T) = true.
Proof.
  intros env Omega n R Sigma m x T_ann e1 e2 T Sigma' R' roots type_args
    Htyped Htransport_e1 Htransport_ann Htransport_e2 Hcheck_subst.
  inversion Htyped; subst.
  match goal with
  | He1 : typed_env_roots_shadow_safe env Omega n R Sigma e1
      ?T1 ?Sigma1 ?R1 ?roots1 |- _ =>
      pose proof (Htransport_e1 T1 Sigma1 R1 roots1 He1)
        as [T1_subst [Htyped_e1_subst Hcompat_e1]]
  end.
  match goal with
  | Hcompat_ann : ty_compatible_b Omega ?T1 T_ann = true |- _ =>
      pose proof (Htransport_ann T1 T1_subst Hcompat_e1 Hcompat_ann)
        as Hcompat_ann_subst
  end.
  match goal with
  | He2 : typed_env_roots_shadow_safe env Omega n
      (root_env_add x ?roots1 ?R1) (sctx_add x T_ann m ?Sigma1)
      e2 ?T2 ?Sigma2 ?R2 ?roots2,
    Hcompat_ann : ty_compatible_b Omega ?T1 T_ann = true |- _ =>
      pose proof (Htransport_e2 T1 T1_subst Sigma1 R1 roots1
        T2 Sigma2 R2 roots2 He2 Hcompat_e1 Hcompat_ann
        Hcompat_ann_subst)
        as [T2_subst [Htyped_e2_subst Hcompat_e2]]
  end.
  exists T2_subst, (subst_type_params_ctx type_args (sctx_remove x Σ2)).
  split.
  - simpl. rewrite subst_type_params_ctx_sctx_remove.
    eapply TERS_Let.
    + exact Htyped_e1_subst.
    + exact Hcompat_ann_subst.
    + eassumption.
    + eassumption.
    + eassumption.
    + exact Htyped_e2_subst.
    + eapply Hcheck_subst; eauto.
    + eassumption.
    + eassumption.
  - exact Hcompat_e2.
Qed.

Lemma typed_env_roots_shadow_safe_eletinfer_subst_type_params_compat_package :
  forall env Omega n R Sigma m x e1 e2 T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ELetInfer m x e1 e2) T Sigma' R' roots ->
    (forall T1 Sigma1 R1 roots1,
        typed_env_roots_shadow_safe env Omega n R Sigma e1
          T1 Sigma1 R1 roots1 ->
        exists T1_subst,
          typed_env_roots_shadow_safe env Omega n R
            (subst_type_params_ctx type_args Sigma)
            (subst_type_params_expr type_args e1)
            T1_subst (subst_type_params_ctx type_args Sigma1)
            R1 roots1 /\
          ty_compatible_b Omega T1_subst
            (subst_type_params_ty type_args T1) = true) ->
    (forall T1 T1_subst Sigma1 R1 roots1 T2 Sigma2 R2 roots2,
        typed_env_roots_shadow_safe env Omega n
          (root_env_add x roots1 R1) (sctx_add x T1 m Sigma1)
          e2 T2 Sigma2 R2 roots2 ->
        ty_compatible_b Omega T1_subst
          (subst_type_params_ty type_args T1) = true ->
        exists T2_subst,
          typed_env_roots_shadow_safe env Omega n
            (root_env_add x roots1 R1)
            (sctx_add x T1_subst m
              (subst_type_params_ctx type_args Sigma1))
            (subst_type_params_expr type_args e2)
            T2_subst (subst_type_params_ctx type_args Sigma2)
            R2 roots2 /\
          ty_compatible_b Omega T2_subst
            (subst_type_params_ty type_args T2) = true) ->
    (forall T1 T1_subst Sigma2,
        ty_compatible_b Omega T1_subst
          (subst_type_params_ty type_args T1) = true ->
        sctx_check_ok env x T1 Sigma2 = true ->
        sctx_check_ok env x T1_subst
          (subst_type_params_ctx type_args Sigma2) = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (ELetInfer m x e1 e2))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args T) = true.
Proof.
  intros env Omega n R Sigma m x e1 e2 T Sigma' R' roots type_args
    Htyped Htransport_e1 Htransport_e2 Hcheck_subst.
  inversion Htyped; subst.
  match goal with
  | He1 : typed_env_roots_shadow_safe env Omega n R Sigma e1
      ?T1 ?Sigma1 ?R1 ?roots1 |- _ =>
      pose proof (Htransport_e1 T1 Sigma1 R1 roots1 He1)
        as [T1_subst [Htyped_e1_subst Hcompat_e1]]
  end.
  match goal with
  | He2 : typed_env_roots_shadow_safe env Omega n
      (root_env_add x ?roots1 ?R1) (sctx_add x ?T1 m ?Sigma1)
      e2 ?T2 ?Sigma2 ?R2 ?roots2 |- _ =>
      pose proof (Htransport_e2 T1 T1_subst Sigma1 R1 roots1
        T2 Sigma2 R2 roots2 He2 Hcompat_e1)
        as [T2_subst [Htyped_e2_subst Hcompat_e2]]
  end.
  exists T2_subst, (subst_type_params_ctx type_args (sctx_remove x Σ2)).
  split.
  - simpl. rewrite subst_type_params_ctx_sctx_remove.
    eapply TERS_LetInfer.
    + exact Htyped_e1_subst.
    + eassumption.
    + eassumption.
    + eassumption.
    + exact Htyped_e2_subst.
    + eapply Hcheck_subst; eauto.
    + eassumption.
    + eassumption.
  - exact Hcompat_e2.
Qed.

Lemma typed_env_roots_shadow_safe_eassign_subst_type_params_compat_package :
  forall env Omega n R Sigma p e_new Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma (EAssign p e_new)
      (MkTy UUnrestricted TUnits) Sigma' R' roots ->
    (forall T_new Sigma_new R_new roots_new,
        typed_env_roots_shadow_safe env Omega n R Sigma e_new
          T_new Sigma_new R_new roots_new ->
        exists T_new_subst,
          typed_env_roots_shadow_safe env Omega n R
            (subst_type_params_ctx type_args Sigma)
            (subst_type_params_expr type_args e_new)
            T_new_subst (subst_type_params_ctx type_args Sigma_new)
            R_new roots_new /\
          ty_compatible_b Omega T_new_subst
            (subst_type_params_ty type_args T_new) = true) ->
    (forall T_old T_new T_new_subst,
        ty_compatible_b Omega T_new_subst
          (subst_type_params_ty type_args T_new) = true ->
        ty_compatible_b Omega T_new T_old = true ->
        ty_compatible_b Omega T_new_subst
          (subst_type_params_ty type_args T_old) = true) ->
    (forall T0, ty_compatible_b Omega T0 T0 = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (EAssign p e_new))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args (MkTy UUnrestricted TUnits)) = true.
Proof.
  intros env Omega n R Sigma p e_new Sigma' R' roots type_args
    Htyped Htransport Hcompat_assign Hcompat_refl.
  inversion Htyped; subst.
  - match goal with
    | Hnew : typed_env_roots_shadow_safe env Omega n R Sigma e_new
        ?T_new ?Sigma_new ?R_new ?roots_new |- _ =>
        pose proof (Htransport T_new Sigma_new R_new roots_new Hnew)
          as [T_new_subst [Htyped_new_subst Hcompat_new]]
    end.
    exists (MkTy UUnrestricted TUnits), (subst_type_params_ctx type_args Sigma').
    split.
    + simpl. eapply TERS_Assign_Path.
      * eapply typed_place_env_structural_subst_type_params_ctx. eassumption.
      * rewrite ty_usage_subst_type_params_ty. eassumption.
      * eassumption.
      * eapply writable_place_env_structural_subst_type_params_ctx. eassumption.
      * exact Htyped_new_subst.
      * eassumption.
      * eapply Hcompat_assign; eauto.
      * change (sctx_path_available (subst_type_params_ctx type_args Sigma') x path = infer_ok tt).
        rewrite sctx_path_available_subst_type_params_ctx. exact H10.
    + simpl. apply Hcompat_refl.
  - match goal with
    | Hnew : typed_env_roots_shadow_safe env Omega n R Sigma e_new
        ?T_new ?Sigma_new ?R_new ?roots_new |- _ =>
        pose proof (Htransport T_new Sigma_new R_new roots_new Hnew)
          as [T_new_subst [Htyped_new_subst Hcompat_new]]
    end.
    exists (MkTy UUnrestricted TUnits), (subst_type_params_ctx type_args Sigma').
    split.
    + simpl. eapply TERS_Assign_Resolved.
      * eapply typed_place_env_structural_subst_type_params_ctx. eassumption.
      * rewrite ty_usage_subst_type_params_ty. eassumption.
      * eassumption.
      * eapply place_resolved_write_writable_chain_subst_type_params_ctx.
        eassumption.
      * eassumption.
      * rewrite sctx_lookup_mut_subst_type_params_ctx. eassumption.
      * eapply writable_place_env_structural_subst_type_params_ctx. eassumption.
      * exact Htyped_new_subst.
      * eassumption.
      * eapply Hcompat_assign; eauto.
    + simpl. apply Hcompat_refl.
Qed.

Lemma typed_env_roots_shadow_safe_ereplace_subst_type_params_compat_package :
  forall env Omega n R Sigma p e_new T Sigma' R' roots type_args,
    typed_env_roots_shadow_safe env Omega n R Sigma (EReplace p e_new)
      T Sigma' R' roots ->
    (forall T_new Sigma_new R_new roots_new,
        typed_env_roots_shadow_safe env Omega n R Sigma e_new
          T_new Sigma_new R_new roots_new ->
        exists T_new_subst,
          typed_env_roots_shadow_safe env Omega n R
            (subst_type_params_ctx type_args Sigma)
            (subst_type_params_expr type_args e_new)
            T_new_subst (subst_type_params_ctx type_args Sigma_new)
            R_new roots_new /\
          ty_compatible_b Omega T_new_subst
            (subst_type_params_ty type_args T_new) = true) ->
    (forall T_old T_new T_new_subst,
        ty_compatible_b Omega T_new_subst
          (subst_type_params_ty type_args T_new) = true ->
        ty_compatible_b Omega T_new T_old = true ->
        ty_compatible_b Omega T_new_subst
          (subst_type_params_ty type_args T_old) = true) ->
    (forall T_old,
        ty_compatible_b Omega (subst_type_params_ty type_args T_old)
          (subst_type_params_ty type_args T_old) = true) ->
    exists T_subst Gamma_out_subst,
      typed_env_roots_shadow_safe env Omega n R
        (subst_type_params_ctx type_args Sigma)
        (subst_type_params_expr type_args (EReplace p e_new))
        T_subst (sctx_of_ctx Gamma_out_subst) R' roots /\
      ty_compatible_b Omega T_subst
        (subst_type_params_ty type_args T) = true.
Proof.
  intros env Omega n R Sigma p e_new T Sigma' R' roots type_args
    Htyped Htransport Hcompat_replace Hcompat_result.
  inversion Htyped; subst.
  - match goal with
    | Hnew : typed_env_roots_shadow_safe env Omega n R Sigma e_new
        ?T_new ?Sigma_new ?R_new ?roots_new |- _ =>
        pose proof (Htransport T_new Sigma_new R_new roots_new Hnew)
          as [T_new_subst [Htyped_new_subst Hcompat_new]]
    end.
    match goal with
    | Hplace : typed_place_env_structural env Sigma p ?T_old |- _ =>
        exists (subst_type_params_ty type_args T_old),
          (subst_type_params_ctx type_args Sigma')
    end.
    split.
    + simpl. eapply TERS_Replace_Path.
      * eapply typed_place_env_structural_subst_type_params_ctx. eassumption.
      * eassumption.
      * eapply writable_place_env_structural_subst_type_params_ctx. eassumption.
      * eassumption.
      * exact Htyped_new_subst.
      * eassumption.
      * eapply Hcompat_replace; eauto.
      * match goal with
        | Havail : sctx_path_available ?Sigma1 ?x ?path = infer_ok tt
            |- sctx_path_available (subst_type_params_ctx type_args ?Sigma1)
                 ?x ?path = infer_ok tt =>
            rewrite sctx_path_available_subst_type_params_ctx; exact Havail
        end.
      * change (sctx_restore_path (subst_type_params_ctx type_args Σ1) x path =
          infer_ok (subst_type_params_ctx type_args Sigma')).
        rewrite sctx_restore_path_subst_type_params_ctx.
        match goal with
        | Hrestore : sctx_restore_path Σ1 x path = infer_ok Sigma' |- _ =>
            rewrite Hrestore; reflexivity
        end.
    + apply Hcompat_result.
  - match goal with
    | Hnew : typed_env_roots_shadow_safe env Omega n R Sigma e_new
        ?T_new ?Sigma_new ?R_new ?roots_new |- _ =>
        pose proof (Htransport T_new Sigma_new R_new roots_new Hnew)
          as [T_new_subst [Htyped_new_subst Hcompat_new]]
    end.
    match goal with
    | Hplace : typed_place_env_structural env Sigma p ?T_old |- _ =>
        exists (subst_type_params_ty type_args T_old),
          (subst_type_params_ctx type_args Sigma')
    end.
    split.
    + simpl. eapply TERS_Replace_Resolved.
      * eapply typed_place_env_structural_subst_type_params_ctx. eassumption.
      * eassumption.
      * eapply place_resolved_write_writable_chain_subst_type_params_ctx.
        eassumption.
      * eassumption.
      * eassumption.
      * rewrite sctx_lookup_mut_subst_type_params_ctx. eassumption.
      * eapply writable_place_env_structural_subst_type_params_ctx. eassumption.
      * exact Htyped_new_subst.
      * eassumption.
      * eapply Hcompat_replace; eauto.
    + apply Hcompat_result.
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
