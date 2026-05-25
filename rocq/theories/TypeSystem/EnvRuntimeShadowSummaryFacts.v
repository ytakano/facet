From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeReadinessFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition env_fns_root_shadow_summary_check_ready (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_summary env fdef.

Definition env_fns_root_shadow_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.

Definition callee_body_root_shadow_direct_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_provenance_summary env fdef \/
  exists fname args raw_body synthetic_body fcallee T_body Γ_out R_body roots_body,
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_provenance_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (fn_bounds (fn_with_body fdef synthetic_body)))
      (fn_outlives (fn_with_body fdef synthetic_body))
      (fn_lifetimes (fn_with_body fdef synthetic_body))
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx (fn_with_body fdef synthetic_body)))
      (fn_body (fn_with_body fdef synthetic_body)) T_body
      (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_direct_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_direct_call_provenance_summary env fdef.

Definition callee_body_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_direct_call_provenance_summary env fdef \/
  exists fname args raw_body synthetic_body fcallee T_body Γ_out R_body roots_body,
    fn_body fdef = raw_body /\
    local_fn_value_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_provenance_summary env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env
        (fn_bounds (fn_with_body fdef synthetic_body)))
      (fn_outlives (fn_with_body fdef synthetic_body))
      (fn_lifetimes (fn_with_body fdef synthetic_body))
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx (fn_with_body fdef synthetic_body)))
      (fn_body (fn_with_body fdef synthetic_body)) T_body
      (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition env_fns_root_shadow_non_capturing_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_non_capturing_call_provenance_summary env fdef.

Definition callee_body_root_shadow_captured_callee_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) /\
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fdef) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef ++ fn_captures fdef) roots_body /\
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef) R_body.

Definition callee_hidden_capture_args_disjoint
    (callee : fn_def) (args : list expr) : Prop :=
  Forall
    (fun x => ~ In x (args_local_store_names args))
    (ctx_names (params_ctx (fn_captures callee))).

Inductive expr_root_shadow_captured_call_provenance_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> ctx -> expr -> Prop :=
  | ERSC_Provenance : forall R Γ e,
      provenance_ready_expr e ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ e
  | ERSC_DirectCall : forall R Γ e fname args synthetic_body fcallee
      T_body Γ_out R_body roots_body,
      direct_call_target_expr e = Some (fname, args, synthetic_body) ->
      synthetic_body = ECall fname args ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_body_root_shadow_provenance_summary env fcallee ->
      typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ)
        synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ e
  | ERSC_CapturedCall : forall R Γ e fname captures args fcallee
      env_lt captured_tys T_body Γ_out R_body roots_body,
      captured_call_target_expr e = Some (fname, captures, args) ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_hidden_capture_args_disjoint fcallee args ->
      check_make_closure_captures_exact_sctx_with_env env Ω
        (sctx_of_ctx Γ) captures (fn_captures fcallee) =
        infer_ok (env_lt, captured_tys) ->
      NoDup (ctx_names (params_ctx (fn_params fcallee ++ fn_captures fcallee))) ->
      provenance_ready_expr (fn_body fcallee) ->
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env (fn_bounds fcallee))
        (fn_outlives fcallee)
        (fn_lifetimes fcallee)
        (initial_root_env_for_params
          (fn_params fcallee ++ fn_captures fcallee))
        (sctx_of_ctx (fn_body_ctx fcallee))
        (fn_body fcallee) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      ty_compatible_b (fn_outlives fcallee) T_body
        (fn_ret fcallee) = true ->
      roots_exclude_params (fn_params fcallee ++ fn_captures fcallee)
        roots_body ->
      root_env_excludes_params (fn_params fcallee ++ fn_captures fcallee)
        R_body ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ e
  | ERSC_If : forall R Γ e1 e2 e3 T_cond Γ1 R1 roots_cond,
      typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ)
        e1 T_cond (sctx_of_ctx Γ1) R1 roots_cond ->
      ty_core T_cond = TBooleans ->
      provenance_ready_expr e1 ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R1 Γ1 e2 ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R1 Γ1 e3 ->
      expr_root_shadow_captured_call_provenance_summary env Ω n R Γ
        (EIf e1 e2 e3).

Inductive expr_root_shadow_captured_call_provenance_summary_exact
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set ->
      Prop :=
  | ERSCE_Provenance : forall R Σ e T Σ' R' roots,
      provenance_ready_expr e ->
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots roots
  | ERSCE_DirectCall : forall R Σ e fname args synthetic_body fcallee
      T Σ' R' roots,
      direct_call_target_expr e = Some (fname, args, synthetic_body) ->
      synthetic_body = ECall fname args ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_body_root_shadow_provenance_summary env fcallee ->
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        synthetic_body T Σ' R' roots ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots roots
  | ERSCE_CapturedCall : forall R Σ fname captures args fcallee
      env_lt captured_tys T Σ' R' roots capture_roots
      T_body Γ_out R_body roots_body,
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_hidden_capture_args_disjoint fcallee args ->
      check_make_closure_captures_exact_sctx_with_env env Ω Σ
        captures (fn_captures fcallee) = infer_ok (env_lt, captured_tys) ->
      NoDup (ctx_names (params_ctx (fn_params fcallee ++ fn_captures fcallee))) ->
      provenance_ready_expr (fn_body fcallee) ->
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env (fn_bounds fcallee))
        (fn_outlives fcallee)
        (fn_lifetimes fcallee)
        (initial_root_env_for_params
          (fn_params fcallee ++ fn_captures fcallee))
        (sctx_of_ctx (fn_body_ctx fcallee))
        (fn_body fcallee) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      ty_compatible_b (fn_outlives fcallee) T_body
        (fn_ret fcallee) = true ->
      roots_exclude_params (fn_params fcallee ++ fn_captures fcallee)
        roots_body ->
      root_env_excludes_params (fn_params fcallee ++ fn_captures fcallee)
        R_body ->
      capture_root_bound R captures (fn_captures fcallee) =
        Some capture_roots ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallExpr (EMakeClosure fname captures) args) T Σ' R' roots ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ (ECallExpr (EMakeClosure fname captures) args)
        T Σ' R' roots (root_set_union roots capture_roots)
  | ERSCE_LocalCapturedLet : forall R Σ fname captures args m x T_hidden
      fcallee env_lt captured_tys T_direct T Σ' R' roots roots_direct
      capture_roots T_body Γ_out R_body roots_body,
      ty_usage T_hidden = UUnrestricted ->
      ~ In x captures ->
      ~ In x (ctx_names (params_ctx (fn_captures fcallee))) ->
      ~ In x (args_free_vars_ts args) ->
      ~ In x (args_local_store_names args) ->
      preservation_ready_args args ->
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      callee_hidden_capture_args_disjoint fcallee args ->
      check_make_closure_captures_exact_sctx_with_env env Ω Σ
        captures (fn_captures fcallee) = infer_ok (env_lt, captured_tys) ->
      NoDup (ctx_names (params_ctx (fn_params fcallee ++ fn_captures fcallee))) ->
      provenance_ready_expr (fn_body fcallee) ->
      typed_env_roots_shadow_safe
        (global_env_with_local_bounds env (fn_bounds fcallee))
        (fn_outlives fcallee)
        (fn_lifetimes fcallee)
        (initial_root_env_for_params
          (fn_params fcallee ++ fn_captures fcallee))
        (sctx_of_ctx (fn_body_ctx fcallee))
        (fn_body fcallee) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
      ty_compatible_b (fn_outlives fcallee) T_body
        (fn_ret fcallee) = true ->
      roots_exclude_params (fn_params fcallee ++ fn_captures fcallee)
        roots_body ->
      root_env_excludes_params (fn_params fcallee ++ fn_captures fcallee)
        R_body ->
      capture_root_bound R captures (fn_captures fcallee) =
        Some capture_roots ->
      root_env_lookup x R = None ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ECallExpr (EMakeClosure fname captures) args) T_direct
        Σ' R' roots_direct ->
      typed_env_roots_shadow_safe env Ω n R Σ
        (ELet m x T_hidden (EMakeClosure fname captures)
          (ECallExpr (EVar x) args)) T Σ' R' roots ->
      ty_compatible_b Ω T_direct T = true ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ
        (ELet m x T_hidden (EMakeClosure fname captures)
          (ECallExpr (EVar x) args))
        T Σ' R' roots (root_set_union roots_direct capture_roots)
  | ERSCE_If : forall R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3
      T_cond T2 T3 roots_cond roots2 roots3 ret_roots2 ret_roots3,
      provenance_ready_expr e1 ->
      typed_env_roots_shadow_safe env Ω n R Σ e1 T_cond Σ1 R1
        roots_cond ->
      ty_core T_cond = TBooleans ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ret_roots2 ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ret_roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      R2 = R3 ->
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        (sctx_of_ctx Σ4) R2 (root_set_union roots2 roots3)
        (root_set_union ret_roots2 ret_roots3).

Lemma expr_root_shadow_captured_call_provenance_summary_exact_typed :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - exact H0.
  - exact H5.
  - exact H11.
  - exact H18.
  - subst R3. eapply TERS_If; eauto. apply root_env_equiv_refl.
Qed.

Definition callee_body_root_shadow_captured_call_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_non_capturing_call_provenance_summary env fdef \/
  (
  exists fname captures args fcallee env_lt captured_tys
      T_body Γ_out R_body roots_body,
    fn_body fdef = ECallExpr (EMakeClosure fname captures) args /\
    captured_call_target_expr (fn_body fdef) = Some (fname, captures, args) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_hidden_capture_args_disjoint fcallee args /\
    check_make_closure_captures_exact_sctx_with_env env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee) = infer_ok (env_lt, captured_tys) /\
    callee_body_root_shadow_captured_callee_provenance_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body) \/
  (
  exists T_body Γ_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_captured_call_provenance_summary_exact env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body) \/
  (
  exists fname captures args m x T direct_body let_body fcallee
      env_lt captured_tys T_direct Γ_direct R_direct roots_direct
      T_let Γ_let R_let roots_let,
    fn_body fdef =
      ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args) /\
    local_captured_call_target_expr (fn_body fdef) =
      Some (fname, captures, args, m, x, T, direct_body, let_body) /\
    direct_body = ECallExpr (EMakeClosure fname captures) args /\
    let_body =
      ELet m x T (EMakeClosure fname captures) direct_body /\
    ty_usage T = UUnrestricted /\
    ~ In x captures /\
    ~ In x (ctx_names (params_ctx (fn_captures fcallee))) /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args) /\
    preservation_ready_args args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_hidden_capture_args_disjoint fcallee args /\
    check_make_closure_captures_exact_sctx_with_env env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee) = infer_ok (env_lt, captured_tys) /\
    callee_body_root_shadow_captured_callee_provenance_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      direct_body T_direct (sctx_of_ctx Γ_direct) R_direct roots_direct /\
    ty_compatible_b (fn_outlives fdef) T_direct (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_direct /\
    root_env_excludes_params (fn_params fdef) R_direct /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      let_body T_let (sctx_of_ctx Γ_let) R_let roots_let).

Definition env_fns_root_shadow_captured_call_provenance_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_provenance_summary env fdef.

Lemma capture_ref_free_ty_b_fuel_global_env_with_local_bounds :
  forall fuel env bounds T,
    capture_ref_free_ty_b_fuel fuel
      (global_env_with_local_bounds env bounds) T =
    capture_ref_free_ty_b_fuel fuel env T.
Proof.
  induction fuel as [| fuel IH]; intros env bounds T; simpl.
  - reflexivity.
  - destruct T as [u core].
	    destruct core as [| | | | name | idx | name lts args | name lts args | ts ret
	      | env_lt args ret | n Ω body | n type_bounds body | l rk inner];
      simpl; try reflexivity.
    + assert (Hargs :
        forallb
          (capture_ref_free_ty_b_fuel fuel
            (global_env_with_local_bounds env bounds)) args =
        forallb (capture_ref_free_ty_b_fuel fuel env) args).
      { induction args as [| T Ts IHTs]; simpl; [reflexivity |].
        rewrite (IH env bounds T), IHTs. reflexivity. }
      rewrite Hargs.
      destruct (lookup_struct name (global_env_with_local_bounds env bounds))
        as [sdef |] eqn:Hlookup_body.
      * change (lookup_struct name (global_env_with_local_bounds env bounds))
          with (lookup_struct name env) in Hlookup_body.
        rewrite Hlookup_body.
        assert (Hfields :
          forallb
            (fun f : field_def =>
              capture_ref_free_ty_b_fuel fuel
                (global_env_with_local_bounds env bounds)
                (instantiate_struct_field_ty lts args f)) (struct_fields sdef) =
          forallb
            (fun f : field_def =>
              capture_ref_free_ty_b_fuel fuel env
                (instantiate_struct_field_ty lts args f)) (struct_fields sdef)).
        { set (fields := struct_fields sdef).
          change (struct_fields sdef) with fields.
          induction fields as [| field fields IHfields].
          - reflexivity.
          - simpl.
            rewrite (IH env bounds (instantiate_struct_field_ty lts args field)).
            rewrite IHfields. reflexivity. }
	        rewrite Hfields. reflexivity.
	      * change (lookup_struct name (global_env_with_local_bounds env bounds))
	          with (lookup_struct name env) in Hlookup_body.
	        rewrite Hlookup_body. reflexivity.
    + assert (Hargs :
        forallb
          (capture_ref_free_ty_b_fuel fuel
            (global_env_with_local_bounds env bounds)) args =
        forallb (capture_ref_free_ty_b_fuel fuel env) args).
      { induction args as [| T Ts IHTs]; simpl; [reflexivity |].
        rewrite (IH env bounds T), IHTs. reflexivity. }
      rewrite Hargs.
      destruct (lookup_enum name (global_env_with_local_bounds env bounds))
        as [edef |] eqn:Hlookup_body.
      * change (lookup_enum name (global_env_with_local_bounds env bounds))
          with (lookup_enum name env) in Hlookup_body.
        rewrite Hlookup_body.
        assert (Hvariants :
          forallb
            (fun v : enum_variant_def =>
              forallb
                (fun T : Ty =>
                  capture_ref_free_ty_b_fuel fuel
                    (global_env_with_local_bounds env bounds)
                    (instantiate_enum_variant_field_ty lts args T))
                (enum_variant_fields v)) (enum_variants edef) =
          forallb
            (fun v : enum_variant_def =>
              forallb
                (fun T : Ty =>
                  capture_ref_free_ty_b_fuel fuel env
                    (instantiate_enum_variant_field_ty lts args T))
                (enum_variant_fields v)) (enum_variants edef)).
        { induction (enum_variants edef) as [| v vs IHvs]; simpl.
          - reflexivity.
          - assert (Hfields :
              forallb
                (fun T : Ty =>
                  capture_ref_free_ty_b_fuel fuel
                    (global_env_with_local_bounds env bounds)
                    (instantiate_enum_variant_field_ty lts args T))
                (enum_variant_fields v) =
              forallb
                (fun T : Ty =>
                  capture_ref_free_ty_b_fuel fuel env
                    (instantiate_enum_variant_field_ty lts args T))
                (enum_variant_fields v)).
            { induction (enum_variant_fields v) as [| T Ts IHTs]; simpl.
              - reflexivity.
              - rewrite (IH env bounds
                  (instantiate_enum_variant_field_ty lts args T)).
                rewrite IHTs. reflexivity. }
            rewrite Hfields, IHvs. reflexivity. }
        rewrite Hvariants. reflexivity.
      * change (lookup_enum name (global_env_with_local_bounds env bounds))
          with (lookup_enum name env) in Hlookup_body.
        rewrite Hlookup_body. reflexivity.
	    + assert (Hts :
        forallb
          (capture_ref_free_ty_b_fuel fuel
            (global_env_with_local_bounds env bounds)) ts =
        forallb (capture_ref_free_ty_b_fuel fuel env) ts).
      { induction ts as [| T Ts IHTs]; simpl; [reflexivity |].
        rewrite (IH env bounds T), IHTs. reflexivity. }
      rewrite Hts, (IH env bounds ret). reflexivity.
	    + apply IH.
	    + apply IH.
Qed.

Lemma capture_ref_free_ty_b_global_env_with_local_bounds :
  forall env bounds T,
    capture_ref_free_ty_b (global_env_with_local_bounds env bounds) T =
    capture_ref_free_ty_b env T.
Proof.
  intros env bounds T.
  unfold capture_ref_free_ty_b.
	  change (Datatypes.length
	    (env_structs (global_env_with_local_bounds env bounds)))
	    with (Datatypes.length (env_structs env)).
  change (Datatypes.length
    (env_enums (global_env_with_local_bounds env bounds)))
    with (Datatypes.length (env_enums env)).
	  apply capture_ref_free_ty_b_fuel_global_env_with_local_bounds.
Qed.

Lemma closure_capture_allowed_b_global_env_with_local_bounds :
  forall env bounds Ω env_lt T,
    closure_capture_allowed_b
      (global_env_with_local_bounds env bounds) Ω env_lt T =
    closure_capture_allowed_b env Ω env_lt T.
Proof.
  intros env bounds Ω env_lt T.
  unfold closure_capture_allowed_b.
  rewrite capture_ref_free_ty_b_global_env_with_local_bounds.
  reflexivity.
Qed.

Lemma closure_captures_allowed_b_global_env_with_local_bounds :
  forall captured_tys env bounds Ω env_lt,
    closure_captures_allowed_b
      (global_env_with_local_bounds env bounds) Ω env_lt captured_tys =
    closure_captures_allowed_b env Ω env_lt captured_tys.
Proof.
  induction captured_tys as [| T rest IH]; intros env bounds Ω env_lt;
    simpl; [reflexivity |].
  rewrite closure_capture_allowed_b_global_env_with_local_bounds, IH.
  reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_base_global_env_with_local_bounds :
  forall captures params env bounds Ω Σ,
    check_make_closure_captures_exact_sctx_with_env_base
      (global_env_with_local_bounds env bounds) Ω Σ captures params =
    check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures params.
Proof.
  induction captures as [| x captures IH];
    intros params env bounds Ω Σ; destruct params as [| cap params];
    simpl; try reflexivity.
  destruct (param_mutability cap); try reflexivity.
  destruct (sctx_lookup (param_name cap) Σ); try reflexivity.
  destruct (sctx_lookup x Σ) as [[T st] |]; try reflexivity.
  destruct (st_consumed st); try reflexivity.
  destruct (st_moved_paths st); try reflexivity.
  destruct (sctx_lookup_mut x Σ); try reflexivity.
  destruct m; try reflexivity.
  destruct (usage_eqb (ty_usage T) UUnrestricted); try reflexivity.
  destruct (ty_eqb T (param_ty cap) && ty_compatible_b Ω T (param_ty cap));
    try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_global_env_with_local_bounds :
  forall env bounds Ω Σ captures params,
    check_make_closure_captures_exact_sctx_with_env
      (global_env_with_local_bounds env bounds) Ω Σ captures params =
    check_make_closure_captures_exact_sctx_with_env
      env Ω Σ captures params.
Proof.
  intros env bounds Ω Σ captures params.
  unfold check_make_closure_captures_exact_sctx_with_env.
  rewrite check_make_closure_captures_exact_sctx_with_env_base_global_env_with_local_bounds.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures params) as [captured_tys | err]; [| reflexivity].
  destruct (infer_closure_env_lifetime Ω captured_tys) as [env_lt | err];
    [| reflexivity].
  rewrite closure_captures_allowed_b_global_env_with_local_bounds.
  reflexivity.
Qed.

Lemma callee_body_root_shadow_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    callee_body_root_shadow_summary env fdef ->
    callee_body_root_shadow_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef [Hnodup Hready_at].
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_ready_at in *.
  destruct Hready_at as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Hready & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  exists T_body, Γ_out, R_body, roots_body.
  repeat split;
    try exact Hprov;
    try exact Hready;
    try exact Hcompat;
    try exact Hexclude_roots;
    try exact Hexclude_env.
  change (global_env_with_local_bounds
    (global_env_with_local_bounds env bounds) (fn_bounds fdef))
    with (global_env_with_local_bounds env (fn_bounds fdef)).
  exact Htyped.
Qed.

Lemma env_fns_root_shadow_summary_evidence_global_env_with_local_bounds :
  forall env bounds,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_shadow_summary_evidence
      (global_env_with_local_bounds env bounds).
Proof.
  intros env bounds Hsummary fname fdef Hlookup.
  apply callee_body_root_shadow_summary_global_env_with_local_bounds.
  apply Hsummary with (fname := fname).
  exact Hlookup.
Qed.

Lemma callee_body_root_shadow_provenance_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    callee_body_root_shadow_provenance_summary env fdef ->
    callee_body_root_shadow_provenance_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef [Hnodup Hready_at].
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_provenance_ready_at in *.
  destruct Hready_at as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  exists T_body, Γ_out, R_body, roots_body.
  repeat split;
    try exact Hprov;
    try exact Hcompat;
    try exact Hexclude_roots;
    try exact Hexclude_env.
  change (global_env_with_local_bounds
    (global_env_with_local_bounds env bounds) (fn_bounds fdef))
    with (global_env_with_local_bounds env (fn_bounds fdef)).
  exact Htyped.
Qed.

Lemma callee_body_root_shadow_captured_callee_provenance_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    callee_body_root_shadow_captured_callee_provenance_summary env fdef ->
    callee_body_root_shadow_captured_callee_provenance_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef [Hnodup Hbody].
  split; [exact Hnodup |].
  destruct Hbody as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  exists T_body, Γ_out, R_body, roots_body.
  repeat split;
    try exact Hprov;
    try exact Hcompat;
    try exact Hexclude_roots;
    try exact Hexclude_env.
  change (global_env_with_local_bounds
    (global_env_with_local_bounds env bounds) (fn_bounds fdef))
    with (global_env_with_local_bounds env (fn_bounds fdef)).
  exact Htyped.
Qed.
