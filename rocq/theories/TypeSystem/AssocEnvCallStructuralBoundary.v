From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker RootProvenance
  EnvStructuralRules EnvTypingSoundness EnvRootSoundness AssocEnvStructural
  AssocDirectCallHelpers AssocFnValueCallHelpers
  AssocArgBoolFacts AssocFnValueCallFacts
  AssocEnvArgSoundness AssocEnvRootArgSoundness EnvSoundnessFacts.
From Stdlib Require Import List String Bool PeanoNat.
Import ListNotations.

(* Specification-only call typing boundaries for associated projections.
   These mirror the env/root structural call constructors, but keep associated
   projection compatibility only at the argument-list boundary. They do not
   change the executable checker or the primary typed_env_structural relation. *)
Inductive typed_env_structural_assoc_call_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TESAssocBoundary_Call : forall Sigma Sigma' fname fdef args sigma,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_env_structural_assoc env Omega n Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECall fname args) (apply_lt_ty sigma (fn_ret fdef)) Sigma'
  | TESAssocBoundary_CallGeneric : forall Sigma Sigma' fname fdef
      (type_args : list Ty) args sigma,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma args
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fdef))) Sigma' ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallGeneric fname type_args args)
        (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
        Sigma'
  | TESAssocBoundary_CallExpr_Fn : forall Sigma Sigma1 Sigma' callee args
      u param_tys ret,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TFn param_tys ret)) Sigma1 ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys param_tys) Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) ret Sigma'
  | TESAssocBoundary_CallExpr_Closure : forall Sigma Sigma1 Sigma' callee
      args u env_lt param_tys ret,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TClosure env_lt param_tys ret)) Sigma1 ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys param_tys) Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) ret Sigma'
  | TESAssocBoundary_CallExpr_Forall : forall Sigma Sigma1 Sigma' callee args
      u m bounds body param_tys ret sigma,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TForall m bounds body)) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma'
  | TESAssocBoundary_CallExpr_Forall_Closure : forall Sigma Sigma1 Sigma'
      callee args u m bounds body env_lt param_tys ret sigma,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TForall m bounds body)) Sigma1 ->
      ty_core body = TClosure env_lt param_tys ret ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' ->
      contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma'
  | TESAssocBoundary_CallExpr_MixedForall : forall Sigma Sigma1 Sigma'
      callee args u u_body m bounds type_params type_bounds body param_tys
      ret sigma type_args,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds sigma type_bounds)
        type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys
          (map (open_bound_ty sigma)
            (map (subst_type_params_ty type_args) param_tys))) Sigma' ->
      contains_lbound_ty
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args)
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) Sigma'
  | TESAssocBoundary_CallExpr_TypeForall : forall Sigma Sigma1 Sigma' callee
      args u m bounds body param_tys ret type_args,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TTypeForall m bounds body)) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr callee args) (subst_type_params_ty type_args ret) Sigma'
  | TESAssocBoundary_CallExprGeneric_TypeForall : forall Sigma Sigma1 Sigma'
      callee args u m bounds body param_tys ret type_args,
      typed_env_structural env Omega n Sigma callee
        (MkTy u (TTypeForall m bounds body)) Sigma1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_env_structural_assoc env Omega n Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExprGeneric callee type_args args)
        (subst_type_params_ty type_args ret) Sigma'
  | TESAssocBoundary_CallExpr_MakeClosure : forall Sigma Sigma' fname fdef
      captures env_lt captured_tys args sigma,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Omega Sigma captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_env_structural_assoc env Omega n Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_structural_assoc_call_boundary env Omega n Sigma
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty sigma (fn_ret fdef)) Sigma'.

Inductive typed_env_roots_assoc_call_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERAssocBoundary_Call : forall R R' Sigma Sigma' fname fdef args sigma
      arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_roots_assoc env Omega n R Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' R' arg_roots ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECall fname args) (apply_lt_ty sigma (fn_ret fdef)) Sigma' R'
        (root_sets_union arg_roots)
  | TERAssocBoundary_CallGeneric : forall R R' Sigma Sigma' fname fdef
      (type_args : list Ty) args sigma arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_roots_assoc env Omega n R Sigma args
        (apply_lt_params sigma
          (apply_type_params type_args (fn_params fdef))) Sigma' R'
        arg_roots ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallGeneric fname type_args args)
        (apply_lt_ty sigma (subst_type_params_ty type_args (fn_ret fdef)))
        Sigma' R' (root_sets_union arg_roots)
  | TERAssocBoundary_CallExpr_Fn : forall R R1 R' Sigma Sigma1 Sigma'
      callee args u param_tys ret arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TFn param_tys ret)) Sigma1 R1 roots_callee ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys param_tys) Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) ret Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_Closure : forall R R1 R' Sigma Sigma1 Sigma'
      callee args u env_lt param_tys ret arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TClosure env_lt param_tys ret)) Sigma1 R1 roots_callee ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys param_tys) Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) ret Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_TypeForall : forall R R1 R' Sigma Sigma1
      Sigma' callee args u type_params bounds body_ty param_tys ret_inner
      type_args arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Sigma1 R1
        roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) (subst_type_params_ty type_args ret_inner)
        Sigma' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExprGeneric_TypeForall : forall R R1 R' Sigma
      Sigma1 Sigma' callee args u type_params bounds body_ty param_tys
      ret_inner type_args arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Sigma1 R1
        roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Sigma' R' arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExprGeneric callee type_args args)
        (subst_type_params_ty type_args ret_inner) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_MixedForall : forall R R1 R' Sigma Sigma1
      Sigma' callee args u u_body m bounds type_params type_bounds body_ty
      param_tys ret sigma type_args arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body_ty))))
        Sigma1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds sigma type_bounds)
        type_args = None ->
      contains_lbound_ty
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys
          (map (open_bound_ty sigma)
            (map (subst_type_params_ty type_args) param_tys))) Sigma' R'
        arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args)
        (open_bound_ty sigma (subst_type_params_ty type_args ret)) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_Forall_Fn : forall R R1 R' Sigma Sigma1
      Sigma' callee args u m bounds body_ty param_tys ret sigma arg_roots
      roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R'
        arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_Forall_Closure : forall R R1 R' Sigma Sigma1
      Sigma' callee args u m bounds body_ty env_lt param_tys ret sigma
      arg_roots roots_callee,
      typed_env_roots env Omega n R Sigma callee
        (MkTy u (TForall m bounds body_ty)) Sigma1 R1 roots_callee ->
      ty_core body_ty = TClosure env_lt param_tys ret ->
      contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false ->
      contains_lbound_ty (open_bound_ty sigma ret) = false ->
      contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
      Forall (fun '(a, b) => outlives Omega a b)
        (open_bound_outlives sigma bounds) ->
      typed_args_roots_assoc env Omega n R1 Sigma1 args
        (params_of_tys (map (open_bound_ty sigma) param_tys)) Sigma' R'
        arg_roots ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr callee args) (open_bound_ty sigma ret) Sigma' R'
        (root_set_union roots_callee (root_sets_union arg_roots))
  | TERAssocBoundary_CallExpr_MakeClosure : forall R R' Sigma Sigma' fname
      fdef captures env_lt captured_tys args sigma arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Omega Sigma captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_roots_assoc env Omega n R Sigma args
        (apply_lt_params sigma (fn_params fdef)) Sigma' R' arg_roots ->
      Forall (fun '(a, b) => outlives Omega a b)
        (apply_lt_outlives sigma (fn_outlives fdef)) ->
      typed_env_roots_assoc_call_boundary env Omega n R Sigma
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty sigma (fn_ret fdef)) Sigma' R'
        (root_sets_union arg_roots).


Lemma infer_env_direct_call_assoc_structural_boundary :
  forall fuel env Omega n fname fdef args arg_tys T Sigma Sigma',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    infer_env_args_collect fuel env Omega n Sigma args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma1,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma1) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma1) ->
    infer_direct_call_assoc env Omega n fdef arg_tys = infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECall fname args) T Sigma'.
Proof.
  intros fuel env Omega n fname fdef args arg_tys T Sigma Sigma'
    Hin Hname Hcollect Hexpr Hcall.
  unfold infer_direct_call_assoc in Hcall.
  destruct (no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0)
    eqn:Hgate; try discriminate.
  destruct (build_sigma (fn_lifetimes fdef)
    (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef))
    as [sigma_acc|] eqn:Hsigma; try discriminate.
  destruct (check_args_assoc env Omega arg_tys
    (apply_lt_params (finalize_subst sigma_acc) (fn_params fdef)))
    as [err|] eqn:Hcheck; try discriminate.
  destruct (forallb (wf_lifetime_b (mk_region_ctx n))
    (finalize_subst sigma_acc)) eqn:Hwf; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)))
    eqn:Hout; try discriminate.
  inversion Hcall; subst; clear Hcall.
  apply andb_true_iff in Hgate as [Hcaptures Htype_params].
  unfold no_captures_b in Hcaptures.
  destruct (fn_captures fdef) as [| capture captures] eqn:Hcaps;
    try discriminate.
  apply Nat.eqb_eq in Htype_params.
  eapply TESAssocBoundary_Call.
  - exact Hin.
  - first [reflexivity | exact Hname].
  - exact Hcaps.
  - exact Htype_params.
  - eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Lemma infer_env_direct_call_generic_assoc_structural_boundary :
  forall fuel env Omega n fname fdef type_args args arg_tys T Sigma Sigma',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    infer_env_args_collect fuel env Omega n Sigma args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma1,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma1) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma1) ->
    infer_direct_call_generic_assoc env Omega n fdef type_args arg_tys =
      infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallGeneric fname type_args args) T Sigma'.
Proof.
  intros fuel env Omega n fname fdef type_args args arg_tys T Sigma Sigma'
    Hin Hname Hcollect Hexpr Hcall.
  unfold infer_direct_call_generic_assoc in Hcall.
  destruct (no_captures_b fdef &&
    Nat.eqb (Datatypes.length type_args) (fn_type_params fdef))
    eqn:Hgate; try discriminate.
  destruct (check_struct_bounds env (fn_bounds fdef) type_args)
    as [err_bounds|] eqn:Hbounds; try discriminate.
  destruct (build_sigma (fn_lifetimes fdef)
    (repeat None (fn_lifetimes fdef)) arg_tys
    (apply_type_params type_args (fn_params fdef)))
    as [sigma_acc|] eqn:Hsigma; try discriminate.
  destruct (check_args_assoc env Omega arg_tys
    (apply_lt_params (finalize_subst sigma_acc)
      (apply_type_params type_args (fn_params fdef))))
    as [err|] eqn:Hcheck; try discriminate.
  destruct (forallb (wf_lifetime_b (mk_region_ctx n))
    (finalize_subst sigma_acc)) eqn:Hwf; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)))
    eqn:Hout; try discriminate.
  inversion Hcall; subst; clear Hcall.
  apply andb_true_iff in Hgate as [Hcaptures Htype_params].
  unfold no_captures_b in Hcaptures.
  destruct (fn_captures fdef) as [| capture captures] eqn:Hcaps;
    try discriminate.
  apply Nat.eqb_eq in Htype_params.
  eapply TESAssocBoundary_CallGeneric.
  - exact Hin.
  - first [reflexivity | exact Hname].
  - exact Hcaps.
  - exact Htype_params.
  - exact Hbounds.
  - eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Lemma infer_roots_direct_call_assoc_structural_boundary :
  forall fuel env Omega n fname fdef R Sigma args arg_tys T Sigma' R'
      arg_roots,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    infer_env_args_collect_roots fuel env Omega n R Sigma args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma1, R1, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma1 R1 roots1) ->
    infer_direct_call_assoc env Omega n fdef arg_tys = infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECall fname args) T Sigma' R' (root_sets_union arg_roots).
Proof.
  intros fuel env Omega n fname fdef R Sigma args arg_tys T Sigma' R'
    arg_roots Hin Hname Hcollect Hexpr Hcall.
  unfold infer_direct_call_assoc in Hcall.
  destruct (no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0)
    eqn:Hgate; try discriminate.
  destruct (build_sigma (fn_lifetimes fdef)
    (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef))
    as [sigma_acc|] eqn:Hsigma; try discriminate.
  destruct (check_args_assoc env Omega arg_tys
    (apply_lt_params (finalize_subst sigma_acc) (fn_params fdef)))
    as [err|] eqn:Hcheck; try discriminate.
  destruct (forallb (wf_lifetime_b (mk_region_ctx n))
    (finalize_subst sigma_acc)) eqn:Hwf; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)))
    eqn:Hout; try discriminate.
  inversion Hcall; subst; clear Hcall.
  apply andb_true_iff in Hgate as [Hcaptures Htype_params].
  unfold no_captures_b in Hcaptures.
  destruct (fn_captures fdef) as [| capture captures] eqn:Hcaps;
    try discriminate.
  apply Nat.eqb_eq in Htype_params.
  eapply TERAssocBoundary_Call.
  - exact Hin.
  - first [reflexivity | exact Hname].
  - exact Hcaps.
  - exact Htype_params.
  - eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Lemma infer_roots_direct_call_generic_assoc_structural_boundary :
  forall fuel env Omega n fname fdef type_args R Sigma args arg_tys T Sigma'
      R' arg_roots,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    infer_env_args_collect_roots fuel env Omega n R Sigma args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma1, R1, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma1 R1 roots1) ->
    infer_direct_call_generic_assoc env Omega n fdef type_args arg_tys =
      infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallGeneric fname type_args args) T Sigma' R'
      (root_sets_union arg_roots).
Proof.
  intros fuel env Omega n fname fdef type_args R Sigma args arg_tys T Sigma'
    R' arg_roots Hin Hname Hcollect Hexpr Hcall.
  unfold infer_direct_call_generic_assoc in Hcall.
  destruct (no_captures_b fdef &&
    Nat.eqb (Datatypes.length type_args) (fn_type_params fdef))
    eqn:Hgate; try discriminate.
  destruct (check_struct_bounds env (fn_bounds fdef) type_args)
    as [err_bounds|] eqn:Hbounds; try discriminate.
  destruct (build_sigma (fn_lifetimes fdef)
    (repeat None (fn_lifetimes fdef)) arg_tys
    (apply_type_params type_args (fn_params fdef)))
    as [sigma_acc|] eqn:Hsigma; try discriminate.
  destruct (check_args_assoc env Omega arg_tys
    (apply_lt_params (finalize_subst sigma_acc)
      (apply_type_params type_args (fn_params fdef))))
    as [err|] eqn:Hcheck; try discriminate.
  destruct (forallb (wf_lifetime_b (mk_region_ctx n))
    (finalize_subst sigma_acc)) eqn:Hwf; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)))
    eqn:Hout; try discriminate.
  inversion Hcall; subst; clear Hcall.
  apply andb_true_iff in Hgate as [Hcaptures Htype_params].
  unfold no_captures_b in Hcaptures.
  destruct (fn_captures fdef) as [| capture captures] eqn:Hcaps;
    try discriminate.
  apply Nat.eqb_eq in Htype_params.
  eapply TERAssocBoundary_CallGeneric.
  - exact Hin.
  - first [reflexivity | exact Hname].
  - exact Hcaps.
  - exact Htype_params.
  - exact Hbounds.
  - eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.


Lemma infer_env_fn_value_call_assoc_structural_boundary :
  forall fuel env Omega n callee callee_ty args arg_tys T Sigma Sigma1 Sigma',
    typed_env_structural env Omega n Sigma callee callee_ty Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_fn_value_call_assoc env Omega callee_ty arg_tys = infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExpr callee args) T Sigma'.
Proof.
  intros fuel env Omega n callee callee_ty args arg_tys T Sigma Sigma1
    Sigma' Hcallee Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_assoc_checked_args
    env Omega callee_ty arg_tys T Hcall) as
    [[param_tys [ret [Hcore [Hcheck [_ Hret]]]]] |
     [env_lt [param_tys [ret [Hcore [Hcheck [_ Hret]]]]]]].
  - destruct callee_ty as [u core]. simpl in Hcore. subst core T.
    eapply TESAssocBoundary_CallExpr_Fn.
    + exact Hcallee.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - destruct callee_ty as [u core]. simpl in Hcore. subst core T.
    eapply TESAssocBoundary_CallExpr_Closure.
    + exact Hcallee.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_roots_fn_value_call_assoc_structural_boundary :
  forall fuel env Omega n callee callee_ty R R1 Sigma Sigma1 args arg_tys T
      Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee callee_ty Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_fn_value_call_assoc env Omega callee_ty arg_tys = infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee callee_ty R R1 Sigma Sigma1 args arg_tys T
    Sigma' R' arg_roots roots_callee Hcallee Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_assoc_checked_args
    env Omega callee_ty arg_tys T Hcall) as
    [[param_tys [ret [Hcore [Hcheck [_ Hret]]]]] |
     [env_lt [param_tys [ret [Hcore [Hcheck [_ Hret]]]]]]].
  - destruct callee_ty as [u core]. simpl in Hcore. subst core T.
    eapply TERAssocBoundary_CallExpr_Fn.
    + exact Hcallee.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - destruct callee_ty as [u core]. simpl in Hcore. subst core T.
    eapply TERAssocBoundary_CallExpr_Closure.
    + exact Hcallee.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.
