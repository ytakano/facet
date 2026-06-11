From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program Renaming TypingRules TypeChecker RuntimeTyping
  RootProvenance EnvStructuralRules AlphaRootEnvFacts AlphaRoots TypeSafetyRootFacts
  TypeSafetyRootsReadyRootSets
  TypeSafetyRootsReadyCtx TypeSafetyRootsReadyMutual
  TypeSafetyCheckedRoots EnvTypingSoundness
  EnvRootSoundness AssocEnvStructural
  AssocDirectCallHelpers AssocFnValueCallHelpers
  AssocArgBoolFacts AssocFnValueCallFacts
  AssocHrtHelpers AssocHrtFacts AssocEnvArgSoundness
  AssocEnvRootArgSoundness AssocEnvHrtSoundness EnvBorrowSoundness EnvSoundnessFacts.
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

Lemma typed_env_structural_assoc_call_boundary_same_bindings :
  forall env Omega n Sigma e T Sigma',
    typed_env_structural_assoc_call_boundary env Omega n Sigma e T Sigma' ->
    sctx_same_bindings Sigma Sigma'.
Proof.
  intros env Omega n Sigma e T Sigma' Hboundary.
  destruct Hboundary.
  - eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings; eassumption.
    + eapply typed_args_env_structural_assoc_same_bindings; eassumption.
  - eapply typed_args_env_structural_assoc_same_bindings; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_same_bindings :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R' roots ->
    sctx_same_bindings Sigma Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  destruct Hboundary.
  - eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings.
      eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_same_bindings; eassumption.
  - eapply typed_args_roots_assoc_same_bindings; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_no_shadow :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow.
  destruct Hboundary; eauto using typed_env_roots_no_shadow,
    typed_args_roots_assoc_no_shadow.
Qed.

Lemma typed_env_roots_assoc_call_boundary_ctx_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Sigma ->
    root_env_ctx_keys_named R' Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hkeys.
  destruct Hboundary; eauto using typed_args_roots_assoc_ctx_keys_named.
  all: eapply typed_args_roots_assoc_ctx_keys_named; [eassumption | |];
    [eapply typed_env_roots_no_shadow; eassumption |
     eapply (proj1 (typed_roots_ctx_keys_named_mutual env Omega n));
       eassumption].
Qed.

Lemma typed_env_roots_assoc_call_boundary_sctx_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    root_env_sctx_keys_named R' Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hkeys.
  unfold root_env_sctx_keys_named, root_env_ctx_keys_named in *.
  eapply typed_env_roots_assoc_call_boundary_ctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_ctx_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Sigma ->
    root_env_ctx_roots_named R' Sigma' /\
    root_set_ctx_roots_named roots Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed.
  destruct Hboundary.
  all: try match goal with
  | |- root_env_ctx_roots_named ?ROut ?SigmaOut /\ root_set_ctx_roots_named (root_sets_union ?arg_roots) ?SigmaOut =>
      let Hargs_named := fresh "Hargs_named" in
      assert (Hargs_named :
        root_env_ctx_roots_named ROut SigmaOut /\
        Forall (fun roots => root_set_ctx_roots_named roots SigmaOut)
          arg_roots)
        by (eapply typed_args_roots_assoc_ctx_roots_named; eassumption);
      destruct Hargs_named as [Hnamed' Hroots];
      split; [exact Hnamed' | apply root_sets_ctx_roots_named_union; exact Hroots]
  end.
  all: match goal with
  | |- root_env_ctx_roots_named ?ROut ?SigmaOut /\ root_set_ctx_roots_named
          (root_set_union ?roots_callee (root_sets_union ?arg_roots)) ?SigmaOut =>
      let Hcallee_named := fresh "Hcallee_named" in
      pose proof (proj1 (typed_roots_ctx_roots_named_mutual _ _ _)
        _ _ _ _ _ _ _ ltac:(eassumption) Hshadow Hnamed) as Hcallee_named;
      destruct Hcallee_named as [Hnamed1 Hroots_callee];
      let Hshadow1 := fresh "Hshadow1" in
      assert (Hshadow1 : root_env_no_shadow _)
        by (eapply typed_env_roots_no_shadow; eassumption);
      let Hargs_named := fresh "Hargs_named" in
      assert (Hargs_named :
        root_env_ctx_roots_named ROut SigmaOut /\
        Forall (fun roots => root_set_ctx_roots_named roots SigmaOut)
          arg_roots)
        by (eapply typed_args_roots_assoc_ctx_roots_named; eassumption);
      destruct Hargs_named as [Hnamed' Hroots_args];
      split; [exact Hnamed' | apply root_set_ctx_roots_named_union;
        [eapply root_set_ctx_roots_named_same_bindings;
          [eapply typed_args_roots_assoc_same_bindings; eassumption | exact Hroots_callee]
        | apply root_sets_ctx_roots_named_union; exact Hroots_args]]
  end.
Qed.

Lemma typed_env_roots_assoc_call_boundary_sctx_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    root_env_sctx_roots_named R' Sigma' /\
    root_set_sctx_roots_named roots Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed.
  unfold root_env_sctx_roots_named, root_set_sctx_roots_named,
    root_env_ctx_roots_named, root_set_ctx_roots_named in *.
  eapply typed_env_roots_assoc_call_boundary_ctx_roots_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_store_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    store_typed env s Sigma' ->
    root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hkeys Hstore.
  eapply root_env_sctx_keys_named_store_typed.
  - exact Hstore.
  - eapply typed_env_roots_assoc_call_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_store_keys_named_prefix :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    store_typed_prefix env s Sigma' ->
    root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hkeys Hstore.
  eapply root_env_sctx_keys_named_store_typed_prefix.
  - exact Hstore.
  - eapply typed_env_roots_assoc_call_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_store_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    store_typed env s Sigma' ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hnamed Hstore.
  destruct (typed_env_roots_assoc_call_boundary_sctx_roots_named env Omega n
    R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed) as [Henv Hroots].
  split.
  - eapply root_env_sctx_roots_named_store_typed; eassumption.
  - eapply root_set_sctx_roots_named_store_typed; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_store_roots_named_prefix :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    store_typed_prefix env s Sigma' ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hnamed Hstore.
  destruct (typed_env_roots_assoc_call_boundary_sctx_roots_named env Omega n
    R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed) as [Henv Hroots].
  split.
  - eapply root_env_sctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_set_sctx_roots_named_store_typed_prefix; eassumption.
Qed.

Lemma typed_env_roots_assoc_call_boundary_structural :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R' roots ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma e T Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  destruct Hboundary.
  - eapply TESAssocBoundary_Call; eauto.
    eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallGeneric; eauto.
    eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_Fn.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_Closure.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_TypeForall; eauto.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExprGeneric_TypeForall; eauto.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_MixedForall; eauto.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_Forall; eauto.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_Forall_Closure; eauto.
    + eapply typed_env_roots_structural; eassumption.
    + eapply typed_args_roots_assoc_structural; eassumption.
  - eapply TESAssocBoundary_CallExpr_MakeClosure; eauto.
    eapply typed_args_roots_assoc_structural; eassumption.
Qed.


Inductive typed_env_structural_assoc_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TESAssocBoundary_Structural : forall Sigma e T Sigma',
      typed_env_structural env Omega n Sigma e T Sigma' ->
      typed_env_structural_assoc_boundary env Omega n Sigma e T Sigma'
  | TESAssocBoundary_CallBoundary : forall Sigma e T Sigma',
      typed_env_structural_assoc_call_boundary env Omega n Sigma e T Sigma' ->
      typed_env_structural_assoc_boundary env Omega n Sigma e T Sigma'.

Inductive typed_env_roots_assoc_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERAssocBoundary_Roots : forall R Sigma e T Sigma' R' roots,
      typed_env_roots env Omega n R Sigma e T Sigma' R' roots ->
      typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots
  | TERAssocBoundary_CallBoundary : forall R Sigma e T Sigma' R' roots,
      typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R' roots ->
      typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots.

Lemma typed_env_structural_assoc_boundary_same_bindings :
  forall env Omega n Sigma e T Sigma',
    typed_env_structural_assoc_boundary env Omega n Sigma e T Sigma' ->
    sctx_same_bindings Sigma Sigma'.
Proof.
  intros env Omega n Sigma e T Sigma' Hboundary.
  destruct Hboundary.
  - eapply typed_env_structural_same_bindings; eassumption.
  - eapply typed_env_structural_assoc_call_boundary_same_bindings; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_structural :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    typed_env_structural_assoc_boundary env Omega n Sigma e T Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  destruct Hboundary.
  - apply TESAssocBoundary_Structural.
    eapply typed_env_roots_structural; eassumption.
  - apply TESAssocBoundary_CallBoundary.
    eapply typed_env_roots_assoc_call_boundary_structural; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_same_bindings :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    sctx_same_bindings Sigma Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  eapply typed_env_structural_assoc_boundary_same_bindings.
  eapply typed_env_roots_assoc_boundary_structural. exact Hboundary.
Qed.

Lemma typed_env_roots_assoc_boundary_no_shadow :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow.
  destruct Hboundary.
  - eapply typed_env_roots_no_shadow; eassumption.
  - eapply typed_env_roots_assoc_call_boundary_no_shadow; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_ctx_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Sigma ->
    root_env_ctx_keys_named R' Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hkeys.
  destruct Hboundary.
  - eapply (proj1 (typed_roots_ctx_keys_named_mutual env Omega n));
      eassumption.
  - eapply typed_env_roots_assoc_call_boundary_ctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_sctx_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    root_env_sctx_keys_named R' Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hkeys.
  unfold root_env_sctx_keys_named, root_env_ctx_keys_named in *.
  eapply typed_env_roots_assoc_boundary_ctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_ctx_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Sigma ->
    root_env_ctx_roots_named R' Sigma' /\
    root_set_ctx_roots_named roots Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed.
  destruct Hboundary.
  - eapply (proj1 (typed_roots_ctx_roots_named_mutual env Omega n));
      eassumption.
  - eapply typed_env_roots_assoc_call_boundary_ctx_roots_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_sctx_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    root_env_sctx_roots_named R' Sigma' /\
    root_set_sctx_roots_named roots Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed.
  unfold root_env_sctx_roots_named, root_set_sctx_roots_named,
    root_env_ctx_roots_named, root_set_ctx_roots_named in *.
  eapply typed_env_roots_assoc_boundary_ctx_roots_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_store_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    store_typed env s Sigma' ->
    root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hkeys Hstore.
  eapply root_env_sctx_keys_named_store_typed.
  - exact Hstore.
  - eapply typed_env_roots_assoc_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_store_keys_named_prefix :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    store_typed_prefix env s Sigma' ->
    root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hkeys Hstore.
  eapply root_env_sctx_keys_named_store_typed_prefix.
  - exact Hstore.
  - eapply typed_env_roots_assoc_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_store_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    store_typed env s Sigma' ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hnamed Hstore.
  destruct (typed_env_roots_assoc_boundary_sctx_roots_named env Omega n
    R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed) as [Henv Hroots].
  split.
  - eapply root_env_sctx_roots_named_store_typed; eassumption.
  - eapply root_set_sctx_roots_named_store_typed; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_store_roots_named_prefix :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    store_typed_prefix env s Sigma' ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hnamed Hstore.
  destruct (typed_env_roots_assoc_boundary_sctx_roots_named env Omega n
    R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed) as [Henv Hroots].
  split.
  - eapply root_env_sctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_set_sctx_roots_named_store_typed_prefix; eassumption.
Qed.

Inductive typed_env_roots_checked_assoc_boundary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERCAssocBoundary_Checked : forall R Sigma e T Sigma' R' roots,
      typed_env_roots_checked env Omega n R Sigma e T Sigma' R' roots ->
      typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots
  | TERCAssocBoundary_RootBoundary : forall R Sigma e T Sigma' R' roots,
      typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
      typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots.

Lemma typed_env_roots_checked_assoc_boundary_structural :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    typed_env_structural_assoc_boundary env Omega n Sigma e T Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  destruct Hboundary.
  - apply TESAssocBoundary_Structural.
    eapply typed_env_roots_checked_structural. exact H.
  - eapply typed_env_roots_assoc_boundary_structural. exact H.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_same_bindings :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    sctx_same_bindings Sigma Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  eapply typed_env_structural_assoc_boundary_same_bindings.
  eapply typed_env_roots_checked_assoc_boundary_structural. exact Hboundary.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_no_shadow :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow.
  destruct Hboundary.
  - eapply typed_env_roots_checked_no_shadow; eassumption.
  - eapply typed_env_roots_assoc_boundary_no_shadow; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_ctx_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Sigma ->
    root_env_ctx_keys_named R' Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hkeys.
  destruct Hboundary.
  - eapply typed_env_roots_checked_ctx_keys_named; eassumption.
  - eapply typed_env_roots_assoc_boundary_ctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_sctx_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    root_env_sctx_keys_named R' Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hkeys.
  unfold root_env_sctx_keys_named, root_env_ctx_keys_named in *.
  eapply typed_env_roots_checked_assoc_boundary_ctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_ctx_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Sigma ->
    root_env_ctx_roots_named R' Sigma' /\
    root_set_ctx_roots_named roots Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed.
  destruct Hboundary.
  - eapply typed_env_roots_checked_ctx_roots_named; eassumption.
  - eapply typed_env_roots_assoc_boundary_ctx_roots_named; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_sctx_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    root_env_sctx_roots_named R' Sigma' /\
    root_set_sctx_roots_named roots Sigma'.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed.
  unfold root_env_sctx_roots_named, root_set_sctx_roots_named,
    root_env_ctx_roots_named, root_set_ctx_roots_named in *.
  eapply typed_env_roots_checked_assoc_boundary_ctx_roots_named; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_store_keys_named :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    store_typed env s Sigma' ->
    root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hkeys Hstore.
  eapply root_env_sctx_keys_named_store_typed.
  - exact Hstore.
  - eapply typed_env_roots_checked_assoc_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_store_keys_named_prefix :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma ->
    store_typed_prefix env s Sigma' ->
    root_env_store_keys_named R' s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hkeys Hstore.
  eapply root_env_sctx_keys_named_store_typed_prefix.
  - exact Hstore.
  - eapply typed_env_roots_checked_assoc_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_store_roots_named :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    store_typed env s Sigma' ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hnamed Hstore.
  destruct (typed_env_roots_checked_assoc_boundary_sctx_roots_named env Omega n
    R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed) as [Henv Hroots].
  split.
  - eapply root_env_sctx_roots_named_store_typed; eassumption.
  - eapply root_set_sctx_roots_named_store_typed; eassumption.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_store_roots_named_prefix :
  forall env Omega n R Sigma e T Sigma' R' roots s,
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    root_env_no_shadow R ->
    root_env_sctx_roots_named R Sigma ->
    store_typed_prefix env s Sigma' ->
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots s Hboundary Hshadow
    Hnamed Hstore.
  destruct (typed_env_roots_checked_assoc_boundary_sctx_roots_named env Omega n
    R Sigma e T Sigma' R' roots Hboundary Hshadow Hnamed) as [Henv Hroots].
  split.
  - eapply root_env_sctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_set_sctx_roots_named_store_typed_prefix; eassumption.
Qed.

Lemma typed_env_roots_assoc_boundary_of_assoc_call_boundary :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  apply TERAssocBoundary_CallBoundary. exact Hboundary.
Qed.

Lemma typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary :
  forall env Omega n R Sigma e T Sigma' R' roots,
    typed_env_roots_assoc_call_boundary env Omega n R Sigma e T Sigma' R'
      roots ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma'
      R' roots.
Proof.
  intros env Omega n R Sigma e T Sigma' R' roots Hboundary.
  apply TERCAssocBoundary_RootBoundary.
  eapply typed_env_roots_assoc_boundary_of_assoc_call_boundary.
  exact Hboundary.
Qed.

Lemma assoc_boundary_struct_expr_true : forall e,
  struct_expr e = true.
Proof.
  fix IH 1.
  intro e.
  destruct e; simpl; try reflexivity.
  - rewrite IH, IH. reflexivity.
  - rewrite IH, IH. reflexivity.
  - induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l0 as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l0 as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l1 as [| [fname field] rest IHfields]; simpl.
    + reflexivity.
    + rewrite IH, IHfields. reflexivity.
  - induction l2 as [| payload rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| [[name binders] branch] rest IHbranches]; simpl.
    + reflexivity.
    + rewrite IH, IHbranches. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, IH, IH. reflexivity.
Qed.

Theorem infer_core_env_state_fuel_struct_assoc_boundary_sound :
  forall fuel env Omega n Sigma e T Sigma',
    infer_core_env_state_fuel fuel env Omega n Sigma e =
      infer_ok (T, Sigma') ->
    typed_env_structural_assoc_boundary env Omega n Sigma e T Sigma'.
Proof.
  intros fuel env Omega n Sigma e T Sigma' Hinfer.
  apply TESAssocBoundary_Structural.
  eapply infer_core_env_state_fuel_struct_structural_sound.
  - apply assoc_boundary_struct_expr_true.
  - exact Hinfer.
Qed.

Theorem infer_core_env_struct_assoc_boundary_sound :
  forall env Omega n Gamma e T Gamma',
    infer_core_env env Omega n Gamma e = infer_ok (T, Gamma') ->
    typed_env_structural_assoc_boundary env Omega n
      (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma').
Proof.
  unfold infer_core_env, sctx_of_ctx, ctx_of_sctx.
  intros env Omega n Gamma e T Gamma' Hinfer.
  destruct (infer_core_env_state_fuel 10000 env Omega n Gamma e)
    as [[T0 Sigma] | err] eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_struct_assoc_boundary_sound. exact Hcore.
Qed.

Definition typed_fn_env_structural_assoc_boundary
    (env : global_env) (f : fn_def) : Prop :=
  exists T_body Gamma_out,
    typed_env_structural_assoc_boundary
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Gamma_out = true.

Definition env_fns_typed_structural_assoc_boundary
    (env : global_env) : Prop :=
  forall f, In f (env_fns env) ->
    typed_fn_env_structural_assoc_boundary env f.

Definition checked_fn_env_structural_assoc_boundary
    (env : global_env) (f : fn_def) : Prop :=
  typed_fn_env_structural_assoc_boundary env f /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

Definition env_fns_checked_structural_assoc_boundary
    (env : global_env) : Prop :=
  forall f, In f (env_fns env) ->
    checked_fn_env_structural_assoc_boundary env f.

Lemma checked_fn_env_structural_assoc_boundary_typed :
  forall env f,
    checked_fn_env_structural_assoc_boundary env f ->
    typed_fn_env_structural_assoc_boundary env f.
Proof.
  intros env f Hchecked.
  exact (proj1 Hchecked).
Qed.

Lemma typed_fn_env_structural_assoc_boundary_same_bindings :
  forall env f T_body Gamma_out,
    typed_env_structural_assoc_boundary
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) ->
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx f)) (sctx_of_ctx Gamma_out).
Proof.
  intros env f T_body Gamma_out Hbody.
  eapply typed_env_structural_assoc_boundary_same_bindings.
  exact Hbody.
Qed.

Definition typed_fn_env_roots_assoc_boundary
    (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Gamma_out,
    typed_env_roots_assoc_boundary
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Gamma_out = true.

Definition checked_fn_env_roots_assoc_boundary
    (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  typed_fn_env_roots_assoc_boundary env f R0 R_out roots /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

Lemma typed_fn_env_roots_assoc_boundary_sctx_keys_named :
  forall env f R0 R_out roots,
    typed_fn_env_roots_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_assoc_boundary.
  intros env f R0 R_out roots Htyped Hshadow Hkeys.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  repeat split; try assumption.
  eapply typed_env_roots_assoc_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_fn_env_roots_assoc_boundary_sctx_roots_named :
  forall env f R0 R_out roots,
    typed_fn_env_roots_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_out) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_assoc_boundary.
  intros env f R0 R_out roots Htyped Hshadow Hnamed.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  destruct (typed_env_roots_assoc_boundary_sctx_roots_named
    (global_env_with_local_bounds env (fn_bounds f))
    (fn_outlives f) (fn_lifetimes f) R0 (sctx_of_ctx (fn_body_ctx f))
    (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots Hbody
    Hshadow Hnamed) as [Henv Hroots].
  repeat split; assumption.
Qed.

Definition typed_fn_env_roots_checked_assoc_boundary
    (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Gamma_out,
    typed_env_roots_checked_assoc_boundary
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Gamma_out = true.

Definition checked_fn_env_roots_checked_assoc_boundary
    (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

Lemma checked_fn_env_roots_assoc_boundary_typed :
  forall env f R0 R_out roots,
    checked_fn_env_roots_assoc_boundary env f R0 R_out roots ->
    typed_fn_env_roots_assoc_boundary env f R0 R_out roots.
Proof.
  intros env f R0 R_out roots Hchecked.
  exact (proj1 Hchecked).
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_typed :
  forall env f R0 R_out roots,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots.
Proof.
  intros env f R0 R_out roots Hchecked.
  exact (proj1 Hchecked).
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_sctx_keys_named :
  forall env f R0 R_out roots,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots Htyped Hshadow Hkeys.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  repeat split; try assumption.
  eapply typed_env_roots_checked_assoc_boundary_sctx_keys_named; eassumption.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_sctx_roots_named :
  forall env f R0 R_out roots,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_out) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots Htyped Hshadow Hnamed.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  destruct (typed_env_roots_checked_assoc_boundary_sctx_roots_named
    (global_env_with_local_bounds env (fn_bounds f))
    (fn_outlives f) (fn_lifetimes f) R0 (sctx_of_ctx (fn_body_ctx f))
    (fn_body f) T_body (sctx_of_ctx Gamma_out) R_out roots Hbody
    Hshadow Hnamed) as [Henv Hroots].
  repeat split; assumption.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_sctx_keys_named :
  forall env f R0 R_out roots,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots Hchecked Hshadow Hkeys.
  eapply typed_fn_env_roots_checked_assoc_boundary_sctx_keys_named.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hkeys.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_sctx_roots_named :
  forall env f R0 R_out roots,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_out) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots Hchecked Hshadow Hnamed.
  eapply typed_fn_env_roots_checked_assoc_boundary_sctx_roots_named.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hnamed.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_store_keys_named :
  forall env f R0 R_out roots s,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots s Htyped Hshadow Hkeys.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  split.
  - intros Hstore.
    eapply typed_env_roots_checked_assoc_boundary_store_keys_named; eassumption.
  - split; assumption.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_store_keys_named_prefix :
  forall env f R0 R_out roots s,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots s Htyped Hshadow Hkeys.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  split.
  - intros Hstore.
    eapply typed_env_roots_checked_assoc_boundary_store_keys_named_prefix;
      eassumption.
  - split; assumption.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_store_roots_named :
  forall env f R0 R_out roots s,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots s Htyped Hshadow Hnamed.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  split.
  - intros Hstore.
    eapply typed_env_roots_checked_assoc_boundary_store_roots_named; eassumption.
  - split; assumption.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_store_roots_named_prefix :
  forall env f R0 R_out roots s,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots s Htyped Hshadow Hnamed.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  split.
  - intros Hstore.
    eapply typed_env_roots_checked_assoc_boundary_store_roots_named_prefix;
      eassumption.
  - split; assumption.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_store_named :
  forall env f R0 R_out roots s,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s /\
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots s Htyped Hshadow Hkeys Hroots.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  split.
  - intros Hstore.
    split.
    + eapply typed_env_roots_checked_assoc_boundary_store_keys_named;
        eassumption.
    + eapply typed_env_roots_checked_assoc_boundary_store_roots_named;
        eassumption.
  - split; assumption.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_store_named_prefix :
  forall env f R0 R_out roots s,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s /\
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots s Htyped Hshadow Hkeys Hroots.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  split.
  - intros Hstore.
    split.
    + eapply typed_env_roots_checked_assoc_boundary_store_keys_named_prefix;
        eassumption.
    + eapply typed_env_roots_checked_assoc_boundary_store_roots_named_prefix;
        eassumption.
  - split; assumption.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_store_keys_named :
  forall env f R0 R_out roots s,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots s Hchecked Hshadow Hkeys.
  eapply typed_fn_env_roots_checked_assoc_boundary_store_keys_named.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hkeys.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_store_keys_named_prefix :
  forall env f R0 R_out roots s,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots s Hchecked Hshadow Hkeys.
  eapply typed_fn_env_roots_checked_assoc_boundary_store_keys_named_prefix.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hkeys.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_store_roots_named :
  forall env f R0 R_out roots s,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots s Hchecked Hshadow Hnamed.
  eapply typed_fn_env_roots_checked_assoc_boundary_store_roots_named.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hnamed.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_store_roots_named_prefix :
  forall env f R0 R_out roots s,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots s Hchecked Hshadow Hnamed.
  eapply typed_fn_env_roots_checked_assoc_boundary_store_roots_named_prefix.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hnamed.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_store_named :
  forall env f R0 R_out roots s,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s /\
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots s Hchecked Hshadow Hkeys Hroots.
  eapply typed_fn_env_roots_checked_assoc_boundary_store_named.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hkeys.
  - exact Hroots.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_store_named_prefix :
  forall env f R0 R_out roots s,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_out,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_out) ->
       root_env_store_keys_named R_out s /\
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_out = true.
Proof.
  intros env f R0 R_out roots s Hchecked Hshadow Hkeys Hroots.
  eapply typed_fn_env_roots_checked_assoc_boundary_store_named_prefix.
  - eapply checked_fn_env_roots_checked_assoc_boundary_typed. exact Hchecked.
  - exact Hshadow.
  - exact Hkeys.
  - exact Hroots.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_structural :
  forall env f R0 R_out roots,
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    typed_fn_env_structural_assoc_boundary env f.
Proof.
  unfold typed_fn_env_roots_checked_assoc_boundary,
    typed_fn_env_structural_assoc_boundary.
  intros env f R0 R_out roots Htyped.
  destruct Htyped as [T_body [Gamma_out [Hbody [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  repeat split; try assumption.
  eapply typed_env_roots_checked_assoc_boundary_structural.
  exact Hbody.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_structural :
  forall env f R0 R_out roots,
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots ->
    checked_fn_env_structural_assoc_boundary env f.
Proof.
  unfold checked_fn_env_roots_checked_assoc_boundary,
    checked_fn_env_structural_assoc_boundary.
  intros env f R0 R_out roots Hchecked.
  destruct Hchecked as [Htyped [Hborrow Hnodup]].
  repeat split; try assumption.
  eapply typed_fn_env_roots_checked_assoc_boundary_structural.
  exact Htyped.
Qed.

Lemma typed_fn_env_roots_checked_assoc_boundary_of_checked :
  forall env f R0 R_out roots,
    typed_fn_env_roots_checked env f R0 R_out roots ->
    typed_fn_env_roots_checked_assoc_boundary env f R0 R_out roots.
Proof.
  unfold typed_fn_env_roots_checked,
    typed_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots Htyped.
  destruct Htyped as [T_body [Gamma_out [Htyped [Hcompat Hparams]]]].
  exists T_body, Gamma_out.
  repeat split; try assumption.
  apply TERCAssocBoundary_Checked. exact Htyped.
Qed.

Lemma checked_fn_env_roots_checked_assoc_boundary_of_checked :
  forall env f R0 R_out roots,
    checked_fn_env_roots_checked env f R0 R_out roots ->
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots.
Proof.
  unfold checked_fn_env_roots_checked,
    checked_fn_env_roots_checked_assoc_boundary.
  intros env f R0 R_out roots Hchecked.
  destruct Hchecked as [Htyped [Hborrow Hnodup]].
  repeat split; try assumption.
  eapply typed_fn_env_roots_checked_assoc_boundary_of_checked. exact Htyped.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_sound :
  forall env f R0 T Gamma_out R_out roots,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    checked_fn_env_roots_checked_assoc_boundary env f R0 R_out roots.
Proof.
  intros env f R0 T Gamma_out R_out roots Hinfer.
  eapply checked_fn_env_roots_checked_assoc_boundary_of_checked.
  eapply infer_full_env_roots_checked_sound. exact Hinfer.
Qed.

Lemma initial_root_env_for_params_sctx_keys_named :
  forall ps,
    root_env_sctx_keys_named
      (initial_root_env_for_params ps)
      (sctx_of_ctx (params_ctx ps)).
Proof.
  intros ps.
  unfold initial_root_env_for_params.
  apply initial_root_env_for_params_origin_sctx_keys_named.
  reflexivity.
Qed.

Lemma initial_root_env_for_params_sctx_roots_named :
  forall ps,
    root_env_sctx_roots_named
      (initial_root_env_for_params ps)
      (sctx_of_ctx (params_ctx ps)).
Proof.
  intros ps.
  unfold initial_root_env_for_params.
  apply initial_root_env_for_params_origin_sctx_roots_named.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_sctx_keys_named :
  forall env f R0 T Gamma_out R_out roots,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_body,
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f R0 T Gamma_out R_out roots Hinfer Hshadow Hkeys.
  eapply checked_fn_env_roots_checked_assoc_boundary_sctx_keys_named.
  - eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hinfer.
  - exact Hshadow.
  - exact Hkeys.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_sctx_roots_named :
  forall env f R0 T Gamma_out R_out roots,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_body,
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_body) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f R0 T Gamma_out R_out roots Hinfer Hshadow Hnamed.
  eapply checked_fn_env_roots_checked_assoc_boundary_sctx_roots_named.
  - eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hinfer.
  - exact Hshadow.
  - exact Hnamed.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_store_keys_named :
  forall env f R0 T Gamma_out R_out roots s,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_body,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f R0 T Gamma_out R_out roots s Hinfer Hshadow Hkeys.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_keys_named.
  - eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hinfer.
  - exact Hshadow.
  - exact Hkeys.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_store_keys_named_prefix :
  forall env f R0 T Gamma_out R_out roots s,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow R0 ->
    root_env_sctx_keys_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_body,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f R0 T Gamma_out R_out roots s Hinfer Hshadow Hkeys.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_keys_named_prefix.
  - eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hinfer.
  - exact Hshadow.
  - exact Hkeys.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_store_roots_named :
  forall env f R0 T Gamma_out R_out roots s,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_body,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f R0 T Gamma_out R_out roots s Hinfer Hshadow Hnamed.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_roots_named.
  - eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hinfer.
  - exact Hshadow.
  - exact Hnamed.
Qed.

Theorem infer_full_env_roots_checked_assoc_boundary_store_roots_named_prefix :
  forall env f R0 T Gamma_out R_out roots s,
    infer_full_env_roots_checked env f R0 =
      infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow R0 ->
    root_env_sctx_roots_named R0 (sctx_of_ctx (fn_body_ctx f)) ->
    exists T_body Gamma_body,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f R0 T Gamma_out R_out roots s Hinfer Hshadow Hnamed.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_roots_named_prefix.
  - eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hinfer.
  - exact Hshadow.
  - exact Hnamed.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_sound :
  forall env f T Gamma_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    checked_fn_env_roots_checked_assoc_boundary env f
      (initial_root_env_for_params (fn_params f ++ fn_captures f))
      R_out roots.
Proof.
  intros env f T Gamma_out R_out roots Hend.
  unfold infer_fn_env_end2end in Hend.
  remember (initial_root_env_for_params (fn_params f ++ fn_captures f))
    as R0 eqn:HR0.
  destruct (infer_full_env_roots_checked env f R0)
    as [[[[T0 Gamma0] R0_out] roots0] | err] eqn:Hroots; try discriminate.
  destruct (check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
              env f);
    try discriminate.
  injection Hend as <- <- <- <-.
  subst R0.
  eapply infer_full_env_roots_checked_assoc_boundary_sound. exact Hroots.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_sctx_keys_named :
  forall env f T Gamma_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T_body Gamma_body,
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f T Gamma_out R_out roots Hend Hshadow.
  eapply checked_fn_env_roots_checked_assoc_boundary_sctx_keys_named.
  - eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
  - exact Hshadow.
  - unfold fn_body_ctx, fn_body_params.
    apply initial_root_env_for_params_sctx_keys_named.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_sctx_roots_named :
  forall env f T Gamma_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T_body Gamma_body,
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_body) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f T Gamma_out R_out roots Hend Hshadow.
  eapply checked_fn_env_roots_checked_assoc_boundary_sctx_roots_named.
  - eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
  - exact Hshadow.
  - unfold fn_body_ctx, fn_body_params.
    apply initial_root_env_for_params_sctx_roots_named.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_store_keys_named :
  forall env f T Gamma_out R_out roots s,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T_body Gamma_body,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f T Gamma_out R_out roots s Hend Hshadow.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_keys_named.
  - eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
  - exact Hshadow.
  - unfold fn_body_ctx, fn_body_params.
    apply initial_root_env_for_params_sctx_keys_named.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_store_keys_named_prefix :
  forall env f T Gamma_out R_out roots s,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T_body Gamma_body,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f T Gamma_out R_out roots s Hend Hshadow.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_keys_named_prefix.
  - eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
  - exact Hshadow.
  - unfold fn_body_ctx, fn_body_params.
    apply initial_root_env_for_params_sctx_keys_named.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_store_roots_named :
  forall env f T Gamma_out R_out roots s,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T_body Gamma_body,
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f T Gamma_out R_out roots s Hend Hshadow.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_roots_named.
  - eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
  - exact Hshadow.
  - unfold fn_body_ctx, fn_body_params.
    apply initial_root_env_for_params_sctx_roots_named.
Qed.

Theorem infer_fn_env_end2end_assoc_boundary_store_roots_named_prefix :
  forall env f T Gamma_out R_out roots s,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T_body Gamma_body,
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env f T Gamma_out R_out roots s Hend Hshadow.
  eapply checked_fn_env_roots_checked_assoc_boundary_store_roots_named_prefix.
  - eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
  - exact Hshadow.
  - unfold fn_body_ctx, fn_body_params.
    apply initial_root_env_for_params_sctx_roots_named.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_sound :
  forall env fns f,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    exists T Gamma_out R_out roots,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env fns.
  induction fns as [| f0 rest IH]; intros f Hinfer Hin.
  - contradiction.
  - simpl in Hinfer, Hin.
    destruct (infer_fn_env_end2end env f0)
      as [[[[T0 Gamma0] R0_out] roots0] | err] eqn:Hhead; try discriminate.
    destruct Hin as [Heq | Hin].
    + subst f0.
      exists T0, Gamma0, R0_out, roots0. split.
      * exact Hhead.
      * eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hhead.
    + eapply IH; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_sound :
  forall env env' f,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Gamma_out R_out roots,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f Hprog Hin.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_sound; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_sound :
  forall env env' f,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    exists T Gamma_out R_out roots,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      checked_fn_env_roots_checked_assoc_boundary env' f
        (initial_root_env_for_params (fn_params f ++ fn_captures f))
        R_out roots.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_assoc_boundary_sound; eauto.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_sctx_keys_named :
  forall env fns f,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env fns f Hfns Hin Hshadow.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend _]]]]].
  destruct (infer_fn_env_end2end_assoc_boundary_sctx_keys_named
      env f T Gamma_out R_out roots Hend Hshadow)
    as [T_body [Gamma_body [Hkeys [Hcompat Hparams]]]].
  exists T, Gamma_out, R_out, roots, T_body, Gamma_body.
  repeat split; assumption.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_sctx_roots_named :
  forall env fns f,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_body) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env fns f Hfns Hin Hshadow.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend _]]]]].
  destruct (infer_fn_env_end2end_assoc_boundary_sctx_roots_named
      env f T Gamma_out R_out roots Hend Hshadow)
    as [T_body [Gamma_body [Henv [Hroots [Hcompat Hparams]]]]].
  exists T, Gamma_out, R_out, roots, T_body, Gamma_body.
  repeat split; assumption.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_sctx_keys_named :
  forall env env' f,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f Hprog Hin Hshadow.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_sctx_keys_named; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_sctx_roots_named :
  forall env env' f,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_body) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f Hprog Hin Hshadow.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_sctx_roots_named; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_sctx_keys_named :
  forall env env' f,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      root_env_sctx_keys_named R_out (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f _ Hprog Hin Hshadow.
  eapply infer_program_env_end2end_assoc_boundary_sctx_keys_named; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_sctx_roots_named :
  forall env env' f,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      root_env_sctx_roots_named R_out (sctx_of_ctx Gamma_body) /\
      root_set_sctx_roots_named roots (sctx_of_ctx Gamma_body) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f _ Hprog Hin Hshadow.
  eapply infer_program_env_end2end_assoc_boundary_sctx_roots_named; eauto.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_store_keys_named :
  forall env fns f s,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env fns f s Hfns Hin Hshadow.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend _]]]]].
  destruct (infer_fn_env_end2end_assoc_boundary_store_keys_named
      env f T Gamma_out R_out roots s Hend Hshadow)
    as [T_body [Gamma_body [Hkeys [Hcompat Hparams]]]].
  exists T, Gamma_out, R_out, roots, T_body, Gamma_body.
  split; [exact Hend |].
  split; [exact Hkeys |].
  split; assumption.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_store_keys_named_prefix :
  forall env fns f s,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env fns f s Hfns Hin Hshadow.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend _]]]]].
  destruct (infer_fn_env_end2end_assoc_boundary_store_keys_named_prefix
      env f T Gamma_out R_out roots s Hend Hshadow)
    as [T_body [Gamma_body [Hkeys [Hcompat Hparams]]]].
  exists T, Gamma_out, R_out, roots, T_body, Gamma_body.
  split; [exact Hend |].
  split; [exact Hkeys |].
  split; assumption.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_store_roots_named :
  forall env fns f s,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env fns f s Hfns Hin Hshadow.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend _]]]]].
  destruct (infer_fn_env_end2end_assoc_boundary_store_roots_named
      env f T Gamma_out R_out roots s Hend Hshadow)
    as [T_body [Gamma_body [Hroots [Hcompat Hparams]]]].
  exists T, Gamma_out, R_out, roots, T_body, Gamma_body.
  split; [exact Hend |].
  split; [exact Hroots |].
  split; assumption.
Qed.

Lemma infer_fns_env_end2end_in_assoc_boundary_store_roots_named_prefix :
  forall env fns f s,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed_prefix (global_env_with_local_bounds env (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Gamma_body = true.
Proof.
  intros env fns f s Hfns Hin Hshadow.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend _]]]]].
  destruct (infer_fn_env_end2end_assoc_boundary_store_roots_named_prefix
      env f T Gamma_out R_out roots s Hend Hshadow)
    as [T_body [Gamma_body [Hroots [Hcompat Hparams]]]].
  exists T, Gamma_out, R_out, roots, T_body, Gamma_body.
  split; [exact Hend |].
  split; [exact Hroots |].
  split; assumption.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_store_keys_named :
  forall env env' f s,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s Hprog Hin Hshadow.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_store_keys_named; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_store_keys_named_prefix :
  forall env env' f s,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed_prefix (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s Hprog Hin Hshadow.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_store_keys_named_prefix; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_store_roots_named :
  forall env env' f s,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s Hprog Hin Hshadow.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_store_roots_named; eauto.
Qed.

Theorem infer_program_env_end2end_assoc_boundary_store_roots_named_prefix :
  forall env env' f s,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed_prefix (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s Hprog Hin Hshadow.
  unfold infer_program_env_end2end in Hprog.
  set (env_alpha := alpha_normalize_global_env env) in *.
  destruct (global_names_unique_b env_alpha) eqn:Hunique; try discriminate.
  destruct (infer_program_env_alpha_elab env) as [env_elab | err] eqn:Helab;
    try discriminate.
  destruct (infer_fns_env_end2end env_elab (env_fns env_elab))
    as [[] | err] eqn:Hfns; try discriminate.
  inversion Hprog; subst env'.
  eapply infer_fns_env_end2end_in_assoc_boundary_store_roots_named_prefix; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_store_keys_named :
  forall env env' f s,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s _ Hprog Hin Hshadow.
  eapply infer_program_env_end2end_assoc_boundary_store_keys_named; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_store_keys_named_prefix :
  forall env env' f s,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed_prefix (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_keys_named R_out s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s _ Hprog Hin Hshadow.
  eapply infer_program_env_end2end_assoc_boundary_store_keys_named_prefix; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_store_roots_named :
  forall env env' f s,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s _ Hprog Hin Hshadow.
  eapply infer_program_env_end2end_assoc_boundary_store_roots_named; eauto.
Qed.

Theorem check_program_env_end2end_assoc_boundary_store_roots_named_prefix :
  forall env env' f s,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    root_env_no_shadow
      (initial_root_env_for_params (fn_params f ++ fn_captures f)) ->
    exists T Gamma_out R_out roots T_body Gamma_body,
      infer_fn_env_end2end env' f = infer_ok (T, Gamma_out, R_out, roots) /\
      (store_typed_prefix (global_env_with_local_bounds env' (fn_bounds f)) s
         (sctx_of_ctx Gamma_body) ->
       root_env_store_roots_named R_out s /\
       root_set_store_roots_named roots s) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env' (fn_params f) Gamma_body = true.
Proof.
  intros env env' f s _ Hprog Hin Hshadow.
  eapply infer_program_env_end2end_assoc_boundary_store_roots_named_prefix; eauto.
Qed.

Theorem infer_fn_env_end2end_structural_assoc_boundary_sound :
  forall env f T Gamma_out R_out roots,
    infer_fn_env_end2end env f = infer_ok (T, Gamma_out, R_out, roots) ->
    checked_fn_env_structural_assoc_boundary env f.
Proof.
  intros env f T Gamma_out R_out roots Hend.
  eapply checked_fn_env_roots_checked_assoc_boundary_structural.
  eapply infer_fn_env_end2end_assoc_boundary_sound. exact Hend.
Qed.

Lemma infer_fns_env_end2end_in_structural_assoc_boundary_sound :
  forall env fns f,
    infer_fns_env_end2end env fns = infer_ok tt ->
    In f fns ->
    checked_fn_env_structural_assoc_boundary env f.
Proof.
  intros env fns f Hfns Hin.
  destruct (infer_fns_env_end2end_in_assoc_boundary_sound env fns f Hfns Hin)
    as [T [Gamma_out [R_out [roots [Hend Hchecked]]]]].
  eapply checked_fn_env_roots_checked_assoc_boundary_structural.
  exact Hchecked.
Qed.

Theorem infer_program_env_end2end_structural_assoc_boundary_sound :
  forall env env' f,
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    checked_fn_env_structural_assoc_boundary env' f.
Proof.
  intros env env' f Hprog Hin.
  destruct (infer_program_env_end2end_assoc_boundary_sound env env' f Hprog Hin)
    as [T [Gamma_out [R_out [roots [Hend Hchecked]]]]].
  eapply checked_fn_env_roots_checked_assoc_boundary_structural.
  exact Hchecked.
Qed.

Theorem check_program_env_end2end_structural_assoc_boundary_sound :
  forall env env' f,
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    In f (env_fns env') ->
    checked_fn_env_structural_assoc_boundary env' f.
Proof.
  intros env env' f _ Hprog Hin.
  eapply infer_program_env_end2end_structural_assoc_boundary_sound; eauto.
Qed.

Theorem infer_program_env_end2end_env_fns_checked_structural_assoc_boundary_sound :
  forall env env',
    infer_program_env_end2end env = infer_ok env' ->
    env_fns_checked_structural_assoc_boundary env'.
Proof.
  unfold env_fns_checked_structural_assoc_boundary.
  intros env env' Hprog f Hin.
  eapply infer_program_env_end2end_structural_assoc_boundary_sound; eauto.
Qed.

Theorem check_program_env_end2end_env_fns_checked_structural_assoc_boundary_sound :
  forall env env',
    check_program_env_end2end env = true ->
    infer_program_env_end2end env = infer_ok env' ->
    env_fns_checked_structural_assoc_boundary env'.
Proof.
  intros env env' _ Hprog.
  eapply infer_program_env_end2end_env_fns_checked_structural_assoc_boundary_sound.
  exact Hprog.
Qed.

Theorem infer_env_roots_assoc_boundary_sound :
  forall env f R0 T Gamma_out R_out roots,
    infer_env_roots env f R0 = infer_ok (T, Gamma_out, R_out, roots) ->
    typed_fn_env_roots_assoc_boundary env f R0 R_out roots.
Proof.
  unfold infer_env_roots, typed_fn_env_roots_assoc_boundary.
  intros env f R0 T Gamma_out R_out roots Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env_roots (global_env_with_local_bounds env (fn_bounds f))
              (fn_outlives f) (fn_lifetimes f) R0 (fn_body_ctx f)
              (fn_body f))
    as [[[[T_body Gamma_body] R_body] roots_body] | err] eqn:Hcore;
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompatible; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Gamma_body) eqn:Hparams;
    try discriminate.
  inversion Hinfer; subst.
  exists T_body, Gamma_out.
  repeat split.
  - apply TERAssocBoundary_Roots.
    eapply infer_core_env_roots_sound. exact Hcore.
  - exact Hcompatible.
  - exact Hparams.
Qed.

Theorem infer_full_env_roots_assoc_boundary_sound :
  forall env f R0 T Gamma_out R_out roots,
    infer_full_env_roots env f R0 = infer_ok (T, Gamma_out, R_out, roots) ->
    checked_fn_env_roots_assoc_boundary env f R0 R_out roots.
Proof.
  unfold infer_full_env_roots, checked_fn_env_roots_assoc_boundary.
  intros env f R0 T Gamma_out R_out roots Hfull.
  destruct (infer_env_roots env f R0)
    as [[[[T0 Gamma0] R1] roots1] | err] eqn:Hinfer; try discriminate.
  destruct (borrow_check_env env [] (fn_body_ctx f) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  inversion Hfull; subst.
  split.
  - eapply infer_env_roots_assoc_boundary_sound. exact Hinfer.
  - split.
    + exists PBS'. eapply borrow_check_env_structural_sound. exact Hborrow.
    + eapply infer_env_roots_params_nodup. exact Hinfer.
Qed.


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

Lemma infer_env_fn_value_call_generic_assoc_structural_boundary :
  forall fuel env Omega n callee callee_ty type_args args arg_tys T Sigma
      Sigma1 Sigma_out,
    typed_env_structural env Omega n Sigma callee callee_ty Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma_out) ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_fn_value_call_generic_assoc env Omega callee_ty type_args arg_tys =
      infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExprGeneric callee type_args args) T Sigma_out.
Proof.
  intros fuel env Omega n callee callee_ty type_args args arg_tys T Sigma
    Sigma1 Sigma_out Hcallee Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_generic_assoc_checked_args
    env Omega callee_ty type_args arg_tys T Hcall) as
    [type_params [bounds [body [param_tys [ret
      [Hcore [Hbody [Hbounds [Hcheck [_ Hret]]]]]]]]]].
  destruct callee_ty as [u core]. simpl in Hcore. subst core T.
  eapply TESAssocBoundary_CallExprGeneric_TypeForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_roots_fn_value_call_generic_assoc_structural_boundary :
  forall fuel env Omega n callee callee_ty type_args R R1 Sigma Sigma1 args
      arg_tys T Sigma_out R_out arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee callee_ty Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma_out, R_out, arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_fn_value_call_generic_assoc env Omega callee_ty type_args arg_tys =
      infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExprGeneric callee type_args args) T Sigma_out R_out
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee callee_ty type_args R R1 Sigma Sigma1 args
    arg_tys T Sigma_out R_out arg_roots roots_callee Hcallee Hcollect Hexpr Hcall.
  destruct (infer_fn_value_call_generic_assoc_checked_args
    env Omega callee_ty type_args arg_tys T Hcall) as
    [type_params [bounds [body [param_tys [ret
      [Hcore [Hbody [Hbounds [Hcheck [_ Hret]]]]]]]]]].
  destruct callee_ty as [u core]. simpl in Hcore. subst core T.
  eapply TERAssocBoundary_CallExprGeneric_TypeForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.


Lemma infer_roots_direct_call_checked_assoc_boundary :
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
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECall fname args) T Sigma' R' (root_sets_union arg_roots).
Proof.
  intros fuel env Omega n fname fdef R Sigma args arg_tys T Sigma' R'
    arg_roots Hin Hname Hcollect Hexpr Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_direct_call_assoc_structural_boundary; eassumption.
Qed.

Lemma infer_roots_direct_call_generic_checked_assoc_boundary :
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
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallGeneric fname type_args args) T Sigma' R'
      (root_sets_union arg_roots).
Proof.
  intros fuel env Omega n fname fdef type_args R Sigma args arg_tys T Sigma'
    R' arg_roots Hin Hname Hcollect Hexpr Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_direct_call_generic_assoc_structural_boundary;
    eassumption.
Qed.

Lemma infer_roots_fn_value_call_checked_assoc_boundary :
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
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee callee_ty R R1 Sigma Sigma1 args arg_tys T
    Sigma' R' arg_roots roots_callee Hcallee Hcollect Hexpr Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_fn_value_call_assoc_structural_boundary; eassumption.
Qed.

Lemma infer_roots_fn_value_call_generic_checked_assoc_boundary :
  forall fuel env Omega n callee callee_ty type_args R R1 Sigma Sigma1 args
      arg_tys T Sigma_out R_out arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee callee_ty Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma_out, R_out, arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_fn_value_call_generic_assoc env Omega callee_ty type_args arg_tys =
      infer_ok T ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallExprGeneric callee type_args args) T Sigma_out R_out
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee callee_ty type_args R R1 Sigma Sigma1 args
    arg_tys T Sigma_out R_out arg_roots roots_callee Hcallee Hcollect Hexpr
    Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_fn_value_call_generic_assoc_structural_boundary;
    eassumption.
Qed.


Lemma infer_env_type_forall_assoc_structural_boundary :
  forall fuel env Omega n callee u type_params bounds body args arg_tys T
      Sigma Sigma1 Sigma',
    typed_env_structural env Omega n Sigma callee
      (MkTy u (TTypeForall type_params bounds body)) Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_type_forall_call_env_assoc env Omega type_params bounds body arg_tys =
      infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExpr callee args) T Sigma'.
Proof.
  intros fuel env Omega n callee u type_params bounds body args arg_tys T
    Sigma Sigma1 Sigma' Hcallee Hcollect Hexpr Hcall.
  destruct (infer_type_forall_call_env_assoc_checked_args
    env Omega type_params bounds body arg_tys T Hcall) as
    [type_args [param_tys [ret
      [Hbody [Htype_args [Hbounds [Hcheck _]]]]]]].
  unfold infer_type_forall_call_env_assoc in Hcall.
  rewrite Hbody, Htype_args, Hbounds, Hcheck in Hcall.
  inversion Hcall; subst; clear Hcall.
  eapply TESAssocBoundary_CallExpr_TypeForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_type_forall_elab_assoc_structural_boundary :
  forall fuel env Omega n callee u type_params bounds body args arg_tys
      type_args_ret Sigma Sigma1 Sigma',
    typed_env_structural env Omega n Sigma callee
      (MkTy u (TTypeForall type_params bounds body)) Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_type_forall_call_env_elab_assoc
      env Omega type_params bounds body arg_tys = infer_ok type_args_ret ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExpr callee args) (snd type_args_ret) Sigma'.
Proof.
  intros fuel env Omega n callee u type_params bounds body args arg_tys
    type_args_ret Sigma Sigma1 Sigma' Hcallee Hcollect Hexpr Hcall.
  destruct (infer_type_forall_call_env_elab_assoc_checked_args
    env Omega type_params bounds body arg_tys type_args_ret Hcall) as
    [type_args [param_tys [ret
      [Hbody [Htype_args [Hbounds [Hcheck _]]]]]]].
  unfold infer_type_forall_call_env_elab_assoc in Hcall.
  rewrite Hbody, Htype_args, Hbounds, Hcheck in Hcall.
  inversion Hcall; subst; clear Hcall; simpl.
  eapply TESAssocBoundary_CallExpr_TypeForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
Qed.

Lemma infer_roots_type_forall_assoc_structural_boundary :
  forall fuel env Omega n callee u type_params bounds body R R1 Sigma Sigma1
      args arg_tys T Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TTypeForall type_params bounds body)) Sigma1 R1 roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_type_forall_call_env_assoc env Omega type_params bounds body arg_tys =
      infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u type_params bounds body R R1 Sigma Sigma1
    args arg_tys T Sigma' R' arg_roots roots_callee Hcallee Hcollect Hexpr
    Hcall.
  destruct (infer_type_forall_call_env_assoc_checked_args
    env Omega type_params bounds body arg_tys T Hcall) as
    [type_args [param_tys [ret
      [Hbody [Htype_args [Hbounds [Hcheck _]]]]]]].
  unfold infer_type_forall_call_env_assoc in Hcall.
  rewrite Hbody, Htype_args, Hbounds, Hcheck in Hcall.
  inversion Hcall; subst; clear Hcall.
  eapply TERAssocBoundary_CallExpr_TypeForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_roots_type_forall_checked_assoc_boundary :
  forall fuel env Omega n callee u type_params bounds body R R1 Sigma Sigma1
      args arg_tys T Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TTypeForall type_params bounds body)) Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_type_forall_call_env_assoc env Omega type_params bounds body arg_tys =
      infer_ok T ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u type_params bounds body R R1 Sigma Sigma1
    args arg_tys T Sigma' R' arg_roots roots_callee Hcallee Hcollect Hexpr
    Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_type_forall_assoc_structural_boundary; eassumption.
Qed.


Lemma infer_roots_type_forall_elab_assoc_structural_boundary :
  forall fuel env Omega n callee u type_params bounds body R R1 Sigma Sigma1
      args arg_tys type_args_ret Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TTypeForall type_params bounds body)) Sigma1 R1 roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_type_forall_call_env_elab_assoc
      env Omega type_params bounds body arg_tys = infer_ok type_args_ret ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExpr callee args) (snd type_args_ret) Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u type_params bounds body R R1 Sigma Sigma1
    args arg_tys type_args_ret Sigma' R' arg_roots roots_callee Hcallee
    Hcollect Hexpr Hcall.
  destruct (infer_type_forall_call_env_elab_assoc_checked_args
    env Omega type_params bounds body arg_tys type_args_ret Hcall) as
    [type_args [param_tys [ret
      [Hbody [Htype_args [Hbounds [Hcheck _]]]]]]].
  unfold infer_type_forall_call_env_elab_assoc in Hcall.
  rewrite Hbody, Htype_args, Hbounds, Hcheck in Hcall.
  inversion Hcall; subst; clear Hcall; simpl.
  eapply TERAssocBoundary_CallExpr_TypeForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.


Lemma infer_env_mixed_forall_assoc_structural_boundary :
  forall fuel env Omega n callee u u_body m bounds type_params type_bounds body
      args arg_tys T Sigma Sigma1 Sigma',
    typed_env_structural env Omega n Sigma callee
      (MkTy u (TForall m bounds
        (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_mixed_forall_call_env_assoc
      env Omega n m bounds type_params type_bounds body arg_tys = infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExpr callee args) T Sigma'.
Proof.
  intros fuel env Omega n callee u u_body m bounds type_params type_bounds body
    args arg_tys T Sigma Sigma1 Sigma' Hcallee Hcollect Hexpr Hcall.
  unfold infer_mixed_forall_call_env_assoc in Hcall.
  destruct (ty_core body) eqn:Hbody; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|]
    eqn:Htype_args; try discriminate.
  destruct (build_bound_sigma (repeat None m) arg_tys
    (map (subst_type_params_ty type_args) l)) as [sigma0|]
    eqn:Hsigma; try discriminate.
  set (sigma := complete_bound_sigma_with_vars n sigma0) in *.
  destruct (check_arg_tys_assoc env Omega arg_tys
    (map (open_bound_ty sigma)
      (map (subst_type_params_ty type_args) l))) as [err|]
    eqn:Hcheck; try discriminate.
  destruct (contains_lbound_ty
    (open_bound_ty sigma (subst_type_params_ty type_args t)) ||
    contains_lbound_outlives (open_bound_outlives sigma bounds) ||
    existsb
      (fun b : core_trait_bound Ty =>
         existsb
           (fun tr : core_trait_ref Ty =>
              existsb contains_lbound_ty (core_trait_ref_args Ty tr))
           (core_bound_traits Ty b))
      (open_core_trait_bounds sigma type_bounds)) eqn:Hunres; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (open_bound_outlives sigma bounds)) eqn:Hout; try discriminate.
  destruct (check_type_forall_bounds env
    (open_core_trait_bounds sigma type_bounds) type_args) as [err_bounds|]
    eqn:Hbounds; try discriminate.
  inversion Hcall; subst; clear Hcall.
  apply orb_false_iff in Hunres as [Hunres_left Htype_bounds_unres].
  apply orb_false_iff in Hunres_left as [Hret_unres Hbounds_unres].
  eapply TESAssocBoundary_CallExpr_MixedForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - exact Hret_unres.
  - exact Hbounds_unres.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Lemma infer_env_mixed_forall_elab_assoc_structural_boundary :
  forall fuel env Omega n callee u u_body m bounds type_params type_bounds body
      args arg_tys type_args_ret Sigma Sigma1 Sigma',
    typed_env_structural env Omega n Sigma callee
      (MkTy u (TForall m bounds
        (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_mixed_forall_call_env_elab_assoc
      env Omega n m bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExpr callee args) (snd type_args_ret) Sigma'.
Proof.
  intros fuel env Omega n callee u u_body m bounds type_params type_bounds body
    args arg_tys type_args_ret Sigma Sigma1 Sigma' Hcallee Hcollect Hexpr
    Hcall.
  unfold infer_mixed_forall_call_env_elab_assoc in Hcall.
  destruct (ty_core body) eqn:Hbody; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|]
    eqn:Htype_args; try discriminate.
  destruct (build_bound_sigma (repeat None m) arg_tys
    (map (subst_type_params_ty type_args) l)) as [sigma0|]
    eqn:Hsigma; try discriminate.
  set (sigma := complete_bound_sigma_with_vars n sigma0) in *.
  destruct (check_arg_tys_assoc env Omega arg_tys
    (map (open_bound_ty sigma)
      (map (subst_type_params_ty type_args) l))) as [err|]
    eqn:Hcheck; try discriminate.
  destruct (contains_lbound_ty
    (open_bound_ty sigma (subst_type_params_ty type_args t)) ||
    contains_lbound_outlives (open_bound_outlives sigma bounds) ||
    existsb
      (fun b : core_trait_bound Ty =>
         existsb
           (fun tr : core_trait_ref Ty =>
              existsb contains_lbound_ty (core_trait_ref_args Ty tr))
           (core_bound_traits Ty b))
      (open_core_trait_bounds sigma type_bounds)) eqn:Hunres; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (open_bound_outlives sigma bounds)) eqn:Hout; try discriminate.
  destruct (check_type_forall_bounds env
    (open_core_trait_bounds sigma type_bounds) type_args) as [err_bounds|]
    eqn:Hbounds; try discriminate.
  inversion Hcall; subst; clear Hcall; simpl.
  apply orb_false_iff in Hunres as [Hunres_left Htype_bounds_unres].
  apply orb_false_iff in Hunres_left as [Hret_unres Hbounds_unres].
  eapply TESAssocBoundary_CallExpr_MixedForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_assoc_checked_sound; eassumption.
  - exact Hret_unres.
  - exact Hbounds_unres.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Lemma infer_roots_mixed_forall_assoc_structural_boundary :
  forall fuel env Omega n callee u u_body m bounds type_params type_bounds body
      R R1 Sigma Sigma1 args arg_tys T Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TForall m bounds
        (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_mixed_forall_call_env_assoc
      env Omega n m bounds type_params type_bounds body arg_tys = infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u u_body m bounds type_params type_bounds body
    R R1 Sigma Sigma1 args arg_tys T Sigma' R' arg_roots roots_callee
    Hcallee Hcollect Hexpr Hcall.
  unfold infer_mixed_forall_call_env_assoc in Hcall.
  destruct (ty_core body) eqn:Hbody; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|]
    eqn:Htype_args; try discriminate.
  destruct (build_bound_sigma (repeat None m) arg_tys
    (map (subst_type_params_ty type_args) l)) as [sigma0|]
    eqn:Hsigma; try discriminate.
  set (sigma := complete_bound_sigma_with_vars n sigma0) in *.
  destruct (check_arg_tys_assoc env Omega arg_tys
    (map (open_bound_ty sigma)
      (map (subst_type_params_ty type_args) l))) as [err|]
    eqn:Hcheck; try discriminate.
  destruct (contains_lbound_ty
    (open_bound_ty sigma (subst_type_params_ty type_args t)) ||
    contains_lbound_outlives (open_bound_outlives sigma bounds) ||
    existsb
      (fun b : core_trait_bound Ty =>
         existsb
           (fun tr : core_trait_ref Ty =>
              existsb contains_lbound_ty (core_trait_ref_args Ty tr))
           (core_bound_traits Ty b))
      (open_core_trait_bounds sigma type_bounds)) eqn:Hunres; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (open_bound_outlives sigma bounds)) eqn:Hout; try discriminate.
  destruct (check_type_forall_bounds env
    (open_core_trait_bounds sigma type_bounds) type_args) as [err_bounds|]
    eqn:Hbounds; try discriminate.
  inversion Hcall; subst; clear Hcall.
  apply orb_false_iff in Hunres as [Hunres_left Htype_bounds_unres].
  apply orb_false_iff in Hunres_left as [Hret_unres Hbounds_unres].
  eapply TERAssocBoundary_CallExpr_MixedForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - exact Hret_unres.
  - exact Hbounds_unres.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_roots_mixed_forall_checked_assoc_boundary :
  forall fuel env Omega n callee u u_body m bounds type_params type_bounds body
      R R1 Sigma Sigma1 args arg_tys T Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TForall m bounds
        (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_mixed_forall_call_env_assoc
      env Omega n m bounds type_params type_bounds body arg_tys = infer_ok T ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u u_body m bounds type_params type_bounds body
    R R1 Sigma Sigma1 args arg_tys T Sigma' R' arg_roots roots_callee
    Hcallee Hcollect Hexpr Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_mixed_forall_assoc_structural_boundary; eassumption.
Qed.


Lemma infer_roots_mixed_forall_elab_assoc_structural_boundary :
  forall fuel env Omega n callee u u_body m bounds type_params type_bounds body
      R R1 Sigma Sigma1 args arg_tys type_args_ret Sigma' R' arg_roots
      roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TForall m bounds
        (MkTy u_body (TTypeForall type_params type_bounds body)))) Sigma1 R1
      roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_mixed_forall_call_env_elab_assoc
      env Omega n m bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExpr callee args) (snd type_args_ret) Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u u_body m bounds type_params type_bounds body
    R R1 Sigma Sigma1 args arg_tys type_args_ret Sigma' R' arg_roots
    roots_callee Hcallee Hcollect Hexpr Hcall.
  unfold infer_mixed_forall_call_env_elab_assoc in Hcall.
  destruct (ty_core body) eqn:Hbody; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|]
    eqn:Htype_args; try discriminate.
  destruct (build_bound_sigma (repeat None m) arg_tys
    (map (subst_type_params_ty type_args) l)) as [sigma0|]
    eqn:Hsigma; try discriminate.
  set (sigma := complete_bound_sigma_with_vars n sigma0) in *.
  destruct (check_arg_tys_assoc env Omega arg_tys
    (map (open_bound_ty sigma)
      (map (subst_type_params_ty type_args) l))) as [err|]
    eqn:Hcheck; try discriminate.
  destruct (contains_lbound_ty
    (open_bound_ty sigma (subst_type_params_ty type_args t)) ||
    contains_lbound_outlives (open_bound_outlives sigma bounds) ||
    existsb
      (fun b : core_trait_bound Ty =>
         existsb
           (fun tr : core_trait_ref Ty =>
              existsb contains_lbound_ty (core_trait_ref_args Ty tr))
           (core_bound_traits Ty b))
      (open_core_trait_bounds sigma type_bounds)) eqn:Hunres; try discriminate.
  destruct (outlives_constraints_hold_b Omega
    (open_bound_outlives sigma bounds)) eqn:Hout; try discriminate.
  destruct (check_type_forall_bounds env
    (open_core_trait_bounds sigma type_bounds) type_args) as [err_bounds|]
    eqn:Hbounds; try discriminate.
  inversion Hcall; subst; clear Hcall; simpl.
  apply orb_false_iff in Hunres as [Hunres_left Htype_bounds_unres].
  apply orb_false_iff in Hunres_left as [Hret_unres Hbounds_unres].
  eapply TERAssocBoundary_CallExpr_MixedForall.
  - exact Hcallee.
  - exact Hbody.
  - exact Hbounds.
  - exact Hret_unres.
  - exact Hbounds_unres.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
  - rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
    eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.

Lemma infer_env_hrt_assoc_structural_boundary :
  forall fuel env Omega n callee u m bounds body args arg_tys T Sigma Sigma1
      Sigma',
    typed_env_structural env Omega n Sigma callee
      (MkTy u (TForall m bounds body)) Sigma1 ->
    infer_env_args_collect fuel env Omega n Sigma1 args =
      infer_ok (arg_tys, Sigma') ->
    (forall Sigma0 e T0 Sigma2,
        In e args ->
        infer_core_env_state_fuel fuel env Omega n Sigma0 e =
          infer_ok (T0, Sigma2) ->
        typed_env_structural env Omega n Sigma0 e T0 Sigma2) ->
    infer_hrt_call_env_assoc env Omega n m bounds body arg_tys = infer_ok T ->
    typed_env_structural_assoc_call_boundary env Omega n Sigma
      (ECallExpr callee args) T Sigma'.
Proof.
  intros fuel env Omega n callee u m bounds body args arg_tys T Sigma Sigma1
    Sigma' Hcallee Hcollect Hexpr Hcall.
  unfold infer_hrt_call_env_assoc in Hcall.
  destruct (ty_core body) eqn:Hbody; try discriminate.
  - destruct (build_bound_sigma (repeat None m) arg_tys l) as [sigma|]
      eqn:Hsigma; try discriminate.
    destruct (check_arg_tys_assoc env Omega arg_tys
      (map (open_bound_ty sigma) l)) as [err|] eqn:Hcheck; try discriminate.
    destruct (contains_lbound_ty (open_bound_ty sigma t) ||
      contains_lbound_outlives (open_bound_outlives sigma bounds))
      eqn:Hunres; try discriminate.
    destruct (outlives_constraints_hold_b Omega (open_bound_outlives sigma bounds))
      eqn:Hout; try discriminate.
    inversion Hcall; subst; clear Hcall.
    apply orb_false_iff in Hunres as [Hret_unres Hbounds_unres].
    eapply TESAssocBoundary_CallExpr_Forall.
    + exact Hcallee.
    + exact Hbody.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_assoc_checked_sound; eassumption.
    + exact Hret_unres.
    + exact Hbounds_unres.
    + apply env_outlives_constraints_hold_b_sound. exact Hout.
  - destruct (build_bound_sigma (repeat None m) arg_tys l0) as [sigma0|]
      eqn:Hsigma; try discriminate.
    set (sigma := complete_bound_sigma_with_vars n sigma0) in *.
    destruct (check_arg_tys_assoc env Omega arg_tys
      (map (open_bound_ty sigma) l0)) as [err|] eqn:Hcheck; try discriminate.
    destruct (contains_lbound_lifetime (open_bound_lifetime sigma l) ||
      contains_lbound_ty (open_bound_ty sigma t) ||
      contains_lbound_outlives (open_bound_outlives sigma bounds))
      eqn:Hunres; try discriminate.
    destruct (outlives_constraints_hold_b Omega (open_bound_outlives sigma bounds))
      eqn:Hout; try discriminate.
    inversion Hcall; subst; clear Hcall.
    apply orb_false_iff in Hunres as [Hunres_left Hbounds_unres].
    apply orb_false_iff in Hunres_left as [Henv_unres Hret_unres].
    eapply TESAssocBoundary_CallExpr_Forall_Closure.
    + exact Hcallee.
    + exact Hbody.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_assoc_checked_sound; eassumption.
    + exact Henv_unres.
    + exact Hret_unres.
    + exact Hbounds_unres.
    + apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Lemma infer_roots_hrt_assoc_structural_boundary :
  forall fuel env Omega n callee u m bounds body R R1 Sigma Sigma1 args
      arg_tys T Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TForall m bounds body)) Sigma1 R1 roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_hrt_call_env_assoc env Omega n m bounds body arg_tys = infer_ok T ->
    typed_env_roots_assoc_call_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u m bounds body R R1 Sigma Sigma1 args
    arg_tys T Sigma' R' arg_roots roots_callee Hcallee Hcollect Hexpr Hcall.
  unfold infer_hrt_call_env_assoc in Hcall.
  destruct (ty_core body) eqn:Hbody; try discriminate.
  - destruct (build_bound_sigma (repeat None m) arg_tys l) as [sigma|]
      eqn:Hsigma; try discriminate.
    destruct (check_arg_tys_assoc env Omega arg_tys
      (map (open_bound_ty sigma) l)) as [err|] eqn:Hcheck; try discriminate.
    destruct (contains_lbound_ty (open_bound_ty sigma t) ||
      contains_lbound_outlives (open_bound_outlives sigma bounds))
      eqn:Hunres; try discriminate.
    destruct (outlives_constraints_hold_b Omega (open_bound_outlives sigma bounds))
      eqn:Hout; try discriminate.
    inversion Hcall; subst; clear Hcall.
    apply orb_false_iff in Hunres as [Hret_unres Hbounds_unres].
    eapply TERAssocBoundary_CallExpr_Forall_Fn.
    + exact Hcallee.
    + exact Hbody.
    + exact Hret_unres.
    + exact Hbounds_unres.
    + apply env_outlives_constraints_hold_b_sound. exact Hout.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - destruct (build_bound_sigma (repeat None m) arg_tys l0) as [sigma0|]
      eqn:Hsigma; try discriminate.
    set (sigma := complete_bound_sigma_with_vars n sigma0) in *.
    destruct (check_arg_tys_assoc env Omega arg_tys
      (map (open_bound_ty sigma) l0)) as [err|] eqn:Hcheck; try discriminate.
    destruct (contains_lbound_lifetime (open_bound_lifetime sigma l) ||
      contains_lbound_ty (open_bound_ty sigma t) ||
      contains_lbound_outlives (open_bound_outlives sigma bounds))
      eqn:Hunres; try discriminate.
    destruct (outlives_constraints_hold_b Omega (open_bound_outlives sigma bounds))
      eqn:Hout; try discriminate.
    inversion Hcall; subst; clear Hcall.
    apply orb_false_iff in Hunres as [Hunres_left Hbounds_unres].
    apply orb_false_iff in Hunres_left as [Henv_unres Hret_unres].
    eapply TERAssocBoundary_CallExpr_Forall_Closure.
    + exact Hcallee.
    + exact Hbody.
    + exact Henv_unres.
    + exact Hret_unres.
    + exact Hbounds_unres.
    + apply env_outlives_constraints_hold_b_sound. exact Hout.
    + rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
      eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
Qed.


Lemma infer_roots_hrt_checked_assoc_boundary :
  forall fuel env Omega n callee u m bounds body R R1 Sigma Sigma1 args
      arg_tys T Sigma' R' arg_roots roots_callee,
    typed_env_roots env Omega n R Sigma callee
      (MkTy u (TForall m bounds body)) Sigma1 R1 roots_callee ->
    infer_env_args_collect_roots fuel env Omega n R1 Sigma1 args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma2 R2 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma2, R2, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma2 R2 roots1) ->
    infer_hrt_call_env_assoc env Omega n m bounds body arg_tys = infer_ok T ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallExpr callee args) T Sigma' R'
      (root_set_union roots_callee (root_sets_union arg_roots)).
Proof.
  intros fuel env Omega n callee u m bounds body R R1 Sigma Sigma1 args
    arg_tys T Sigma' R' arg_roots roots_callee Hcallee Hcollect Hexpr Hcall.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply infer_roots_hrt_assoc_structural_boundary; eassumption.
Qed.


Lemma infer_roots_make_closure_checked_assoc_boundary :
  forall fuel env Omega n fname fdef captures env_lt captured_tys R Sigma args
      arg_tys sigma_acc Sigma' R' arg_roots,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    check_make_closure_captures_sctx_with_env env Omega Sigma captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    infer_env_args_collect_roots fuel env Omega n R Sigma args =
      infer_ok (arg_tys, Sigma', R', arg_roots) ->
    (forall R0 Sigma0 e T0 Sigma1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Omega n R0 Sigma0 e =
          infer_ok (T0, Sigma1, R1, roots1) ->
        typed_env_roots env Omega n R0 Sigma0 e T0 Sigma1 R1 roots1) ->
    build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
      arg_tys (fn_params fdef) = Some sigma_acc ->
    check_args_assoc env Omega arg_tys
      (apply_lt_params (finalize_subst sigma_acc) (fn_params fdef)) = None ->
    forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst sigma_acc) = true ->
    outlives_constraints_hold_b Omega
      (apply_lt_outlives (finalize_subst sigma_acc) (fn_outlives fdef)) = true ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma
      (ECallExpr (EMakeClosure fname captures) args)
      (apply_lt_ty (finalize_subst sigma_acc) (fn_ret fdef)) Sigma' R'
      (root_sets_union arg_roots).
Proof.
  intros fuel env Omega n fname fdef captures env_lt captured_tys R Sigma args
    arg_tys sigma_acc Sigma' R' arg_roots Hin Hname Hcaptures Hcollect Hexpr
    Hbuild Hcheck Hwf Hout.
  eapply typed_env_roots_checked_assoc_boundary_of_assoc_call_boundary.
  eapply TERAssocBoundary_CallExpr_MakeClosure with
    (env_lt := env_lt) (captured_tys := captured_tys)
    (sigma := finalize_subst sigma_acc).
  - exact Hin.
  - exact Hname.
  - exact Hcaptures.
  - eapply infer_env_args_collect_roots_assoc_checked_sound; eassumption.
  - apply env_outlives_constraints_hold_b_sound. exact Hout.
Qed.

Theorem infer_core_env_state_fuel_roots_assoc_boundary_sound :
  forall fuel env Omega n R Sigma e T Sigma' R' roots,
    infer_core_env_state_fuel_roots fuel env Omega n R Sigma e =
      infer_ok (T, Sigma', R', roots) ->
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots.
Proof.
  intros fuel env Omega n R Sigma e T Sigma' R' roots Hinfer.
  apply TERAssocBoundary_Roots.
  eapply infer_core_env_state_fuel_roots_sound. exact Hinfer.
Qed.

Theorem infer_core_env_roots_assoc_boundary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    typed_env_roots_assoc_boundary env Omega n R (sctx_of_ctx Gamma) e T
      (sctx_of_ctx Gamma') R' roots.
Proof.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer.
  apply TERAssocBoundary_Roots.
  eapply infer_core_env_roots_sound. exact Hinfer.
Qed.

Theorem infer_core_env_state_fuel_roots_shadow_safe_assoc_boundary_sound :
  forall fuel env Omega n R Sigma e T Sigma' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Sigma e =
      infer_ok (T, Sigma', R', roots) ->
    typed_env_roots_assoc_boundary env Omega n R Sigma e T Sigma' R' roots.
Proof.
  intros fuel env Omega n R Sigma e T Sigma' R' roots Hinfer.
  apply TERAssocBoundary_Roots.
  eapply typed_env_roots_shadow_safe_roots.
  eapply infer_core_env_state_fuel_roots_shadow_safe_sound. exact Hinfer.
Qed.

Theorem infer_core_env_roots_shadow_safe_assoc_boundary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    typed_env_roots_assoc_boundary env Omega n R (sctx_of_ctx Gamma) e T
      (sctx_of_ctx Gamma') R' roots.
Proof.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer.
  apply TERAssocBoundary_Roots.
  eapply typed_env_roots_shadow_safe_roots.
  eapply infer_core_env_roots_shadow_safe_sound. exact Hinfer.
Qed.

Theorem infer_core_env_state_fuel_roots_shadow_safe_checked_assoc_boundary_sound :
  forall fuel env Omega n R Sigma e T Sigma' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe_checked fuel env Omega n R Sigma e =
      infer_ok (T, Sigma', R', roots) ->
    typed_env_roots_checked_assoc_boundary env Omega n R Sigma e T Sigma' R' roots.
Proof.
  intros fuel env Omega n R Sigma e T Sigma' R' roots Hinfer.
  apply TERCAssocBoundary_Checked.
  eapply typed_env_roots_shadow_safe_checked_checked.
  eapply infer_core_env_state_fuel_roots_shadow_safe_checked_sound. exact Hinfer.
Qed.

Theorem infer_core_env_roots_shadow_safe_checked_assoc_boundary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe_checked env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    typed_env_roots_checked_assoc_boundary env Omega n R (sctx_of_ctx Gamma) e T
      (sctx_of_ctx Gamma') R' roots.
Proof.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer.
  apply TERCAssocBoundary_Checked.
  eapply typed_env_roots_shadow_safe_checked_checked.
  eapply infer_core_env_roots_shadow_safe_checked_sound. exact Hinfer.
Qed.
