From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program TypingRules RootProvenance
  TypeChecker EnvStructuralRules AssocEnvStructural
  AssocDirectCallHelpers AssocFnValueCallHelpers
  EnvTypingSoundness EnvRootSoundness
  AssocDirectCallFacts AssocFnValueCallFacts.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Env/root associated-projection call typing boundaries                *)
(* ------------------------------------------------------------------ *)

Definition assoc_env_call_args_compatible
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (args : list expr) (params : list param) (Σ' : sctx)
    : Prop :=
  typed_args_env_structural_assoc env Ω n Σ args params Σ'.

Definition assoc_roots_call_args_compatible
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (args : list expr) (params : list param)
    (Σ' : sctx) (R' : root_env) (arg_roots : list root_set) : Prop :=
  typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots.

Inductive assoc_env_call_typing_boundary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> list expr -> list param -> Ty -> sctx -> Prop :=
  | AssocEnvCallTypingBoundary : forall Σ args params ret Σ',
      assoc_env_call_args_compatible env Ω n Σ args params Σ' ->
      assoc_env_call_typing_boundary env Ω n Σ args params ret Σ'.

Inductive assoc_roots_call_typing_boundary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param -> Ty -> sctx ->
      root_env -> list root_set -> Prop :=
  | AssocRootsCallTypingBoundary : forall R Σ args params ret Σ' R' arg_roots,
      assoc_roots_call_args_compatible env Ω n R Σ args params Σ' R'
        arg_roots ->
      assoc_roots_call_typing_boundary env Ω n R Σ args params ret Σ' R'
        arg_roots.

Lemma assoc_env_call_typing_boundary_args :
  forall env Ω n Σ args params ret Σ',
    assoc_env_call_typing_boundary env Ω n Σ args params ret Σ' ->
    typed_args_env_structural_assoc env Ω n Σ args params Σ'.
Proof.
  intros env Ω n Σ args params ret Σ' Hboundary.
  inversion Hboundary; subst. exact H.
Qed.

Lemma assoc_roots_call_typing_boundary_args :
  forall env Ω n R Σ args params ret Σ' R' arg_roots,
    assoc_roots_call_typing_boundary env Ω n R Σ args params ret Σ' R'
      arg_roots ->
    typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args params ret Σ' R' arg_roots Hboundary.
  inversion Hboundary; subst. exact H.
Qed.

Lemma assoc_env_call_typing_boundary_length :
  forall env Ω n Σ args params ret Σ',
    assoc_env_call_typing_boundary env Ω n Σ args params ret Σ' ->
    Datatypes.length args = Datatypes.length params.
Proof.
  intros env Ω n Σ args params ret Σ' Hboundary.
  eapply typed_args_env_structural_assoc_length.
  eapply assoc_env_call_typing_boundary_args. exact Hboundary.
Qed.

Lemma assoc_roots_call_typing_boundary_length :
  forall env Ω n R Σ args params ret Σ' R' arg_roots,
    assoc_roots_call_typing_boundary env Ω n R Σ args params ret Σ' R'
      arg_roots ->
    Datatypes.length args = Datatypes.length params.
Proof.
  intros env Ω n R Σ args params ret Σ' R' arg_roots Hboundary.
  eapply typed_args_roots_assoc_length.
  eapply assoc_roots_call_typing_boundary_args. exact Hboundary.
Qed.

Lemma infer_env_direct_call_assoc_boundary :
  forall fuel env Ω n fdef args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists params,
      assoc_env_call_typing_boundary env Ω n Σ args params T Σ'.
Proof.
  intros fuel env Ω n fdef args arg_tys T Σ Σ' Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_direct_call_assoc_checked_sound
    fuel env Ω n fdef args arg_tys T Σ Σ' Hcollect Hexpr Hcall)
    as [params Hargs].
  exists params. constructor. exact Hargs.
Qed.

Lemma infer_env_direct_call_generic_assoc_boundary :
  forall fuel env Ω n fdef type_args args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys = infer_ok T ->
    exists params,
      assoc_env_call_typing_boundary env Ω n Σ args params T Σ'.
Proof.
  intros fuel env Ω n fdef type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_direct_call_generic_assoc_checked_sound
    fuel env Ω n fdef type_args args arg_tys T Σ Σ' Hcollect Hexpr Hcall)
    as [params Hargs].
  exists params. constructor. exact Hargs.
Qed.

Lemma infer_env_fn_value_call_assoc_boundary :
  forall fuel env Ω n callee_ty args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
    exists param_tys,
      assoc_env_call_typing_boundary env Ω n Σ args (params_of_tys param_tys)
        T Σ'.
Proof.
  intros fuel env Ω n callee_ty args arg_tys T Σ Σ' Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_fn_value_call_assoc_checked_sound
    fuel env Ω n callee_ty args arg_tys T Σ Σ' Hcollect Hexpr Hcall)
    as [param_tys Hargs].
  exists param_tys. constructor. exact Hargs.
Qed.

Lemma infer_env_fn_value_call_generic_assoc_boundary :
  forall fuel env Ω n callee_ty type_args args arg_tys T Σ Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T0 Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T0, Σ1) ->
        typed_env_structural env Ω n Σ0 e T0 Σ1) ->
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists param_tys,
      assoc_env_call_typing_boundary env Ω n Σ args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) T Σ'.
Proof.
  intros fuel env Ω n callee_ty type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_fn_value_call_generic_assoc_checked_sound
    fuel env Ω n callee_ty type_args args arg_tys T Σ Σ'
    Hcollect Hexpr Hcall) as [param_tys Hargs].
  exists param_tys. constructor. exact Hargs.
Qed.

Lemma infer_roots_direct_call_assoc_boundary :
  forall fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_direct_call_assoc env Ω n fdef arg_tys = infer_ok T ->
    exists params,
      assoc_roots_call_typing_boundary env Ω n R Σ args params T Σ' R'
        arg_roots.
Proof.
  intros fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_direct_call_assoc_checked_sound
    fuel env Ω n fdef R Σ args arg_tys T Σ' R' arg_roots Hcollect Hexpr
    Hcall) as [params Hargs].
  exists params. constructor. exact Hargs.
Qed.

Lemma infer_roots_direct_call_generic_assoc_boundary :
  forall fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_direct_call_generic_assoc env Ω n fdef type_args arg_tys =
      infer_ok T ->
    exists params,
      assoc_roots_call_typing_boundary env Ω n R Σ args params T Σ' R'
        arg_roots.
Proof.
  intros fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_direct_call_generic_assoc_checked_sound
    fuel env Ω n fdef type_args R Σ args arg_tys T Σ' R' arg_roots Hcollect
    Hexpr Hcall) as [params Hargs].
  exists params. constructor. exact Hargs.
Qed.

Lemma infer_roots_fn_value_call_assoc_boundary :
  forall fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_fn_value_call_assoc env Ω callee_ty arg_tys = infer_ok T ->
    exists param_tys,
      assoc_roots_call_typing_boundary env Ω n R Σ args
        (params_of_tys param_tys) T Σ' R' arg_roots.
Proof.
  intros fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_fn_value_call_assoc_checked_sound
    fuel env Ω n callee_ty R Σ args arg_tys T Σ' R' arg_roots Hcollect
    Hexpr Hcall) as [param_tys Hargs].
  exists param_tys. constructor. exact Hargs.
Qed.

Lemma infer_roots_fn_value_call_generic_assoc_boundary :
  forall fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R'
      arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T0 Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T0, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T0 Σ1 R1 roots1) ->
    infer_fn_value_call_generic_assoc env Ω callee_ty type_args arg_tys =
      infer_ok T ->
    exists param_tys,
      assoc_roots_call_typing_boundary env Ω n R Σ args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) T Σ'
        R' arg_roots.
Proof.
  intros fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R'
    arg_roots Hcollect Hexpr Hcall.
  destruct (infer_env_args_collect_roots_fn_value_call_generic_assoc_checked_sound
    fuel env Ω n callee_ty type_args R Σ args arg_tys T Σ' R' arg_roots
    Hcollect Hexpr Hcall) as [param_tys Hargs].
  exists param_tys. constructor. exact Hargs.
Qed.
