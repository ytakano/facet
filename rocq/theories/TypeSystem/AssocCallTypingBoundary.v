From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker
  AssocCompatibility AssocArgBoolFacts.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Associated-projection call typing boundaries                         *)
(* ------------------------------------------------------------------ *)

Definition assoc_call_args_compatible
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    (Γ : ctx) (args : list expr) (params : list param) (Γ' : ctx) : Prop :=
  typed_args_assoc env fenv Ω n Γ args params Γ'.

Inductive assoc_direct_call_typing_boundary
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> list expr -> list param -> Ty -> ctx -> Prop :=
  | AssocDirectCallTypingBoundary : forall Γ args params ret Γ',
      assoc_call_args_compatible env fenv Ω n Γ args params Γ' ->
      assoc_direct_call_typing_boundary env fenv Ω n Γ args params ret Γ'.

Inductive assoc_fn_value_call_typing_boundary
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> expr -> Ty -> ctx -> list expr -> list Ty -> Ty -> ctx -> Prop :=
  | AssocFnValueCallTypingBoundaryFn :
      forall Γ callee callee_ty Γ_args args param_tys ret Γ',
        typed fenv Ω n Γ callee callee_ty Γ_args ->
        ty_core callee_ty = TFn param_tys ret ->
        assoc_call_args_compatible env fenv Ω n Γ_args args
          (params_of_tys param_tys) Γ' ->
        assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
          Γ_args args param_tys ret Γ'
  | AssocFnValueCallTypingBoundaryClosure :
      forall Γ callee callee_ty Γ_args args env_lt param_tys ret Γ',
        typed fenv Ω n Γ callee callee_ty Γ_args ->
        ty_core callee_ty = TClosure env_lt param_tys ret ->
        assoc_call_args_compatible env fenv Ω n Γ_args args
          (params_of_tys param_tys) Γ' ->
        assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
          Γ_args args param_tys ret Γ'.


Inductive assoc_fn_value_forall_call_typing_boundary
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> expr -> Ty -> ctx -> list expr -> nat -> outlives_ctx ->
      Ty -> list (option lifetime) -> list Ty -> Ty -> ctx -> Prop :=
  | AssocFnValueForallCallTypingBoundaryFn :
      forall Γ callee callee_ty Γ_args args m bounds body sigma
          param_tys ret Γ',
        typed fenv Ω n Γ callee callee_ty Γ_args ->
        ty_core callee_ty = TForall m bounds body ->
        ty_core body = TFn param_tys ret ->
        contains_lbound_ty (open_bound_ty sigma ret) = false ->
        contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
        Forall (fun '(a, b) => outlives Ω a b)
          (open_bound_outlives sigma bounds) ->
        assoc_call_args_compatible env fenv Ω n Γ_args args
          (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ' ->
        assoc_fn_value_forall_call_typing_boundary env fenv Ω n Γ callee
          callee_ty Γ_args args m bounds body sigma param_tys ret Γ'.

Inductive assoc_fn_value_forall_closure_call_typing_boundary
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> expr -> Ty -> ctx -> list expr -> nat -> outlives_ctx ->
      Ty -> lifetime -> list (option lifetime) -> list Ty -> Ty -> ctx -> Prop :=
  | AssocFnValueForallClosureCallTypingBoundary :
      forall Γ callee callee_ty Γ_args args m bounds body env_lt sigma
          param_tys ret Γ',
        typed fenv Ω n Γ callee callee_ty Γ_args ->
        ty_core callee_ty = TForall m bounds body ->
        ty_core body = TClosure env_lt param_tys ret ->
        contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false ->
        contains_lbound_ty (open_bound_ty sigma ret) = false ->
        contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
        Forall (fun '(a, b) => outlives Ω a b)
          (open_bound_outlives sigma bounds) ->
        assoc_call_args_compatible env fenv Ω n Γ_args args
          (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ' ->
        assoc_fn_value_forall_closure_call_typing_boundary env fenv Ω n Γ
          callee callee_ty Γ_args args m bounds body env_lt sigma param_tys
          ret Γ'.

Inductive assoc_fn_value_type_forall_call_typing_boundary
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> expr -> Ty -> ctx -> list expr -> nat ->
      list (core_trait_bound Ty) -> Ty -> list Ty -> list Ty -> Ty ->
      ctx -> Prop :=
  | AssocFnValueTypeForallCallTypingBoundaryFn :
      forall Γ callee callee_ty Γ_args args m bounds body type_args
          param_tys ret Γ',
        typed fenv Ω n Γ callee callee_ty Γ_args ->
        ty_core callee_ty = TTypeForall m bounds body ->
        ty_core body = TFn param_tys ret ->
        assoc_call_args_compatible env fenv Ω n Γ_args args
          (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Γ' ->
        assoc_fn_value_type_forall_call_typing_boundary env fenv Ω n Γ
          callee callee_ty Γ_args args m bounds body type_args param_tys ret Γ'.

Lemma typed_args_assoc_Forall2_compat :
  forall env fenv Ω n Γ args params Γ',
    typed_args_assoc env fenv Ω n Γ args params Γ' ->
    Forall2
      (fun e p =>
         exists T Γin Γout,
           typed fenv Ω n Γin e T Γout /\
           ty_compatible_assoc env Ω T (param_ty p))
      args params.
Proof.
  intros env fenv Ω n Γ args params Γ' Hargs.
  induction Hargs.
  - constructor.
  - constructor.
    + exists T_e, Γ, Γ1. split; assumption.
    + exact IHHargs.
Qed.


Lemma assoc_fn_value_forall_call_typing_boundary_callee :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
      param_tys ret Γ',
    assoc_fn_value_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body sigma param_tys ret Γ' ->
    typed fenv Ω n Γ callee callee_ty Γ_args /\
    ty_core callee_ty = TForall m bounds body /\
    ty_core body = TFn param_tys ret /\
    contains_lbound_ty (open_bound_ty sigma ret) = false /\
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false /\
    Forall (fun '(a, b) => outlives Ω a b)
      (open_bound_outlives sigma bounds).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
    param_tys ret Γ' Hboundary.
  inversion Hboundary; subst. repeat split; assumption.
Qed.

Lemma assoc_fn_value_forall_call_typing_boundary_args :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
      param_tys ret Γ',
    assoc_fn_value_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body sigma param_tys ret Γ' ->
    typed_args_assoc env fenv Ω n Γ_args args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
    param_tys ret Γ' Hboundary.
  inversion Hboundary; subst; eassumption.
Qed.

Lemma assoc_fn_value_forall_call_typing_boundary_Forall2_compat :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
      param_tys ret Γ',
    assoc_fn_value_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body sigma param_tys ret Γ' ->
    Forall2
      (fun e p =>
         exists T Γin Γout,
           typed fenv Ω n Γin e T Γout /\
           ty_compatible_assoc env Ω T (param_ty p))
      args (params_of_tys (map (open_bound_ty sigma) param_tys)).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
    param_tys ret Γ' Hboundary.
  exact (typed_args_assoc_Forall2_compat env fenv Ω n Γ_args args
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ'
    (assoc_fn_value_forall_call_typing_boundary_args env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body sigma param_tys ret Γ'
      Hboundary)).
Qed.

Lemma assoc_fn_value_forall_call_typing_boundary_length :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
      param_tys ret Γ',
    assoc_fn_value_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body sigma param_tys ret Γ' ->
    length args = length (params_of_tys (map (open_bound_ty sigma) param_tys)).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body sigma
    param_tys ret Γ' Hboundary.
  exact (typed_args_assoc_length env fenv Ω n Γ_args args
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ'
    (assoc_fn_value_forall_call_typing_boundary_args env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body sigma param_tys ret Γ'
      Hboundary)).
Qed.

Lemma assoc_fn_value_forall_closure_call_typing_boundary_callee :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
      sigma param_tys ret Γ',
    assoc_fn_value_forall_closure_call_typing_boundary env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ' ->
    typed fenv Ω n Γ callee callee_ty Γ_args /\
    ty_core callee_ty = TForall m bounds body /\
    ty_core body = TClosure env_lt param_tys ret /\
    contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false /\
    contains_lbound_ty (open_bound_ty sigma ret) = false /\
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false /\
    Forall (fun '(a, b) => outlives Ω a b)
      (open_bound_outlives sigma bounds).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
    sigma param_tys ret Γ' Hboundary.
  inversion Hboundary; subst. repeat split; assumption.
Qed.

Lemma assoc_fn_value_forall_closure_call_typing_boundary_args :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
      sigma param_tys ret Γ',
    assoc_fn_value_forall_closure_call_typing_boundary env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ' ->
    typed_args_assoc env fenv Ω n Γ_args args
      (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
    sigma param_tys ret Γ' Hboundary.
  inversion Hboundary; subst; eassumption.
Qed.

Lemma assoc_fn_value_forall_closure_call_typing_boundary_Forall2_compat :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
      sigma param_tys ret Γ',
    assoc_fn_value_forall_closure_call_typing_boundary env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ' ->
    Forall2
      (fun e p =>
         exists T Γin Γout,
           typed fenv Ω n Γin e T Γout /\
           ty_compatible_assoc env Ω T (param_ty p))
      args (params_of_tys (map (open_bound_ty sigma) param_tys)).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
    sigma param_tys ret Γ' Hboundary.
  exact (typed_args_assoc_Forall2_compat env fenv Ω n Γ_args args
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ'
    (assoc_fn_value_forall_closure_call_typing_boundary_args env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ'
      Hboundary)).
Qed.

Lemma assoc_fn_value_forall_closure_call_typing_boundary_length :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
      sigma param_tys ret Γ',
    assoc_fn_value_forall_closure_call_typing_boundary env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ' ->
    length args = length (params_of_tys (map (open_bound_ty sigma) param_tys)).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body env_lt
    sigma param_tys ret Γ' Hboundary.
  exact (typed_args_assoc_length env fenv Ω n Γ_args args
    (params_of_tys (map (open_bound_ty sigma) param_tys)) Γ'
    (assoc_fn_value_forall_closure_call_typing_boundary_args env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ'
      Hboundary)).
Qed.

Lemma assoc_fn_value_type_forall_call_typing_boundary_callee :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
      param_tys ret Γ',
    assoc_fn_value_type_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body type_args param_tys ret Γ' ->
    typed fenv Ω n Γ callee callee_ty Γ_args /\
    ty_core callee_ty = TTypeForall m bounds body /\
    ty_core body = TFn param_tys ret.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
    param_tys ret Γ' Hboundary.
  inversion Hboundary; subst. repeat split; assumption.
Qed.

Lemma assoc_fn_value_type_forall_call_typing_boundary_args :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
      param_tys ret Γ',
    assoc_fn_value_type_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body type_args param_tys ret Γ' ->
    typed_args_assoc env fenv Ω n Γ_args args
      (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
    param_tys ret Γ' Hboundary.
  inversion Hboundary; subst; eassumption.
Qed.

Lemma assoc_fn_value_type_forall_call_typing_boundary_Forall2_compat :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
      param_tys ret Γ',
    assoc_fn_value_type_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body type_args param_tys ret Γ' ->
    Forall2
      (fun e p =>
         exists T Γin Γout,
           typed fenv Ω n Γin e T Γout /\
           ty_compatible_assoc env Ω T (param_ty p))
      args (params_of_tys (map (subst_type_params_ty type_args) param_tys)).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
    param_tys ret Γ' Hboundary.
  exact (typed_args_assoc_Forall2_compat env fenv Ω n Γ_args args
    (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Γ'
    (assoc_fn_value_type_forall_call_typing_boundary_args env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body type_args param_tys ret Γ'
      Hboundary)).
Qed.

Lemma assoc_fn_value_type_forall_call_typing_boundary_length :
  forall env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
      param_tys ret Γ',
    assoc_fn_value_type_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body type_args param_tys ret Γ' ->
    length args =
      length (params_of_tys (map (subst_type_params_ty type_args) param_tys)).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args m bounds body type_args
    param_tys ret Γ' Hboundary.
  exact (typed_args_assoc_length env fenv Ω n Γ_args args
    (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Γ'
    (assoc_fn_value_type_forall_call_typing_boundary_args env fenv Ω n Γ
      callee callee_ty Γ_args args m bounds body type_args param_tys ret Γ'
      Hboundary)).
Qed.

Lemma assoc_direct_call_typing_boundary_args :
  forall env fenv Ω n Γ args params ret Γ',
    assoc_direct_call_typing_boundary env fenv Ω n Γ args params ret Γ' ->
    typed_args_assoc env fenv Ω n Γ args params Γ'.
Proof.
  intros env fenv Ω n Γ args params ret Γ' Hboundary.
  inversion Hboundary; subst. exact H.
Qed.

Lemma assoc_direct_call_typing_boundary_Forall2_compat :
  forall env fenv Ω n Γ args params ret Γ',
    assoc_direct_call_typing_boundary env fenv Ω n Γ args params ret Γ' ->
    Forall2
      (fun e p =>
         exists T Γin Γout,
           typed fenv Ω n Γin e T Γout /\
           ty_compatible_assoc env Ω T (param_ty p))
      args params.
Proof.
  intros env fenv Ω n Γ args params ret Γ' Hboundary.
  exact (typed_args_assoc_Forall2_compat env fenv Ω n Γ args params Γ'
    (assoc_direct_call_typing_boundary_args env fenv Ω n Γ args params ret Γ'
      Hboundary)).
Qed.

Lemma assoc_direct_call_typing_boundary_length :
  forall env fenv Ω n Γ args params ret Γ',
    assoc_direct_call_typing_boundary env fenv Ω n Γ args params ret Γ' ->
    length args = length params.
Proof.
  intros env fenv Ω n Γ args params ret Γ' Hboundary.
  exact (typed_args_assoc_length env fenv Ω n Γ args params Γ'
    (assoc_direct_call_typing_boundary_args env fenv Ω n Γ args params ret Γ'
      Hboundary)).
Qed.

Lemma assoc_fn_value_call_typing_boundary_callee :
  forall env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ',
    assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
      Γ_args args param_tys ret Γ' ->
    typed fenv Ω n Γ callee callee_ty Γ_args /\
    (ty_core callee_ty = TFn param_tys ret \/
     exists env_lt, ty_core callee_ty = TClosure env_lt param_tys ret).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ'
    Hboundary.
  inversion Hboundary; subst.
  - split; [assumption | left; assumption].
  - split; [assumption | right; eexists; eassumption].
Qed.

Lemma assoc_fn_value_call_typing_boundary_args :
  forall env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ',
    assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
      Γ_args args param_tys ret Γ' ->
    typed_args_assoc env fenv Ω n Γ_args args (params_of_tys param_tys) Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ'
    Hboundary.
  inversion Hboundary; subst; exact H1.
Qed.

Lemma assoc_fn_value_call_typing_boundary_Forall2_compat :
  forall env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ',
    assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
      Γ_args args param_tys ret Γ' ->
    Forall2
      (fun e p =>
         exists T Γin Γout,
           typed fenv Ω n Γin e T Γout /\
           ty_compatible_assoc env Ω T (param_ty p))
      args (params_of_tys param_tys).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ'
    Hboundary.
  exact (typed_args_assoc_Forall2_compat env fenv Ω n Γ_args args
    (params_of_tys param_tys) Γ'
    (assoc_fn_value_call_typing_boundary_args env fenv Ω n Γ callee
      callee_ty Γ_args args param_tys ret Γ' Hboundary)).
Qed.

Lemma assoc_fn_value_call_typing_boundary_length :
  forall env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ',
    assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
      Γ_args args param_tys ret Γ' ->
    length args = length (params_of_tys param_tys).
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args param_tys ret Γ'
    Hboundary.
  exact (typed_args_assoc_length env fenv Ω n Γ_args args
    (params_of_tys param_tys) Γ'
    (assoc_fn_value_call_typing_boundary_args env fenv Ω n Γ callee
      callee_ty Γ_args args param_tys ret Γ' Hboundary)).
Qed.

Lemma infer_call_args_assoc_direct_boundary :
  forall env fenv Ω n Γ args arg_tys params Γ' ret,
    infer_args_collect fenv Ω n Γ args = infer_ok (arg_tys, Γ') ->
    (forall Γ0 e T Γ1,
        In e args ->
        infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
        typed fenv Ω n Γ0 e T Γ1) ->
    check_args_assoc env Ω arg_tys params = None ->
    assoc_direct_call_typing_boundary env fenv Ω n Γ args params ret Γ'.
Proof.
  intros env fenv Ω n Γ args arg_tys params Γ' ret Hcollect Hexpr Hcheck.
  constructor.
  eapply infer_call_args_assoc_sound_v2; eassumption.
Qed.

Lemma infer_call_args_assoc_fn_value_boundary :
  forall env fenv Ω n Γ callee callee_ty Γ_args args arg_tys param_tys ret Γ',
    typed fenv Ω n Γ callee callee_ty Γ_args ->
    ty_core callee_ty = TFn param_tys ret \/
      (exists env_lt, ty_core callee_ty = TClosure env_lt param_tys ret) ->
    infer_args_collect fenv Ω n Γ_args args = infer_ok (arg_tys, Γ') ->
    (forall Γ0 e T Γ1,
        In e args ->
        infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
        typed fenv Ω n Γ0 e T Γ1) ->
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    assoc_fn_value_call_typing_boundary env fenv Ω n Γ callee callee_ty
      Γ_args args param_tys ret Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args arg_tys param_tys ret Γ'
    Hcallee Hshape Hcollect Hexpr Hcheck.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  destruct Hshape as [Hfn | [env_lt Hclosure]].
  - eapply AssocFnValueCallTypingBoundaryFn; eauto.
    eapply infer_call_args_assoc_sound_v2; eassumption.
  - eapply AssocFnValueCallTypingBoundaryClosure; eauto.
    eapply infer_call_args_assoc_sound_v2; eassumption.
Qed.

Lemma infer_call_args_assoc_fn_value_forall_boundary :
  forall env fenv Ω n Γ callee callee_ty Γ_args args arg_tys m bounds body
      sigma param_tys ret Γ',
    typed fenv Ω n Γ callee callee_ty Γ_args ->
    ty_core callee_ty = TForall m bounds body ->
    ty_core body = TFn param_tys ret ->
    contains_lbound_ty (open_bound_ty sigma ret) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Ω a b)
      (open_bound_outlives sigma bounds) ->
    infer_args_collect fenv Ω n Γ_args args = infer_ok (arg_tys, Γ') ->
    (forall Γ0 e T Γ1,
        In e args ->
        infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
        typed fenv Ω n Γ0 e T Γ1) ->
    check_arg_tys_assoc env Ω arg_tys
      (map (open_bound_ty sigma) param_tys) = None ->
    assoc_fn_value_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body sigma param_tys ret Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args arg_tys m bounds body
    sigma param_tys ret Γ' Hcallee Hforall Hbody Hret Hbounds Hout Hcollect
    Hexpr Hcheck.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply AssocFnValueForallCallTypingBoundaryFn; eauto.
  eapply infer_call_args_assoc_sound_v2; eassumption.
Qed.

Lemma infer_call_args_assoc_fn_value_forall_closure_boundary :
  forall env fenv Ω n Γ callee callee_ty Γ_args args arg_tys m bounds body
      env_lt sigma param_tys ret Γ',
    typed fenv Ω n Γ callee callee_ty Γ_args ->
    ty_core callee_ty = TForall m bounds body ->
    ty_core body = TClosure env_lt param_tys ret ->
    contains_lbound_lifetime (open_bound_lifetime sigma env_lt) = false ->
    contains_lbound_ty (open_bound_ty sigma ret) = false ->
    contains_lbound_outlives (open_bound_outlives sigma bounds) = false ->
    Forall (fun '(a, b) => outlives Ω a b)
      (open_bound_outlives sigma bounds) ->
    infer_args_collect fenv Ω n Γ_args args = infer_ok (arg_tys, Γ') ->
    (forall Γ0 e T Γ1,
        In e args ->
        infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
        typed fenv Ω n Γ0 e T Γ1) ->
    check_arg_tys_assoc env Ω arg_tys
      (map (open_bound_ty sigma) param_tys) = None ->
    assoc_fn_value_forall_closure_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body env_lt sigma param_tys ret Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args arg_tys m bounds body
    env_lt sigma param_tys ret Γ' Hcallee Hforall Hbody Henv_lt Hret Hbounds
    Hout Hcollect Hexpr Hcheck.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply AssocFnValueForallClosureCallTypingBoundary; eauto.
  eapply infer_call_args_assoc_sound_v2; eassumption.
Qed.

Lemma infer_call_args_assoc_fn_value_type_forall_boundary :
  forall env fenv Ω n Γ callee callee_ty Γ_args args arg_tys m bounds body
      type_args param_tys ret Γ',
    typed fenv Ω n Γ callee callee_ty Γ_args ->
    ty_core callee_ty = TTypeForall m bounds body ->
    ty_core body = TFn param_tys ret ->
    infer_args_collect fenv Ω n Γ_args args = infer_ok (arg_tys, Γ') ->
    (forall Γ0 e T Γ1,
        In e args ->
        infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
        typed fenv Ω n Γ0 e T Γ1) ->
    check_arg_tys_assoc env Ω arg_tys
      (map (subst_type_params_ty type_args) param_tys) = None ->
    assoc_fn_value_type_forall_call_typing_boundary env fenv Ω n Γ callee
      callee_ty Γ_args args m bounds body type_args param_tys ret Γ'.
Proof.
  intros env fenv Ω n Γ callee callee_ty Γ_args args arg_tys m bounds body
    type_args param_tys ret Γ' Hcallee Hforall Hbody Hcollect Hexpr Hcheck.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  eapply AssocFnValueTypeForallCallTypingBoundaryFn; eauto.
  eapply infer_call_args_assoc_sound_v2; eassumption.
Qed.
