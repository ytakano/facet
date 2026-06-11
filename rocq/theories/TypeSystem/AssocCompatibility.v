From Facet.TypeSystem Require Import Lifetime Types Syntax Program TypingRules CheckerBase.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Associated type projection compatibility bridge                       *)
(* ------------------------------------------------------------------ *)

Definition ty_compatible_assoc
    (env : global_env) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : Prop :=
  ty_compatible Ω
    (normalize_assoc_ty env T_actual)
    (normalize_assoc_ty env T_expected).

Definition ty_compatible_assoc_b
    (env : global_env) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : bool :=
  ty_compatible_b Ω
    (normalize_assoc_ty env T_actual)
    (normalize_assoc_ty env T_expected).

Definition ty_compatible_assoc_checked
    (env : global_env) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : Prop :=
  ty_compatible_assoc_b env Ω T_actual T_expected = true.

(* Argument typing that carries the global environment needed for associated
   projection compatibility. This is not wired into the executable checker yet;
   it names the Prop-level boundary that future call-site rules should target. *)
Inductive typed_args_assoc
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> list expr -> list param -> ctx -> Prop :=
  | TArgsAssoc_Nil : forall Γ,
      typed_args_assoc env fenv Ω n Γ [] [] Γ
  | TArgsAssoc_Cons : forall Γ Γ1 Γ2 e es p ps T_e,
      typed fenv Ω n Γ e T_e Γ1 ->
      ty_compatible_assoc env Ω T_e (param_ty p) ->
      typed_args_assoc env fenv Ω n Γ1 es ps Γ2 ->
      typed_args_assoc env fenv Ω n Γ (e :: es) (p :: ps) Γ2.

Lemma typed_args_assoc_length :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc env fenv Ω n Γ args ps Γ' ->
    length args = length ps.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  induction Hargs.
  - reflexivity.
  - simpl. f_equal. exact IHHargs.
Qed.

(* Prop-level argument typing that stores only the lightweight checked
   compatibility witness. This is the bridge shape intended for checker-facing
   facts; it avoids embedding the expanded normalized compatibility proof term. *)
Inductive typed_args_assoc_checked
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    : ctx -> list expr -> list param -> ctx -> Prop :=
  | TArgsAssocChecked_Nil : forall Γ,
      typed_args_assoc_checked env fenv Ω n Γ [] [] Γ
  | TArgsAssocChecked_Cons : forall Γ Γ1 Γ2 e es p ps T_e,
      typed fenv Ω n Γ e T_e Γ1 ->
      ty_compatible_assoc_checked env Ω T_e (param_ty p) ->
      typed_args_assoc_checked env fenv Ω n Γ1 es ps Γ2 ->
      typed_args_assoc_checked env fenv Ω n Γ (e :: es) (p :: ps) Γ2.

Lemma typed_args_assoc_checked_length :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    length args = length ps.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  induction Hargs.
  - reflexivity.
  - simpl. f_equal. exact IHHargs.
Qed.
