From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase AssocCompatibility CheckerState
  EnvStructuralRules.
From Stdlib Require Import List.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* Env-structural argument typing that keeps associated projection compatibility
   at the global-environment boundary. This relation is specification support
   only; executable checker call sites still use the existing helpers. *)
Inductive typed_args_env_structural_assoc
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> list expr -> list param -> sctx -> Prop :=
  | TESArgsAssoc_Nil : forall Σ,
      typed_args_env_structural_assoc env Ω n Σ [] [] Σ
  | TESArgsAssoc_Cons : forall Σ Σ1 Σ2 e es p ps T_e,
      typed_env_structural env Ω n Σ e T_e Σ1 ->
      ty_compatible_assoc_b env Ω T_e (param_ty p) = true ->
      typed_args_env_structural_assoc env Ω n Σ1 es ps Σ2 ->
      typed_args_env_structural_assoc env Ω n Σ (e :: es) (p :: ps) Σ2.

Lemma typed_args_env_structural_assoc_length :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    length args = length ps.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  induction Hargs.
  - reflexivity.
  - simpl. f_equal. exact IHHargs.
Qed.
