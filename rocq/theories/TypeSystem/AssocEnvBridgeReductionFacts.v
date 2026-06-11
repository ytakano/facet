From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker RootProvenance EnvStructuralRules
  AssocCompatibility
  AssocCheckedBridgeReductionFacts AssocEnvStructural.
From Stdlib Require Import List String.
Import ListNotations.

Inductive typed_args_env_structural_plain_witness
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> list expr -> list param -> sctx -> Prop :=
  | TESArgsPlainWitness_Nil : forall Σ,
      typed_args_env_structural_plain_witness env Ω n Σ [] [] Σ
  | TESArgsPlainWitness_Cons : forall Σ Σ1 Σ2 e es p ps T_e,
      typed_env_structural env Ω n Σ e T_e Σ1 ->
      ty_compatible Ω T_e (param_ty p) ->
      typed_args_env_structural_plain_witness env Ω n Σ1 es ps Σ2 ->
      typed_args_env_structural_plain_witness env Ω n Σ (e :: es) (p :: ps) Σ2.

Inductive typed_args_roots_plain_witness
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param ->
      sctx -> root_env -> list root_set -> Prop :=
  | TERArgsPlainWitness_Nil : forall R Σ,
      typed_args_roots_plain_witness env Ω n R Σ [] [] Σ R []
  | TERArgsPlainWitness_Cons : forall R R1 R2 Σ Σ1 Σ2 e es p ps T_e
      roots roots_rest,
      typed_env_roots env Ω n R Σ e T_e Σ1 R1 roots ->
      ty_compatible Ω T_e (param_ty p) ->
      typed_args_roots_plain_witness env Ω n R1 Σ1 es ps Σ2 R2 roots_rest ->
      typed_args_roots_plain_witness env Ω n R Σ (e :: es) (p :: ps)
        Σ2 R2 (roots :: roots_rest).

Inductive typed_fields_env_structural_plain_witness
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> sctx -> list (string * expr) ->
      list field_def -> sctx -> Prop :=
  | TESFieldsPlainWitness_Nil : forall lts args Σ fields,
      typed_fields_env_structural_plain_witness env Ω n lts args Σ fields [] Σ
  | TESFieldsPlainWitness_Cons : forall lts args Σ Σ1 Σ2 fields f rest
      e_field T_field,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_structural env Ω n Σ e_field T_field Σ1 ->
      ty_compatible Ω T_field (instantiate_struct_field_ty lts args f) ->
      typed_fields_env_structural_plain_witness env Ω n lts args Σ1 fields
        rest Σ2 ->
      typed_fields_env_structural_plain_witness env Ω n lts args Σ fields
        (f :: rest) Σ2.

Inductive typed_fields_roots_plain_witness
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> root_env -> sctx ->
      list (string * expr) -> list field_def -> sctx -> root_env ->
      root_set -> Prop :=
  | TERFieldsPlainWitness_Nil : forall lts args R Σ fields,
      typed_fields_roots_plain_witness env Ω n lts args R Σ fields [] Σ R []
  | TERFieldsPlainWitness_Cons : forall lts args R R1 R2 Σ Σ1 Σ2 fields
      f rest e_field T_field roots_field roots_rest,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field ->
      ty_compatible Ω T_field (instantiate_struct_field_ty lts args f) ->
      typed_fields_roots_plain_witness env Ω n lts args R1 Σ1 fields rest
        Σ2 R2 roots_rest ->
      typed_fields_roots_plain_witness env Ω n lts args R Σ fields
        (f :: rest) Σ2 R2 (root_set_union roots_field roots_rest).

Lemma typed_args_env_structural_assoc_reduces_to_plain :
  forall env Ω n Σ args ps Σ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    typed_args_env_structural_plain_witness env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_args_roots_assoc_reduces_to_plain :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    typed_args_roots_plain_witness env Ω n R Σ args ps Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_fields_env_structural_assoc_reduces_to_plain :
  forall env Ω n lts args Σ fields defs Σ',
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_fields_env_structural_assoc env Ω n lts args Σ fields defs Σ' ->
    typed_fields_env_structural_plain_witness env Ω n lts args Σ fields
      defs Σ'.
Proof.
  intros env Ω n lts args Σ fields defs Σ' Hcompat Hfields.
  induction Hfields.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_fields_roots_assoc_reduces_to_plain :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    typed_fields_roots_assoc env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_roots_plain_witness env Ω n lts args R Σ fields defs Σ' R'
      roots.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots Hcompat Hfields.
  induction Hfields.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_args_env_structural_assoc_reduces_to_env_structural :
  forall env Ω n Σ args ps Σ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    typed_args_env_structural env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_args_roots_assoc_reduces_to_roots :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    typed_args_roots env Ω n R Σ args ps Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hcompat Hargs.
  induction Hargs.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_fields_env_structural_assoc_reduces_to_env_structural :
  forall env Ω n lts args Σ fields defs Σ',
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_fields_env_structural_assoc env Ω n lts args Σ fields defs Σ' ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ'.
Proof.
  intros env Ω n lts args Σ fields defs Σ' Hcompat Hfields.
  induction Hfields.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma typed_fields_roots_assoc_reduces_to_roots :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    typed_fields_roots_assoc env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots Hcompat Hfields.
  induction Hfields.
  - constructor.
  - econstructor; eauto.
Qed.
