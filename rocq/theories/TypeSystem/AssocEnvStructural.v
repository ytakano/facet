From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase AssocCompatibility
  CheckerState TypeChecker RootProvenance EnvStructuralRules.
From Stdlib Require Import List String.
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
      ty_compatible_assoc_checked env Ω T_e (param_ty p) ->
      typed_args_env_structural_assoc env Ω n Σ1 es ps Σ2 ->
      typed_args_env_structural_assoc env Ω n Σ (e :: es) (p :: ps) Σ2.

Lemma typed_args_env_structural_assoc_length :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    List.length args = List.length ps.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  induction Hargs.
  - reflexivity.
  - simpl. f_equal. exact IHHargs.
Qed.

Lemma typed_args_env_structural_assoc_cons_inv :
  forall env Ω n Σ e es p ps Σ',
    typed_args_env_structural_assoc env Ω n Σ (e :: es) (p :: ps) Σ' ->
    exists T_e Σ1,
      typed_env_structural env Ω n Σ e T_e Σ1 /\
      ty_compatible_assoc_checked env Ω T_e (param_ty p) /\
      typed_args_env_structural_assoc env Ω n Σ1 es ps Σ'.
Proof.
  intros env Ω n Σ e es p ps Σ' Htyped.
  inversion Htyped; subst.
  exists T_e, Σ1. repeat split; assumption.
Qed.

Lemma typed_args_env_structural_assoc_params_of_tys_map_param_ty :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    typed_args_env_structural_assoc env Ω n Σ args
      (params_of_tys (map param_ty ps)) Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  induction Hargs.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

Lemma typed_args_env_structural_assoc_same_bindings :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args ps Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  induction Hargs.
  - apply sctx_same_bindings_refl.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings. exact H.
    + exact IHHargs.
Qed.

(* Roots-aware argument typing with associated projection compatibility. This
   mirrors typed_args_roots at the argument-list boundary only; checker call
   sites are still intentionally unchanged. *)
Inductive typed_args_roots_assoc
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param ->
      sctx -> root_env -> list root_set -> Prop :=
  | TERArgsAssoc_Nil : forall R Σ,
      typed_args_roots_assoc env Ω n R Σ [] [] Σ R []
  | TERArgsAssoc_Cons : forall R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest,
      typed_env_roots env Ω n R Σ e T_e Σ1 R1 roots ->
      ty_compatible_assoc_checked env Ω T_e (param_ty p) ->
      typed_args_roots_assoc env Ω n R1 Σ1 es ps Σ2 R2 roots_rest ->
      typed_args_roots_assoc env Ω n R Σ (e :: es) (p :: ps)
        Σ2 R2 (roots :: roots_rest).

Lemma typed_args_roots_assoc_length :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    List.length args = List.length ps.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  induction Hargs.
  - reflexivity.
  - simpl. f_equal. exact IHHargs.
Qed.

Lemma typed_args_roots_assoc_cons_inv :
  forall env Ω n R Σ e es p ps Σ' R' roots roots_rest,
    typed_args_roots_assoc env Ω n R Σ (e :: es) (p :: ps) Σ' R'
      (roots :: roots_rest) ->
    exists T_e Σ1 R1,
      typed_env_roots env Ω n R Σ e T_e Σ1 R1 roots /\
      ty_compatible_assoc_checked env Ω T_e (param_ty p) /\
      typed_args_roots_assoc env Ω n R1 Σ1 es ps Σ' R' roots_rest.
Proof.
  intros env Ω n R Σ e es p ps Σ' R' roots roots_rest Htyped.
  inversion Htyped; subst.
  exists T_e, Σ1, R1. repeat split; assumption.
Qed.

Lemma typed_args_roots_assoc_arg_roots_length :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    List.length arg_roots = List.length ps.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  induction Hargs; simpl; auto.
Qed.

Lemma typed_args_roots_assoc_arg_roots_args_length :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    List.length arg_roots = List.length args.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  induction Hargs; simpl; auto.
Qed.

Lemma typed_args_roots_assoc_params_of_tys_map_param_ty :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    typed_args_roots_assoc env Ω n R Σ args
      (params_of_tys (map param_ty ps)) Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  induction Hargs.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

Lemma typed_args_roots_assoc_structural :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    typed_args_env_structural_assoc env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  induction Hargs.
  - constructor.
  - econstructor.
    + eapply typed_env_roots_structural. exact H.
    + exact H0.
    + exact IHHargs.
Qed.

(* Field-list typing with associated projection compatibility for struct fields.
   This is a specification bridge; struct literal checker rules are not wired to
   it yet. *)
Inductive typed_fields_env_structural_assoc
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> sctx -> list (string * expr) ->
      list field_def -> sctx -> Prop :=
  | TESFieldsAssoc_Nil : forall lts args Σ fields,
      typed_fields_env_structural_assoc env Ω n lts args Σ fields [] Σ
  | TESFieldsAssoc_Cons : forall lts args Σ Σ1 Σ2 fields f rest e_field T_field,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_structural env Ω n Σ e_field T_field Σ1 ->
      ty_compatible_assoc_checked env Ω T_field
        (instantiate_struct_field_ty lts args f) ->
      typed_fields_env_structural_assoc env Ω n lts args Σ1 fields rest Σ2 ->
      typed_fields_env_structural_assoc env Ω n lts args Σ fields (f :: rest) Σ2.

Lemma typed_fields_env_structural_assoc_nil_inv :
  forall env Ω n lts args Σ fields Σ',
    typed_fields_env_structural_assoc env Ω n lts args Σ fields [] Σ' ->
    Σ' = Σ.
Proof.
  intros env Ω n lts args Σ fields Σ' Hfields.
  inversion Hfields; subst. reflexivity.
Qed.

Lemma typed_fields_env_structural_assoc_cons_inv :
  forall env Ω n lts args Σ fields f rest Σ',
    typed_fields_env_structural_assoc env Ω n lts args Σ fields
      (f :: rest) Σ' ->
    exists e_field T_field Σ1,
      lookup_field_b (field_name f) fields = Some e_field /\
      typed_env_structural env Ω n Σ e_field T_field Σ1 /\
      ty_compatible_assoc_checked env Ω T_field
        (instantiate_struct_field_ty lts args f) /\
      typed_fields_env_structural_assoc env Ω n lts args Σ1 fields
        rest Σ'.
Proof.
  intros env Ω n lts args Σ fields f rest Σ' Htyped.
  inversion Htyped; subst.
  exists e_field, T_field, Σ1. repeat split; assumption.
Qed.

Lemma typed_args_roots_assoc_same_bindings :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots ->
    sctx_same_bindings Σ Σ' .
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  eapply typed_args_env_structural_assoc_same_bindings.
  eapply typed_args_roots_assoc_structural. exact Hargs.
Qed.

Lemma typed_fields_env_structural_assoc_same_bindings :
  forall env Ω n lts args Σ fields defs Σ',
    typed_fields_env_structural_assoc env Ω n lts args Σ fields defs Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  intros env Ω n lts args Σ fields defs Σ' Hfields.
  induction Hfields.
  - apply sctx_same_bindings_refl.
  - eapply sctx_same_bindings_trans.
    + eapply typed_env_structural_same_bindings. exact H0.
    + exact IHHfields.
Qed.

Inductive typed_fields_roots_assoc
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> root_env -> sctx ->
      list (string * expr) -> list field_def -> sctx -> root_env -> root_set -> Prop :=
  | TERFieldsAssoc_Nil : forall lts args R Σ fields,
      typed_fields_roots_assoc env Ω n lts args R Σ fields [] Σ R []
  | TERFieldsAssoc_Cons : forall lts args R R1 R2 Σ Σ1 Σ2 fields f rest
      e_field T_field roots_field roots_rest,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field ->
      ty_compatible_assoc_checked env Ω T_field
        (instantiate_struct_field_ty lts args f) ->
      typed_fields_roots_assoc env Ω n lts args R1 Σ1 fields rest
        Σ2 R2 roots_rest ->
      typed_fields_roots_assoc env Ω n lts args R Σ fields (f :: rest)
        Σ2 R2 (root_set_union roots_field roots_rest).

Lemma typed_fields_roots_assoc_nil_inv :
  forall env Ω n lts args R Σ fields Σ' R' roots,
    typed_fields_roots_assoc env Ω n lts args R Σ fields [] Σ' R' roots ->
    Σ' = Σ /\ R' = R /\ roots = [].
Proof.
  intros env Ω n lts args R Σ fields Σ' R' roots Hfields.
  inversion Hfields; subst. repeat split.
Qed.

Lemma typed_fields_roots_assoc_cons_inv :
  forall env Ω n lts args R Σ fields f rest Σ' R' roots,
    typed_fields_roots_assoc env Ω n lts args R Σ fields
      (f :: rest) Σ' R' roots ->
    exists e_field T_field roots_field roots_rest Σ1 R1,
      lookup_field_b (field_name f) fields = Some e_field /\
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field /\
      ty_compatible_assoc_checked env Ω T_field
        (instantiate_struct_field_ty lts args f) /\
      typed_fields_roots_assoc env Ω n lts args R1 Σ1 fields rest
        Σ' R' roots_rest /\
      roots = root_set_union roots_field roots_rest.
Proof.
  intros env Ω n lts args R Σ fields f rest Σ' R' roots Htyped.
  inversion Htyped; subst.
  exists e_field, T_field, roots_field, roots_rest, Σ1, R1.
  repeat split; assumption.
Qed.

Lemma typed_fields_roots_assoc_structural :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_assoc env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_env_structural_assoc env Ω n lts args Σ fields defs Σ'.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots Hfields.
  induction Hfields.
  - constructor.
  - econstructor.
    + exact H.
    + eapply typed_env_roots_structural. exact H0.
    + exact H1.
    + exact IHHfields.
Qed.

Lemma typed_fields_roots_assoc_same_bindings :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_assoc env Ω n lts args R Σ fields defs Σ' R' roots ->
    sctx_same_bindings Σ Σ' .
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots Hfields.
  eapply typed_fields_env_structural_assoc_same_bindings.
  eapply typed_fields_roots_assoc_structural. exact Hfields.
Qed.

Lemma typed_args_env_structural_assoc_param_tys :
  forall env Ω n Σ args ps_shadow ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args ps_shadow Σ' ->
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      ps_shadow ps ->
    typed_args_env_structural_assoc env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n Σ args ps_shadow ps Σ' Hargs Hparams.
  revert ps Hparams.
  induction Hargs; intros ps' Hparams.
  - inversion Hparams; subst. constructor.
  - inversion Hparams; subst.
    econstructor.
    + exact H.
    + rewrite <- H3. exact H0.
    + apply IHHargs. exact H5.
Qed.

Lemma typed_args_roots_assoc_param_tys :
  forall env Ω n R Σ args ps_shadow ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args ps_shadow Σ' R' arg_roots ->
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      ps_shadow ps ->
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args ps_shadow ps Σ' R' arg_roots Hargs Hparams.
  revert ps Hparams.
  induction Hargs; intros ps' Hparams.
  - inversion Hparams; subst. constructor.
  - inversion Hparams; subst.
    econstructor.
    + exact H.
    + rewrite <- H3. exact H0.
    + apply IHHargs. exact H5.
Qed.

Lemma assoc_params_of_tys_map_param_ty_Forall2 :
  forall ps,
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      (params_of_tys (map param_ty ps)) ps.
Proof.
  induction ps as [| p ps IH].
  - constructor.
  - simpl. constructor.
    + reflexivity.
    + exact IH.
Qed.

Lemma typed_args_env_structural_assoc_params_of_tys_map_param_ty_back :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural_assoc env Ω n Σ args
      (params_of_tys (map param_ty ps)) Σ' ->
    typed_args_env_structural_assoc env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  eapply typed_args_env_structural_assoc_param_tys.
  - exact Hargs.
  - apply assoc_params_of_tys_map_param_ty_Forall2.
Qed.

Lemma typed_args_roots_assoc_params_of_tys_map_param_ty_back :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots_assoc env Ω n R Σ args
      (params_of_tys (map param_ty ps)) Σ' R' arg_roots ->
    typed_args_roots_assoc env Ω n R Σ args ps Σ' R' arg_roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Hargs.
  eapply typed_args_roots_assoc_param_tys.
  - exact Hargs.
  - apply assoc_params_of_tys_map_param_ty_Forall2.
Qed.
