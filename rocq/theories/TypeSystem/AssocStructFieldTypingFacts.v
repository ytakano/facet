From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase
  AssocCompatibility AlphaTyping.
From Stdlib Require Import List String.
Import ListNotations.

(* Prop-level struct-field typing that stores only the lightweight checked
   associated-projection compatibility witness. *)
Inductive typed_struct_fields_assoc_checked
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    (lts : list lifetime) (args : list Ty)
    : ctx -> list (string * expr) -> list field_def -> ctx -> Prop :=
  | TSFieldsAssocChecked_Nil : forall Γ fields,
      typed_struct_fields_assoc_checked env fenv Ω n lts args Γ fields [] Γ
  | TSFieldsAssocChecked_Cons :
      forall Γ Γ1 Γ2 fields f rest e_field T_field,
      lookup_field (field_name f)
        (struct_fields (MkStructDef "" 0 0 [] (f :: rest))) = Some f ->
      In (field_name f, e_field) fields ->
      typed fenv Ω n Γ e_field T_field Γ1 ->
      ty_compatible_assoc_checked env Ω T_field
        (instantiate_struct_field_ty lts args f) ->
      typed_struct_fields_assoc_checked env fenv Ω n lts args Γ1 fields
        rest Γ2 ->
      typed_struct_fields_assoc_checked env fenv Ω n lts args Γ fields
        (f :: rest) Γ2.

Lemma typed_struct_fields_assoc_checked_nil_inv :
  forall env fenv Ω n lts args Γ fields Γ',
    typed_struct_fields_assoc_checked env fenv Ω n lts args Γ fields [] Γ' ->
    Γ' = Γ.
Proof.
  intros env fenv Ω n lts args Γ fields Γ' Hfields.
  inversion Hfields; subst. reflexivity.
Qed.

Lemma typed_struct_fields_assoc_checked_cons_inv :
  forall env fenv Ω n lts args Γ fields f rest Γ',
    typed_struct_fields_assoc_checked env fenv Ω n lts args Γ fields
      (f :: rest) Γ' ->
    exists e_field T_field Γ1,
      lookup_field (field_name f)
        (struct_fields (MkStructDef "" 0 0 [] (f :: rest))) = Some f /\
      In (field_name f, e_field) fields /\
      typed fenv Ω n Γ e_field T_field Γ1 /\
      ty_compatible_assoc_checked env Ω T_field
        (instantiate_struct_field_ty lts args f) /\
      typed_struct_fields_assoc_checked env fenv Ω n lts args Γ1 fields
        rest Γ'.
Proof.
  intros env fenv Ω n lts args Γ fields f rest Γ' Hfields.
  inversion Hfields; subst.
  exists e_field, T_field, Γ1. repeat split; assumption.
Qed.

Lemma typed_struct_fields_assoc_checked_same_bindings :
  forall env fenv Ω n lts args Γ fields defs Γ',
    typed_struct_fields_assoc_checked env fenv Ω n lts args Γ fields
      defs Γ' ->
    ctx_same_bindings Γ Γ'.
Proof.
  intros env fenv Ω n lts args Γ fields defs Γ' Hfields.
  induction Hfields.
  - apply ctx_same_bindings_refl.
  - eapply ctx_same_bindings_trans.
    + destruct typed_same_bindings as [Htyped _].
      eapply Htyped. exact H1.
    + exact IHHfields.
Qed.
