From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase
  AssocCompatibility AssocTypingFacts AlphaTyping.
From Stdlib Require Import List.
Import ListNotations.

(* Prop-level enum-payload typing that stores only lightweight checked
   associated-projection compatibility witnesses through typed_args_assoc_checked.
   The expected payload types are the instantiated enum variant field types.
*)
Definition typed_enum_payloads_assoc_checked
    (env : global_env) (fenv : list fn_def) (Ω : outlives_ctx) (n : nat)
    (lts variant_lts : list lifetime) (args : list Ty)
    (Γ : ctx) (payloads : list expr) (fields : list Ty) (Γ': ctx) : Prop :=
  typed_args_assoc_checked env fenv Ω n Γ payloads
    (params_of_tys (map (instantiate_enum_variant_field_ty lts variant_lts args) fields))
    Γ'.

Lemma typed_enum_payloads_assoc_checked_inv :
  forall env fenv Ω n lts variant_lts args Γ payloads fields Γ',
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads fields Γ' ->
    typed_args_assoc_checked env fenv Ω n Γ payloads
      (params_of_tys
        (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)) Γ'.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads fields Γ' Hpayloads.
  exact Hpayloads.
Qed.

Lemma typed_enum_payloads_assoc_checked_same_bindings :
  forall env fenv Ω n lts variant_lts args Γ payloads fields Γ',
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads fields Γ' ->
    ctx_same_bindings Γ Γ'.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads fields Γ' Hpayloads.
  eapply typed_args_assoc_checked_same_bindings. exact Hpayloads.
Qed.

Lemma typed_enum_payloads_assoc_checked_nil_inv :
  forall env fenv Ω n lts variant_lts args Γ payloads Γ',
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads [] Γ' ->
    payloads = [] /\ Γ' = Γ.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads Γ' Hpayloads.
  unfold typed_enum_payloads_assoc_checked in Hpayloads.
  destruct payloads as [|payload payloads].
  - inversion Hpayloads; subst. split; reflexivity.
  - inversion Hpayloads.
Qed.

Lemma typed_enum_payloads_assoc_checked_cons_inv :
  forall env fenv Ω n lts variant_lts args Γ payloads field fields Γ',
    typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ
      payloads (field :: fields) Γ' ->
    exists payload payloads_tail actual Γ1,
      payloads = payload :: payloads_tail /\
      typed fenv Ω n Γ payload actual Γ1 /\
      ty_compatible_assoc_checked env Ω actual
        (instantiate_enum_variant_field_ty lts variant_lts args field) /\
      typed_enum_payloads_assoc_checked env fenv Ω n lts variant_lts args Γ1
        payloads_tail fields Γ'.
Proof.
  intros env fenv Ω n lts variant_lts args Γ payloads field fields Γ' Hpayloads.
  unfold typed_enum_payloads_assoc_checked in Hpayloads.
  destruct payloads as [|payload payloads_tail].
  - inversion Hpayloads.
  - simpl in Hpayloads. inversion Hpayloads; subst.
    exists payload, payloads_tail, T_e, Γ1. repeat split; assumption.
Qed.
