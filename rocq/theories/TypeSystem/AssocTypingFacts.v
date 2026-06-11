From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase AssocCompatibility AlphaTyping.
From Stdlib Require Import List.
Import ListNotations.

Lemma typed_args_assoc_same_bindings :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc env fenv Ω n Γ args ps Γ' ->
    ctx_same_bindings Γ Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  induction Hargs.
  - apply ctx_same_bindings_refl.
  - eapply ctx_same_bindings_trans.
    + destruct typed_same_bindings as [Htyped _].
      eapply Htyped. exact H.
    + exact IHHargs.
Qed.

Lemma typed_args_assoc_params_of_tys_map_param_ty :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc env fenv Ω n Γ args ps Γ' ->
    typed_args_assoc env fenv Ω n Γ args
      (params_of_tys (map param_ty ps)) Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  induction Hargs.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

Lemma typed_args_assoc_param_tys :
  forall env fenv Ω n Γ args ps_shadow ps Γ',
    typed_args_assoc env fenv Ω n Γ args ps_shadow Γ' ->
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      ps_shadow ps ->
    typed_args_assoc env fenv Ω n Γ args ps Γ'.
Proof.
  intros env fenv Ω n Γ args ps_shadow ps Γ' Hargs.
  revert ps.
  induction Hargs; intros ps_shadow Hparams.
  - inversion Hparams; subst. constructor.
  - destruct ps_shadow as [|p_shadow ps_shadow]; inversion Hparams; subst.
    econstructor; eauto.
    match goal with
    | Heq : param_ty _ = param_ty _ |- _ =>
        rewrite <- Heq; assumption
    end.
Qed.

Lemma typed_args_assoc_checked_same_bindings :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    ctx_same_bindings Γ Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  induction Hargs.
  - apply ctx_same_bindings_refl.
  - eapply ctx_same_bindings_trans.
    + destruct typed_same_bindings as [Htyped _].
      eapply Htyped. exact H.
    + exact IHHargs.
Qed.

Lemma typed_args_assoc_checked_params_of_tys_map_param_ty :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    typed_args_assoc_checked env fenv Ω n Γ args
      (params_of_tys (map param_ty ps)) Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  induction Hargs.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

Lemma typed_args_assoc_checked_param_tys :
  forall env fenv Ω n Γ args ps_shadow ps Γ',
    typed_args_assoc_checked env fenv Ω n Γ args ps_shadow Γ' ->
    Forall2 (fun p_shadow p => param_ty p_shadow = param_ty p)
      ps_shadow ps ->
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ'.
Proof.
  intros env fenv Ω n Γ args ps_shadow ps Γ' Hargs.
  revert ps.
  induction Hargs; intros ps_shadow Hparams.
  - inversion Hparams; subst. constructor.
  - destruct ps_shadow as [|p_shadow ps_shadow]; inversion Hparams; subst.
    econstructor; eauto.
    match goal with
    | Heq : param_ty _ = param_ty _ |- _ =>
        rewrite <- Heq; assumption
    end.
Qed.
