From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules AssocCompatibility AlphaTyping.

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
