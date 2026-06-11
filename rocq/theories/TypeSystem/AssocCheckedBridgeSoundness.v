From Facet.TypeSystem Require Import
  AssocCompatibility AssocCheckedBridgeReductionFacts CompatBoolSoundness.

Lemma ty_compatible_assoc_checked_reduces_to_assoc_proved :
  forall env Ω,
    ty_compatible_assoc_checked_reduces_to_assoc env Ω.
Proof.
  intros env Ω actual expected Hcompat.
  exact (ty_compatible_assoc_checked_sound env Ω actual expected Hcompat).
Qed.

Lemma typed_args_assoc_checked_sound :
  forall env fenv Ω n Γ args ps Γ',
    typed_args_assoc_checked env fenv Ω n Γ args ps Γ' ->
    typed_args_assoc env fenv Ω n Γ args ps Γ'.
Proof.
  intros env fenv Ω n Γ args ps Γ' Hargs.
  eapply typed_args_assoc_checked_reduces_to_assoc.
  - apply ty_compatible_assoc_checked_reduces_to_assoc_proved.
  - exact Hargs.
Qed.
