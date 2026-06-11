From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker AssocCompatibility
  AssocHrtFacts AssocCheckedBridgeReductionFacts
  AssocStructFieldBridgeReductionFacts AssocEnvBridgeReductionFacts.
From Stdlib Require Import List.

Lemma assoc_checked_arg_tys_reduces_to_assoc :
  forall env Ω arg_tys param_tys,
    ty_compatible_assoc_checked_reduces_to_assoc env Ω ->
    assoc_checked_arg_tys env Ω arg_tys param_tys ->
    Forall2
      (fun actual expected => ty_compatible_assoc env Ω actual expected)
      arg_tys param_tys /\
    length arg_tys = length param_tys.
Proof.
  intros env Ω arg_tys param_tys Hcompat Hargs.
  unfold assoc_checked_arg_tys in Hargs.
  destruct Hargs as [Hargs Hlen].
  split.
  - eapply Forall2_impl; [| exact Hargs].
    intros actual expected Hchecked.
    apply Hcompat. exact Hchecked.
  - exact Hlen.
Qed.

Lemma assoc_checked_arg_tys_reduces_to_plain :
  forall env Ω arg_tys param_tys,
    ty_compatible_assoc_checked_reduces_to_plain env Ω ->
    assoc_checked_arg_tys env Ω arg_tys param_tys ->
    Forall2
      (fun actual expected => ty_compatible Ω actual expected)
      arg_tys param_tys /\
    length arg_tys = length param_tys.
Proof.
  intros env Ω arg_tys param_tys Hcompat Hargs.
  unfold assoc_checked_arg_tys in Hargs.
  destruct Hargs as [Hargs Hlen].
  split.
  - eapply Forall2_impl; [| exact Hargs].
    intros actual expected Hchecked.
    apply Hcompat. exact Hchecked.
  - exact Hlen.
Qed.

Lemma assoc_checked_arg_tys_reduces_to_bool :
  forall env Ω arg_tys param_tys,
    ty_compatible_assoc_checked_reduces_to_bool env Ω ->
    assoc_checked_arg_tys env Ω arg_tys param_tys ->
    Forall2
      (fun actual expected => ty_compatible_b Ω actual expected = true)
      arg_tys param_tys /\
    length arg_tys = length param_tys.
Proof.
  intros env Ω arg_tys param_tys Hcompat Hargs.
  unfold assoc_checked_arg_tys in Hargs.
  destruct Hargs as [Hargs Hlen].
  split.
  - eapply Forall2_impl; [| exact Hargs].
    intros actual expected Hchecked.
    apply Hcompat. exact Hchecked.
  - exact Hlen.
Qed.
