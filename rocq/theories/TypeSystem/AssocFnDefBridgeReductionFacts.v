From Facet.TypeSystem Require Import
  TypingRules Syntax AssocFnDefTypingFacts AssocStructFieldBridgeReductionFacts.

Lemma typed_fn_def_assoc_checked_reduces_to_fn_def :
  forall env fenv f,
    ty_compatible_assoc_checked_reduces_to_plain env (fn_outlives f) ->
    typed_fn_def_assoc_checked env fenv f ->
    typed_fn_def fenv f.
Proof.
  intros env fenv f Hcompat Hfn.
  destruct (typed_fn_def_assoc_checked_inv _ _ _ Hfn)
    as [T_body [Gamma_out [Htyped [Hchecked Hparams]]]].
  exists T_body, Gamma_out.
  repeat split; eauto.
Qed.
