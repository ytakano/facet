From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker EnvStructuralRules
  EnvTypingSoundness AssocCompatibility AssocEnvStructural CheckerHrt.
From Stdlib Require Import List.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware env argument collector soundness                         *)
(* ------------------------------------------------------------------ *)

Lemma infer_env_args_collect_assoc_checked_sound :
  forall fuel env Ω n Σ args arg_tys params Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T, Σ1) ->
        typed_env_structural env Ω n Σ0 e T Σ1) ->
    check_args_assoc env Ω arg_tys params = None ->
    typed_args_env_structural_assoc env Ω n Σ args params Σ'.
Proof.
  intros fuel env Ω n Σ args.
  revert Σ.
  induction args as [|e rest IH]; intros Σ arg_tys params Σ' Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel fuel env Ω n Σ e) as [[T_e Σ1] | err] eqn:He;
      try discriminate.
    destruct (infer_env_args_collect fuel env Ω n Σ1 rest) as [[tys Σ2] | err'] eqn:Htail;
      try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_e (param_ty p)) eqn:Hcompat;
      try discriminate.
    eapply TESArgsAssoc_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * intros Σ0 e0 T0 Σ0' Hin Hinfer0.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Hinfer0.
      * exact Hcheck.
Qed.
