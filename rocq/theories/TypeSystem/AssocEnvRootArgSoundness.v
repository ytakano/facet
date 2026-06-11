From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker RootProvenance
  EnvStructuralRules EnvRootSoundness AssocCompatibility AssocEnvStructural
  CheckerHrt.
From Stdlib Require Import List.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware roots argument collector soundness                       *)
(* ------------------------------------------------------------------ *)

Lemma infer_env_args_collect_roots_assoc_checked_sound :
  forall fuel env Ω n R Σ args arg_tys params Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    check_args_assoc env Ω arg_tys params = None ->
    typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros fuel env Ω n R Σ args.
  revert R Σ.
  induction args as [|e rest IH]; intros R Σ arg_tys params Σ' R' arg_roots
      Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e)
      as [[[[T_e Σ1] R1] roots_e] | err] eqn:He; try discriminate.
    destruct (infer_env_args_collect_roots fuel env Ω n R1 Σ1 rest)
      as [[[[tys Σ2] R2] roots_rest] | err] eqn:Htail; try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_e (param_ty p)) eqn:Hcompat;
      try discriminate.
    eapply TERArgsAssoc_Cons.
    + eapply Hexpr. exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * exact Hexpr.
      * exact Hcheck.
Qed.
