From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerHrt AssocCompatibility.
From Stdlib Require Import List.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Associated-projection argument helper boolean facts                   *)
(* ------------------------------------------------------------------ *)

Lemma check_arg_tys_assoc_true :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    Forall2
      (fun actual expected =>
         ty_compatible_assoc_b env Ω actual expected = true)
      arg_tys param_tys.
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [|arg rest IH]; intros param_tys H;
    destruct param_tys as [|param rest_params]; simpl in H; try discriminate.
  - constructor.
  - destruct (ty_compatible_assoc_b env Ω arg param) eqn:Hcompat; try discriminate.
    constructor.
    + exact Hcompat.
    + apply IH. exact H.
Qed.

Lemma check_args_assoc_true :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    Forall2
      (fun actual p =>
         ty_compatible_assoc_b env Ω actual (param_ty p) = true)
      arg_tys params.
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [|arg rest IH]; intros params H;
    destruct params as [|param rest_params]; simpl in H; try discriminate.
  - constructor.
  - destruct (ty_compatible_assoc_b env Ω arg (param_ty param)) eqn:Hcompat;
      try discriminate.
    constructor.
    + exact Hcompat.
    + apply IH. exact H.
Qed.

Lemma check_args_assoc_param_tys_true :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    Forall2
      (fun actual expected =>
         ty_compatible_assoc_b env Ω actual expected = true)
      arg_tys (map param_ty params).
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [|arg rest IH]; intros params H;
    destruct params as [|param rest_params]; simpl in H; try discriminate.
  - constructor.
  - destruct (ty_compatible_assoc_b env Ω arg (param_ty param)) eqn:Hcompat;
      try discriminate.
    simpl. constructor.
    + exact Hcompat.
    + apply IH. exact H.
Qed.

Lemma check_arg_tys_assoc_length :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    length arg_tys = length param_tys.
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [|arg rest IH]; intros param_tys H;
    destruct param_tys as [|param rest_params]; simpl in H; try discriminate.
  - reflexivity.
  - destruct (ty_compatible_assoc_b env Ω arg param); try discriminate.
    simpl. f_equal. apply IH. exact H.
Qed.

Lemma check_args_assoc_length :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    length arg_tys = length params.
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [|arg rest IH]; intros params H;
    destruct params as [|param rest_params]; simpl in H; try discriminate.
  - reflexivity.
  - destruct (ty_compatible_assoc_b env Ω arg (param_ty param));
      try discriminate.
    simpl. f_equal. apply IH. exact H.
Qed.
