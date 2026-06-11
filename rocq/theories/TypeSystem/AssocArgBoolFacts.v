From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerHrt TypeChecker AssocCompatibility
  CompatBoolSoundness.
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
         ty_compatible_assoc_checked env Ω actual expected)
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

Lemma check_arg_tys_assoc_sound :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    Forall2
      (fun actual expected =>
         ty_compatible_assoc env Ω actual expected)
      arg_tys param_tys.
Proof.
  intros env Ω arg_tys param_tys Hcheck.
  eapply Forall2_impl.
  - intros actual expected Hcompat.
    exact (ty_compatible_assoc_checked_sound
      env Ω actual expected Hcompat).
  - apply (check_arg_tys_assoc_true env Ω). exact Hcheck.
Qed.

Lemma check_args_assoc_true :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    Forall2
      (fun actual p =>
         ty_compatible_assoc_checked env Ω actual (param_ty p))
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

Lemma check_args_assoc_sound :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    Forall2
      (fun actual p =>
         ty_compatible_assoc env Ω actual (param_ty p))
      arg_tys params.
Proof.
  intros env Ω arg_tys params Hcheck.
  eapply Forall2_impl.
  - intros actual p Hcompat.
    exact (ty_compatible_assoc_checked_sound
      env Ω actual (param_ty p) Hcompat).
  - apply (check_args_assoc_true env Ω). exact Hcheck.
Qed.

Lemma check_args_assoc_param_tys_true :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    Forall2
      (fun actual expected =>
         ty_compatible_assoc_checked env Ω actual expected)
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

Lemma check_args_assoc_param_tys_sound :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys params = None ->
    Forall2
      (fun actual expected =>
         ty_compatible_assoc env Ω actual expected)
      arg_tys (map param_ty params).
Proof.
  intros env Ω arg_tys params Hcheck.
  eapply Forall2_impl.
  - intros actual expected Hcompat.
    exact (ty_compatible_assoc_checked_sound
      env Ω actual expected Hcompat).
  - apply (check_args_assoc_param_tys_true env Ω). exact Hcheck.
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

Lemma check_arg_tys_assoc_params_of_tys :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys =
    check_args_assoc env Ω arg_tys (params_of_tys param_tys).
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [| a arg_tys IH]; intros param_tys.
  - destruct param_tys; reflexivity.
  - destruct param_tys as [| p ps]; [reflexivity |].
    simpl. destruct (ty_compatible_assoc_b env Ω a p); [apply IH | reflexivity].
Qed.

Lemma check_arg_tys_assoc_params_of_tys_true :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    Forall2
      (fun actual p =>
         ty_compatible_assoc_checked env Ω actual (param_ty p))
      arg_tys (params_of_tys param_tys).
Proof.
  intros env Ω arg_tys param_tys Hcheck.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  apply (check_args_assoc_true env Ω). exact Hcheck.
Qed.

Lemma check_arg_tys_assoc_params_of_tys_sound :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    Forall2
      (fun actual p =>
         ty_compatible_assoc env Ω actual (param_ty p))
      arg_tys (params_of_tys param_tys).
Proof.
  intros env Ω arg_tys param_tys Hcheck.
  eapply Forall2_impl.
  - intros actual p Hcompat.
    exact (ty_compatible_assoc_checked_sound
      env Ω actual (param_ty p) Hcompat).
  - apply (check_arg_tys_assoc_params_of_tys_true env Ω). exact Hcheck.
Qed.

Lemma check_arg_tys_assoc_params_of_tys_length :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    length arg_tys = length (params_of_tys param_tys).
Proof.
  intros env Ω arg_tys param_tys Hcheck.
  rewrite check_arg_tys_assoc_params_of_tys in Hcheck.
  apply (check_args_assoc_length env Ω). exact Hcheck.
Qed.

Lemma check_args_assoc_params_of_tys_map_param_ty :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys (params_of_tys (map param_ty params)) =
    check_args_assoc env Ω arg_tys params.
Proof.
  intros env Ω arg_tys.
  induction arg_tys as [| arg rest IH]; intros params.
  - destruct params; reflexivity.
  - destruct params as [| p ps]; [reflexivity |].
    simpl. destruct (ty_compatible_assoc_b env Ω arg (param_ty p));
      [apply IH | reflexivity].
Qed.

Lemma check_args_assoc_params_of_tys_map_param_ty_true :
  forall env Ω arg_tys params,
    check_args_assoc env Ω arg_tys (params_of_tys (map param_ty params)) = None ->
    check_args_assoc env Ω arg_tys params = None.
Proof.
  intros env Ω arg_tys params Hcheck.
  rewrite <- check_args_assoc_params_of_tys_map_param_ty.
  exact Hcheck.
Qed.

Lemma check_arg_tys_assoc_map_param_ty :
  forall env Ω arg_tys params,
    check_arg_tys_assoc env Ω arg_tys (map param_ty params) =
    check_args_assoc env Ω arg_tys params.
Proof.
  intros env Ω arg_tys params.
  rewrite check_arg_tys_assoc_params_of_tys.
  apply check_args_assoc_params_of_tys_map_param_ty.
Qed.

Lemma check_arg_tys_assoc_map_param_ty_true :
  forall env Ω arg_tys params,
    check_arg_tys_assoc env Ω arg_tys (map param_ty params) = None ->
    check_args_assoc env Ω arg_tys params = None.
Proof.
  intros env Ω arg_tys params Hcheck.
  rewrite <- check_arg_tys_assoc_map_param_ty.
  exact Hcheck.
Qed.

Lemma infer_call_args_assoc_sound_v2 :
  forall env fenv Ω n Γ args arg_tys params Γ',
    infer_args_collect fenv Ω n Γ args = infer_ok (arg_tys, Γ') ->
    (forall Γ0 e T Γ1,
        In e args ->
        infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
        typed fenv Ω n Γ0 e T Γ1) ->
    check_args_assoc env Ω arg_tys params = None ->
    typed_args_assoc env fenv Ω n Γ args params Γ'.
Proof.
  intros env fenv Ω n Γ args.
  revert Γ.
  induction args as [| e es IH]; intros Γ arg_tys params Γ' Hcollect Hexpr Hcheck.
  - simpl in Hcollect. injection Hcollect as <- <-.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core fenv Ω n Γ e) as [[T_e Γ1] | err] eqn:He;
      [| discriminate].
    destruct (infer_args_collect fenv Ω n Γ1 es) as [[tys Γ2] | err']
      eqn:Htail; [| discriminate].
    injection Hcollect as <- <-.
    destruct params as [| p ps]; [discriminate |].
    simpl in Hcheck.
    destruct (ty_compatible_assoc_b env Ω T_e (param_ty p)) eqn:Hcompat;
      [| discriminate].
    eapply TArgsAssoc_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + apply ty_compatible_assoc_checked_sound.
      exact Hcompat.
    + eapply IH.
      * exact Htail.
      * intros Γ0 e0 T0 Γ0' Hin Hinfer0.
        eapply Hexpr. right; exact Hin. exact Hinfer0.
      * exact Hcheck.
Qed.
