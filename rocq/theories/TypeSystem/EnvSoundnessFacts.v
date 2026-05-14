From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program TypingRules TypeChecker CheckerSoundness.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Small helper facts for env/stateful checker soundness                 *)
(* ------------------------------------------------------------------ *)

Lemma sctx_consume_path_success :
  forall Σ x p Σ',
    sctx_consume_path Σ x p = infer_ok Σ' ->
    exists T st,
      sctx_lookup x Σ = Some (T, st) /\
      binding_available_b st p = true /\
      sctx_update_state x (state_consume_path p) Σ = Some Σ'.
Proof.
  unfold sctx_consume_path, sctx_path_available.
  intros Σ x p Σ' H.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b st p) eqn:Havailable; try discriminate.
  destruct (sctx_update_state x (state_consume_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion H; subst.
  exists T, st. repeat split; assumption.
Qed.

Lemma sctx_restore_path_success :
  forall Σ x p Σ',
    sctx_restore_path Σ x p = infer_ok Σ' ->
    sctx_update_state x (state_restore_path p) Σ = Some Σ'.
Proof.
  intros Σ x p Σ' H.
  unfold sctx_restore_path in H.
  destruct (sctx_update_state x (state_restore_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion H; subst. reflexivity.
Qed.

Lemma sctx_check_ok_linear_success :
  forall env Σ x T,
    sctx_check_ok env x T Σ = true ->
    ty_usage T = ULinear ->
    exists Tx st,
      sctx_lookup x Σ = Some (Tx, st) /\
      linear_scope_ok_b env T st = true.
Proof.
  intros env Σ x T Hcheck Hlin.
  unfold sctx_check_ok in Hcheck.
  rewrite Hlin in Hcheck.
  destruct (sctx_lookup x Σ) as [[Tx st] |] eqn:Hlookup; try discriminate.
  exists Tx, st. split; [reflexivity | exact Hcheck].
Qed.

Lemma lookup_struct_in_success :
  forall name structs s,
    lookup_struct_in name structs = Some s ->
    In s structs /\ struct_name s = name.
Proof.
  intros name structs.
  induction structs as [|h rest IH]; intros s Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name (struct_name h)) eqn:Hname.
    + inversion Hlookup; subst.
      apply String.eqb_eq in Hname.
      split; [left; reflexivity | symmetry; exact Hname].
    + destruct (IH s Hlookup) as [Hin Hstruct].
      split; [right; exact Hin | exact Hstruct].
Qed.

Lemma lookup_struct_success :
  forall env name s,
    lookup_struct name env = Some s ->
    In s (env_structs env) /\ struct_name s = name.
Proof.
  unfold lookup_struct. intros env name s H.
  apply lookup_struct_in_success. exact H.
Qed.

Lemma lookup_field_success :
  forall name fields f,
    lookup_field name fields = Some f ->
    In f fields /\ field_name f = name.
Proof.
  intros name fields.
  induction fields as [|h rest IH]; intros f Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name (field_name h)) eqn:Hname.
    + inversion Hlookup; subst.
      apply String.eqb_eq in Hname.
      split; [left; reflexivity | symmetry; exact Hname].
    + destruct (IH f Hlookup) as [Hin Hfield].
      split; [right; exact Hin | exact Hfield].
Qed.

Lemma lookup_field_b_success :
  forall name fields e,
    lookup_field_b name fields = Some e ->
    In (name, e) fields.
Proof.
  unfold lookup_field_b.
  intros name fields.
  induction fields as [|[fname expr] rest IH]; intros e Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name fname) eqn:Hname.
    + inversion Hlookup; subst.
      apply String.eqb_eq in Hname. subst fname.
      left. reflexivity.
    + right. apply IH. exact Hlookup.
Qed.

Lemma first_unknown_field_none_sound :
  forall fields defs,
    first_unknown_field fields defs = None ->
    Forall (fun '(name, _) => exists f, lookup_field name defs = Some f) fields.
Proof.
  induction fields as [|[name e] rest IH]; simpl; intros defs H.
  - constructor.
  - destruct (lookup_field name defs) as [f |] eqn:Hlookup; try discriminate.
    constructor.
    + exists f. exact Hlookup.
    + apply IH. exact H.
Qed.

Lemma first_missing_field_none_sound :
  forall defs fields,
    first_missing_field defs fields = None ->
    Forall (fun f => exists e, lookup_field_b (field_name f) fields = Some e) defs.
Proof.
  induction defs as [|f rest IH]; simpl; intros fields H.
  - constructor.
  - destruct (has_field_b (field_name f) fields) eqn:Hhas; try discriminate.
    constructor.
    + unfold has_field_b in Hhas.
      destruct (lookup_field_b (field_name f) fields) as [e |] eqn:Hlookup;
        try discriminate.
      exists e. reflexivity.
    + apply IH. exact H.
Qed.

Lemma check_arg_tys_sound :
  forall Ω arg_tys param_tys,
    check_arg_tys Ω arg_tys param_tys = None ->
    Forall2 (fun actual expected => ty_compatible Ω actual expected) arg_tys param_tys.
Proof.
  intros Ω arg_tys param_tys H.
  rewrite check_arg_tys_params_of_tys in H.
  revert param_tys H.
  induction arg_tys as [|arg rest IH]; intros param_tys H; destruct param_tys as [|param rest_params];
    simpl in H; try discriminate.
  - constructor.
  - destruct (ty_compatible_b Ω arg param) eqn:Hcompat; try discriminate.
    constructor.
    + apply ty_compatible_b_sound. exact Hcompat.
    + apply IH. exact H.
Qed.

Lemma check_args_sound :
  forall Ω arg_tys params,
    check_args Ω arg_tys params = None ->
    Forall2 (fun actual p => ty_compatible Ω actual (param_ty p)) arg_tys params.
Proof.
  induction arg_tys as [|arg rest IH]; intros params H; destruct params as [|param rest_params];
    simpl in H; try discriminate.
  - constructor.
  - destruct (ty_compatible_b Ω arg (param_ty param)) eqn:Hcompat; try discriminate.
    constructor.
    + apply ty_compatible_b_sound. exact Hcompat.
    + apply IH. exact H.
Qed.

Lemma env_outlives_constraints_hold_b_sound :
  forall Ω constraints,
    outlives_constraints_hold_b Ω constraints = true ->
    Forall (fun '(a, b) => outlives Ω a b) constraints.
Proof.
  apply outlives_constraints_hold_b_sound.
Qed.
