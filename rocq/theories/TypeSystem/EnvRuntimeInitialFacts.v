From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeValidatorFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition initial_store_for_fn (env : global_env) (f : fn_def) (s : store) : Prop :=
  store_typed env s (sctx_of_ctx (fn_body_ctx f)) /\
  store_function_closure_targets_summary env s.

Lemma initial_store_for_fn_store_typed :
  forall env f s,
    initial_store_for_fn env f s ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)).
Proof.
  intros env f s Hinitial. exact (proj1 Hinitial).
Qed.

Lemma initial_store_for_fn_closure_targets_summary :
  forall env f s,
    initial_store_for_fn env f s ->
    store_function_closure_targets_summary env s.
Proof.
  intros env f s Hinitial. exact (proj2 Hinitial).
Qed.

Lemma non_function_value_ty_b_subst_type_params_ty :
  forall type_args T,
    Forall (fun Targ => non_function_value_ty_b Targ = true) type_args ->
    non_function_value_ty_b T = true ->
    non_function_value_ty_b (subst_type_params_ty type_args T) = true.
Proof.
  intros type_args T Hargs. revert T.
  fix IH 1. intros [u c] Hnon.
  destruct c; simpl in *; try reflexivity; try discriminate.
  - destruct (nth_error type_args n) as [Targ |] eqn:Hnth; simpl; auto.
    apply nth_error_In in Hnth.
    rewrite Forall_forall in Hargs.
    specialize (Hargs Targ Hnth).
    destruct Targ as [uarg carg]. destruct carg; simpl in *; try reflexivity;
      try discriminate; exact Hargs.
  - apply IH. exact Hnon.
  - exact Hnon.
Qed.

Lemma non_function_value_ty_b_apply_type_param :
  forall type_args p,
    Forall (fun Targ => non_function_value_ty_b Targ = true) type_args ->
    non_function_value_ty_b (param_ty p) = true ->
    non_function_value_ty_b (param_ty (apply_type_param type_args p)) = true.
Proof.
  intros type_args [m x T] Hargs Hnon. simpl in *.
  eapply non_function_value_ty_b_subst_type_params_ty; eassumption.
Qed.

Lemma Forall_non_function_value_ty_b_apply_type_params :
  forall type_args ps,
    Forall (fun Targ => non_function_value_ty_b Targ = true) type_args ->
    Forall (fun p => non_function_value_ty_b (param_ty p) = true) ps ->
    Forall (fun p => non_function_value_ty_b (param_ty p) = true)
      (apply_type_params type_args ps).
Proof.
  intros type_args ps Hargs Hps. induction Hps as [| p ps Hp Hps IH];
    simpl; constructor.
  - eapply non_function_value_ty_b_apply_type_param; eassumption.
  - exact IH.
Qed.

Lemma root_env_excludes_remove_params :
  forall x ps R,
    root_env_no_shadow R ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_remove_params ps R).
Proof.
  intros x ps.
  induction ps as [| p ps IH]; intros R Hrn Hexcl; simpl.
  - exact Hexcl.
  - apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + apply root_env_excludes_remove_no_shadow; assumption.
Qed.

Lemma root_subst_of_params_apply_type_params :
  forall type_args ps arg_roots,
    root_subst_of_params (apply_type_params type_args ps) arg_roots =
    root_subst_of_params ps arg_roots.
Proof.
  intros type_args ps.
  induction ps as [| p ps IH]; intros arg_roots;
    destruct arg_roots as [| roots arg_roots]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma roots_exclude_params_apply_type_params_iff :
  forall type_args ps roots,
    roots_exclude_params (apply_type_params type_args ps) roots <->
    roots_exclude_params ps roots.
Proof.
  intros type_args ps roots.
  unfold roots_exclude_params.
  rewrite params_ctx_apply_type_params.
  rewrite ctx_names_subst_type_params_ctx.
  split; intro H; exact H.
Qed.

Lemma roots_exclude_params_apply_type_params :
  forall type_args ps roots,
    roots_exclude_params ps roots ->
    roots_exclude_params (apply_type_params type_args ps) roots.
Proof.
  intros type_args ps roots Hexclude.
  apply roots_exclude_params_apply_type_params_iff.
  exact Hexclude.
Qed.

Lemma roots_exclude_params_unapply_type_params :
  forall type_args ps roots,
    roots_exclude_params (apply_type_params type_args ps) roots ->
    roots_exclude_params ps roots.
Proof.
  intros type_args ps roots Hexclude.
  apply (proj1 (roots_exclude_params_apply_type_params_iff
    type_args ps roots)).
  exact Hexclude.
Qed.

Lemma root_env_excludes_params_apply_type_params_iff :
  forall type_args ps R,
    root_env_excludes_params (apply_type_params type_args ps) R <->
    root_env_excludes_params ps R.
Proof.
  intros type_args ps R.
  unfold root_env_excludes_params.
  rewrite params_ctx_apply_type_params.
  rewrite ctx_names_subst_type_params_ctx.
  split; intro H; exact H.
Qed.

Lemma root_env_excludes_params_apply_type_params :
  forall type_args ps R,
    root_env_excludes_params ps R ->
    root_env_excludes_params (apply_type_params type_args ps) R.
Proof.
  intros type_args ps R Hexclude.
  apply root_env_excludes_params_apply_type_params_iff.
  exact Hexclude.
Qed.

Lemma root_env_excludes_params_unapply_type_params :
  forall type_args ps R,
    root_env_excludes_params (apply_type_params type_args ps) R ->
    root_env_excludes_params ps R.
Proof.
  intros type_args ps R Hexclude.
  apply (proj1 (root_env_excludes_params_apply_type_params_iff
    type_args ps R)).
  exact Hexclude.
Qed.

