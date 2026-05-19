From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  TypingRules TypeChecker EnvStructuralRules EnvTypingSoundness EnvBorrowSoundness.
From Stdlib Require Import List Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Total structural typing soundness for the env/stateful checker        *)
(* ------------------------------------------------------------------ *)

Lemma struct_expr_true : forall e,
  struct_expr e = true.
Proof.
  fix IH 1.
  intro e.
  destruct e; simpl; try reflexivity.
  - rewrite IH, IH. reflexivity.
  - rewrite IH, IH. reflexivity.
  - induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - rewrite IH.
    induction l as [| a rest IHargs]; simpl.
    + reflexivity.
    + rewrite IH, IHargs. reflexivity.
  - induction l1 as [| [fname field] rest IHfields]; simpl.
    + reflexivity.
    + rewrite IH, IHfields. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, IH, IH. reflexivity.
Qed.

Theorem infer_core_env_state_fuel_structural_sound :
  forall fuel env Ω n Σ e T Σ',
    infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  intros fuel env Ω n Σ e T Σ' Hinfer.
  eapply infer_core_env_state_fuel_struct_structural_sound.
  - apply struct_expr_true.
  - exact Hinfer.
Qed.

Theorem infer_core_env_structural_sound :
  forall env Ω n Γ e T Γ',
    infer_core_env env Ω n Γ e = infer_ok (T, Γ') ->
    typed_env_structural env Ω n (sctx_of_ctx Γ) e T (sctx_of_ctx Γ').
Proof.
  unfold infer_core_env, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n Γ e T Γ' Hinfer.
  destruct (infer_core_env_state_fuel 10000 env Ω n Γ e) as [[T0 Σ] | err]
    eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_structural_sound. exact Hcore.
Qed.

Theorem infer_env_structural_sound : forall env f T Γ',
  infer_env env f = infer_ok (T, Γ') ->
  typed_fn_env_structural env f.
Proof.
  unfold infer_env, typed_fn_env_structural.
  intros env f T Γ' Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env env (fn_outlives f) (fn_lifetimes f)
              (fn_body_ctx f) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompatible; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_out) eqn:Hparams; try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ'.
  repeat split.
  - eapply infer_core_env_structural_sound. exact Hcore.
  - exact Hcompatible.
  - exact Hparams.
Qed.

Theorem infer_full_env_structural_sound_unvalidated : forall env f T Γ',
  infer_full_env env f = infer_ok (T, Γ') ->
  checked_fn_env_structural env f.
Proof.
  unfold infer_full_env, checked_fn_env_structural.
  intros env f T Γ' Hfull.
  destruct (infer_env env f) as [[T0 Γ0] | err] eqn:Hinfer; try discriminate.
  destruct (borrow_check_env env [] (fn_body_ctx f) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  split.
  - eapply infer_env_structural_sound. exact Hinfer.
  - split.
    + exists PBS'. eapply borrow_check_env_structural_sound. exact Hborrow.
    + eapply infer_env_params_nodup. exact Hinfer.
Qed.

Theorem infer_full_env_alpha_structural_sound : forall env f T Γ',
  infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
  checked_fn_env_structural (alpha_normalize_global_env env) f.
Proof.
  intros env f T Γ' Hfull.
  eapply infer_full_env_structural_sound_unvalidated.
  exact Hfull.
Qed.

Theorem check_program_env_alpha_checked_structural : forall env,
  check_program_env_alpha env = true ->
  env_fns_checked_structural (alpha_normalize_global_env env).
Proof.
  unfold check_program_env_alpha, check_program_env,
    env_fns_checked_structural.
  intros env Hcheck f Hin.
  apply forallb_forall with (x := f) in Hcheck; [| exact Hin].
  destruct (infer_full_env (alpha_normalize_global_env env) f)
    as [[T Γ'] | err] eqn:Hfull.
  - exact (infer_full_env_alpha_structural_sound env f T Γ' Hfull).
  - simpl in Hcheck. discriminate.
Qed.
