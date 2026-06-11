From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules CheckerBase
  AssocCompatibility AlphaTyping.

(* Prop-level function-body typing that stores only the lightweight checked
   associated-projection compatibility witness for the return type.
*)
Inductive typed_fn_def_assoc_checked
    (env : global_env) (fenv : list fn_def) (f : fn_def) : Prop :=
  | TFnDefAssocChecked : forall T_body Gamma_out,
      typed fenv (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
        (fn_body f) T_body Gamma_out ->
      ty_compatible_assoc_checked env (fn_outlives f) T_body (fn_ret f) ->
      params_ok (fn_params f) Gamma_out ->
      typed_fn_def_assoc_checked env fenv f.

Lemma typed_fn_def_assoc_checked_inv :
  forall env fenv f,
    typed_fn_def_assoc_checked env fenv f ->
    exists T_body Gamma_out,
      typed fenv (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
        (fn_body f) T_body Gamma_out /\
      ty_compatible_assoc_checked env (fn_outlives f) T_body (fn_ret f) /\
      params_ok (fn_params f) Gamma_out.
Proof.
  intros env fenv f Hfn.
  inversion Hfn; subst.
  exists T_body, Gamma_out. repeat split; assumption.
Qed.

Lemma typed_fn_def_assoc_checked_body_same_bindings :
  forall env fenv f,
    typed_fn_def_assoc_checked env fenv f ->
    exists T_body Gamma_out,
      typed fenv (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
        (fn_body f) T_body Gamma_out /\
      ctx_same_bindings (fn_body_ctx f) Gamma_out.
Proof.
  intros env fenv f Hfn.
  destruct (typed_fn_def_assoc_checked_inv _ _ _ Hfn)
    as [T_body [Gamma_out [Htyped [_ _]]]].
  exists T_body, Gamma_out. split; [exact Htyped|].
  destruct typed_same_bindings as [Htyped_same _].
  eapply Htyped_same. exact Htyped.
Qed.

Lemma typed_fn_def_assoc_checked_intro :
  forall env fenv f T_body Gamma_out,
    typed fenv (fn_outlives f) (fn_lifetimes f) (fn_body_ctx f)
      (fn_body f) T_body Gamma_out ->
    ty_compatible_assoc_checked env (fn_outlives f) T_body (fn_ret f) ->
    params_ok (fn_params f) Gamma_out ->
    typed_fn_def_assoc_checked env fenv f.
Proof.
  intros env fenv f T_body Gamma_out Htyped Hcompat Hparams.
  econstructor; eauto.
Qed.
