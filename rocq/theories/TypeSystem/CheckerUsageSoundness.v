From Facet.TypeSystem Require Import Types Syntax TypingRules TypeChecker CheckerSoundness.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Linear scope-exit usage                                               *)
(* ------------------------------------------------------------------ *)

Lemma ctx_is_ok_linear_used : forall x T Γ,
  ty_usage T = ULinear ->
  ctx_is_ok x T Γ ->
  exists Tx, ctx_lookup x Γ = Some (Tx, true).
Proof.
  intros x T Γ Hlin Hok.
  unfold ctx_is_ok in Hok.
  rewrite Hlin in Hok.
  destruct (ctx_lookup x Γ) as [[Tx b] |] eqn:Hlookup.
  - destruct b.
    + exists Tx. reflexivity.
    + contradiction.
  - contradiction.
Qed.

Lemma typed_linear_let_binding_used : forall fenv n Γ Γout m x T e1 e2 T2,
  typed fenv n Γ (ELet m x T e1 e2) T2 Γout ->
  ty_usage T = ULinear ->
  exists Γ1 Γ2 T1 Tx,
    typed fenv n Γ e1 T1 Γ1 /\
    typed fenv n (ctx_add x T m Γ1) e2 T2 Γ2 /\
  ctx_lookup x Γ2 = Some (Tx, true).
Proof.
  intros fenv n Γ Γout m x T e1 e2 T2 Htyped Hlin.
  inversion Htyped; subst.
  match goal with
  | H : ctx_is_ok x T Γ2 |- _ =>
      pose proof (ctx_is_ok_linear_used x T Γ2 Hlin H) as [Tx Hlookup]
  end.
  exists Γ1, Γ2, T1, Tx.
  repeat split; assumption.
Qed.

Lemma params_ok_linear_param_used : forall ps Γ p,
  In p ps ->
  params_ok ps Γ ->
  ty_usage (param_ty p) = ULinear ->
  exists Tx, ctx_lookup (param_name p) Γ = Some (Tx, true).
Proof.
  intros ps Γ p Hin Hok Hlin.
  induction ps as [| p0 ps IH].
  - contradiction.
  - simpl in Hin, Hok.
    destruct Hok as [Hok0 Hoks].
    destruct Hin as [Heq | Hin].
    + subst p0.
      exact (ctx_is_ok_linear_used (param_name p) (param_ty p) Γ Hlin Hok0).
    + exact (IH Hin Hoks).
Qed.

Lemma typed_linear_param_used : forall fenv f p,
  typed_fn_def fenv f ->
  In p (fn_params f) ->
  ty_usage (param_ty p) = ULinear ->
  exists T_body Γ' Tx,
    typed fenv (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f) T_body Γ' /\
    ctx_lookup (param_name p) Γ' = Some (Tx, true).
Proof.
  intros fenv f p Htyped_fn Hin Hlin.
  destruct Htyped_fn as [T_body [Γ' [Hbody [_ Hparams]]]].
  pose proof (params_ok_linear_param_used
    (fn_params f) Γ' p Hin Hparams Hlin) as [Tx Hlookup].
  exists T_body, Γ', Tx.
  split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Functions checked by infer satisfy linear usage obligations           *)
(* ------------------------------------------------------------------ *)

Definition infer_fn_def_ok (fenv : list fn_def) (f : fn_def) : Prop :=
  exists Γ',
    infer_body fenv (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f) =
      infer_ok (fn_ret f, Γ') /\
    params_ok (fn_params f) Γ'.

Lemma infer_fn_def_ok_sound : forall fenv f,
  infer_fn_def_ok fenv f ->
  typed_fn_def fenv f.
Proof.
  intros fenv f [Γ' [Hinfer Hparams]].
  exists (fn_ret f), Γ'.
  repeat split.
  - apply infer_body_sound. exact Hinfer.
  - destruct (fn_ret f) as [u c]. apply TC_Core.
    + apply US_refl.
    + reflexivity.
  - exact Hparams.
Qed.

Fixpoint expr_linear_lets_used (fenv : list fn_def) (e : expr) {struct e}
    : Prop :=
  match e with
  | EUnit => True
  | ELit _ => True
  | EVar _ => True
  | ELet m x T e1 e2 =>
      (ty_usage T = ULinear ->
       forall n Γ Γout T2,
         typed fenv n Γ (ELet m x T e1 e2) T2 Γout ->
         exists Γ1 Γ2 T1 Tx,
           typed fenv n Γ e1 T1 Γ1 /\
           typed fenv n (ctx_add x T m Γ1) e2 T2 Γ2 /\
           ctx_lookup x Γ2 = Some (Tx, true)) /\
      expr_linear_lets_used fenv e1 /\
      expr_linear_lets_used fenv e2
  | ELetInfer _ _ e1 e2 =>
      expr_linear_lets_used fenv e1 /\
      expr_linear_lets_used fenv e2
  | ECall _ _ => True
  | EReplace _ e_new => expr_linear_lets_used fenv e_new
  | EAssign _ e_new => expr_linear_lets_used fenv e_new
  | EBorrow _ _ => True
  | EDeref e1 => expr_linear_lets_used fenv e1
  | EDrop e1 => expr_linear_lets_used fenv e1
  | EIf e1 e2 e3 =>
      expr_linear_lets_used fenv e1 /\
      expr_linear_lets_used fenv e2 /\
      expr_linear_lets_used fenv e3
  end.

Fixpoint expr_linear_lets_used_sound (fenv : list fn_def) (e : expr)
    {struct e} : expr_linear_lets_used fenv e.
Proof.
  destruct e; simpl; try exact I.
  - repeat split.
    + intros Hlin n Γ Γout T2 Htyped.
      exact (typed_linear_let_binding_used
        fenv n Γ Γout m i t e1 e2 T2 Htyped Hlin).
    + apply expr_linear_lets_used_sound.
    + apply expr_linear_lets_used_sound.
  - split; apply expr_linear_lets_used_sound.
  - apply expr_linear_lets_used_sound.
  - apply expr_linear_lets_used_sound.
  - apply expr_linear_lets_used_sound.  (* EDeref *)
  - apply expr_linear_lets_used_sound.
  - repeat split; apply expr_linear_lets_used_sound.
Qed.

Theorem infer_checked_fn_linear_lets_used : forall fenv f,
  infer_fn_def_ok fenv f ->
  expr_linear_lets_used fenv (fn_body f).
Proof.
  intros fenv f _.
  apply expr_linear_lets_used_sound.
Qed.

Theorem infer_checked_fn_linear_params_used : forall fenv f p,
  infer_fn_def_ok fenv f ->
  In p (fn_params f) ->
  ty_usage (param_ty p) = ULinear ->
  exists T_body Γ' Tx,
    typed fenv (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f) T_body Γ' /\
    ctx_lookup (param_name p) Γ' = Some (Tx, true).
Proof.
  intros fenv f p Hinfer_fn Hin Hlin.
  apply typed_linear_param_used.
  - apply infer_fn_def_ok_sound. exact Hinfer_fn.
  - exact Hin.
  - exact Hlin.
Qed.

(* If infer accepts a function, every linear let-binding tracked by
   expr_linear_lets_used is used before leaving its scope, and every linear
   function parameter is marked used in the final body context. *)
Theorem infer_checked_fn_linear_usage : forall fenv f,
  infer_fn_def_ok fenv f ->
  expr_linear_lets_used fenv (fn_body f) /\
  (forall p,
      In p (fn_params f) ->
      ty_usage (param_ty p) = ULinear ->
      exists T_body Γ' Tx,
        typed fenv (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f) T_body Γ' /\
        ctx_lookup (param_name p) Γ' = Some (Tx, true)).
Proof.
  intros fenv f Hinfer_fn.
  split.
  - apply infer_checked_fn_linear_lets_used. exact Hinfer_fn.
  - intros p Hin Hlin.
    exact (infer_checked_fn_linear_params_used fenv f p Hinfer_fn Hin Hlin).
Qed.

(* Affine values are consumed through the same context flag as linear values.
   Once infer succeeds with an affine binding marked consumed in the output
   context, checking the same variable again fails because EVar requires an
   unconsumed affine/linear binding. *)
Theorem infer_affine_value_at_most_once : forall fenv n Γ e T Γ' x Tx,
  infer_body fenv n Γ e = infer_ok (T, Γ') ->
  ctx_lookup x Γ = Some (Tx, false) ->
  ty_usage Tx = UAffine ->
  ctx_lookup x Γ' = Some (Tx, true) ->
  infer_body fenv n Γ' (EVar x) = infer_err (ErrAlreadyConsumed x).
Proof.
  intros fenv n Γ e T Γ' x Tx _ _ Haff Hused.
  unfold infer_body, alpha_rename_for_infer.
  destruct (alpha_rename_syntax_go (free_vars_expr (EVar x) ++ ctx_names Γ') fenv)
    as [fenv' used].
  simpl.
  rewrite ctx_lookup_b_eq.
  rewrite Hused.
  rewrite Haff.
  simpl.
  reflexivity.
Qed.
