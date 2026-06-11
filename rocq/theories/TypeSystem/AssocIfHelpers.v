From Facet.TypeSystem Require Import
  Lifetime Types Program TypingRules CheckerBase CompatBoolSoundness.
From Stdlib Require Import Bool.

Local Opaque normalize_assoc_ty.

(* Assoc-aware helper facts for if-branch result core equality. *)

Definition ty_core_assoc_eq_b
    (env : global_env) (T_left T_right : Ty) : bool :=
  ty_core_eqb
    (ty_core (normalize_assoc_ty env T_left))
    (ty_core (normalize_assoc_ty env T_right)).

Lemma ty_core_assoc_eq_b_true :
  forall env T_left T_right,
    ty_core_assoc_eq_b env T_left T_right = true ->
    ty_core (normalize_assoc_ty env T_left) =
    ty_core (normalize_assoc_ty env T_right).
Proof.
  intros env T_left T_right Hcore.
  unfold ty_core_assoc_eq_b in Hcore.
  apply CompatBoolSoundness.ty_core_eqb_true. exact Hcore.
Qed.

Definition infer_if_result_ty_assoc
    (env : global_env) (T_then T_else : Ty) : infer_result Ty :=
  let T_then_norm := normalize_assoc_ty env T_then in
  let T_else_norm := normalize_assoc_ty env T_else in
  if ty_core_assoc_eq_b env T_then T_else
  then infer_ok
    (MkTy
      (usage_max (ty_usage T_then_norm) (ty_usage T_else_norm))
      (ty_core T_then_norm))
  else infer_err
    (ErrTypeMismatch (ty_core T_then_norm) (ty_core T_else_norm)).

Lemma infer_if_result_ty_assoc_ok :
  forall env T_then T_else T_result,
    infer_if_result_ty_assoc env T_then T_else = infer_ok T_result ->
    ty_core (normalize_assoc_ty env T_then) =
    ty_core (normalize_assoc_ty env T_else) /\
    T_result =
      MkTy
        (usage_max
          (ty_usage (normalize_assoc_ty env T_then))
          (ty_usage (normalize_assoc_ty env T_else)))
        (ty_core (normalize_assoc_ty env T_then)).
Proof.
  intros env T_then T_else T_result Hresult.
  unfold infer_if_result_ty_assoc in Hresult.
  destruct (ty_core_assoc_eq_b env T_then T_else) eqn:Hcore.
  - inversion Hresult; subst. split.
    + apply ty_core_assoc_eq_b_true. exact Hcore.
    + reflexivity.
  - discriminate.
Qed.
