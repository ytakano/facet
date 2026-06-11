From Facet.TypeSystem Require Import
  Lifetime Types Program TypingRules CheckerBase AssocIfHelpers.
From Stdlib Require Import Bool List.
Import ListNotations.

Local Opaque normalize_assoc_ty.

(* Assoc-aware helper facts for match-branch result core equality. *)

Fixpoint ty_cores_assoc_eq_all_b
    (env : global_env) (head : Ty) (tail : list Ty) : bool :=
  match tail with
  | [] => true
  | T :: rest =>
      ty_core_assoc_eq_b env T head
      && ty_cores_assoc_eq_all_b env head rest
  end.

Definition infer_match_result_ty_assoc
    (env : global_env) (T_head : Ty) (Ts_tail : list Ty)
    : infer_result Ty :=
  let T_head_norm := normalize_assoc_ty env T_head in
  let Ts_tail_norm := map (normalize_assoc_ty env) Ts_tail in
  if ty_cores_assoc_eq_all_b env T_head Ts_tail
  then infer_ok
    (MkTy
      (usage_max_tys_nonempty T_head_norm Ts_tail_norm)
      (ty_core T_head_norm))
  else infer_err ErrContextCheckFailed.

Lemma infer_match_result_ty_assoc_ok :
  forall env T_head Ts_tail T_result,
    infer_match_result_ty_assoc env T_head Ts_tail = infer_ok T_result ->
    ty_cores_assoc_eq_all_b env T_head Ts_tail = true /\
    T_result =
      MkTy
        (usage_max_tys_nonempty
          (normalize_assoc_ty env T_head)
          (map (normalize_assoc_ty env) Ts_tail))
        (ty_core (normalize_assoc_ty env T_head)).
Proof.
  intros env T_head Ts_tail T_result Hresult.
  unfold infer_match_result_ty_assoc in Hresult.
  destruct (ty_cores_assoc_eq_all_b env T_head Ts_tail) eqn:Hcores.
  - inversion Hresult; subst. split; reflexivity.
  - discriminate.
Qed.
