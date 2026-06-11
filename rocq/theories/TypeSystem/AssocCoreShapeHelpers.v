From Facet.TypeSystem Require Import
  Lifetime Types Program CheckerBase CompatBoolSoundness.

Local Opaque normalize_assoc_ty.

(* Assoc-aware helper facts for normalized core-shape checks. *)

Definition ty_core_assoc_matches_b
    (env : global_env) (T : Ty) (expected_core : TypeCore Ty) : bool :=
  ty_core_eqb (ty_core (normalize_assoc_ty env T)) expected_core.

Lemma ty_core_assoc_matches_b_true :
  forall env T expected_core,
    ty_core_assoc_matches_b env T expected_core = true ->
    ty_core (normalize_assoc_ty env T) = expected_core.
Proof.
  intros env T expected_core Hcore.
  unfold ty_core_assoc_matches_b in Hcore.
  apply CompatBoolSoundness.ty_core_eqb_true. exact Hcore.
Qed.

Definition check_ty_core_assoc
    (env : global_env) (T : Ty) (expected_core : TypeCore Ty)
    : option infer_error :=
  let T_norm := normalize_assoc_ty env T in
  if ty_core_assoc_matches_b env T expected_core
  then None
  else Some (ErrTypeMismatch (ty_core T_norm) expected_core).

Definition check_bool_condition_assoc
    (env : global_env) (T_cond : Ty) : option infer_error :=
  check_ty_core_assoc env T_cond TBooleans.

Lemma check_ty_core_assoc_ok :
  forall env T expected_core,
    check_ty_core_assoc env T expected_core = None ->
    ty_core (normalize_assoc_ty env T) = expected_core.
Proof.
  intros env T expected_core Hcheck.
  unfold check_ty_core_assoc in Hcheck.
  destruct (ty_core_assoc_matches_b env T expected_core) eqn:Hcore.
  - apply ty_core_assoc_matches_b_true. exact Hcore.
  - discriminate.
Qed.

Lemma check_bool_condition_assoc_ok :
  forall env T_cond,
    check_bool_condition_assoc env T_cond = None ->
    ty_core (normalize_assoc_ty env T_cond) = TBooleans.
Proof.
  intros env T_cond Hcheck.
  unfold check_bool_condition_assoc in Hcheck.
  apply check_ty_core_assoc_ok. exact Hcheck.
Qed.
