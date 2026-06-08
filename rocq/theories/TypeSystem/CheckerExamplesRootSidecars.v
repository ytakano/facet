From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram CheckerExamplesBasic CheckerBorrow CheckerFull CheckerAlphaElabProgram CheckerRootSidecars.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.


Definition ex_ready_gap_let_fn : fn_def :=
  MkFnDef (("ready_gap_let"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELetInfer MImmutable (("x"%string), 0)
      (ELit (LInt 1))
      EUnit) 0 [].

Definition ex_ready_gap_let_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_let_fn].

Example check_program_env_alpha_accepts_ready_gap_let :
  check_program_env_alpha ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_duplicate_fn_name_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_let_fn; ex_ready_gap_let_fn].

Example check_program_env_alpha_rejects_duplicate_fn_name :
  check_program_env_alpha ex_duplicate_fn_name_env = false.
Proof. vm_compute. reflexivity. Qed.

Example check_program_env_alpha_validated_root_shadow_rejects_ready_gap_let :
  check_program_env_alpha_validated_root_shadow ex_ready_gap_let_env = false.
Proof. vm_compute. reflexivity. Qed.

Example check_env_root_shadow_provenance_summary_accepts_elab_ready_gap_let :
  match infer_program_env_alpha_elab ex_ready_gap_let_env with
  | infer_ok env =>
      check_env_root_shadow_provenance_summary env
  | infer_err _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example preservation_ready_expr_b_rejects_ready_gap_let :
  preservation_ready_expr_b (fn_body ex_ready_gap_let_fn) = false.
Proof. vm_compute. reflexivity. Qed.

Example provenance_ready_expr_b_accepts_ready_gap_let :
  provenance_ready_expr_b (fn_body ex_ready_gap_let_fn) = true.
Proof. vm_compute. reflexivity. Qed.

Example infer_env_elab_ready_gap_let_annotates_body :
  infer_env_elab ex_ready_gap_let_env ex_ready_gap_let_fn =
  infer_ok
    (MkTy UUnrestricted TUnits,
     [],
     fn_with_body ex_ready_gap_let_fn
       (ELet MImmutable (("x"%string), 0)
         (MkTy UUnrestricted TIntegers)
         (ELit (LInt 1))
         EUnit)).
Proof. vm_compute. reflexivity. Qed.

Example check_env_preservation_ready_rejects_alpha_elab_ready_gap_let :
  match infer_program_env_alpha_elab ex_ready_gap_let_env with
  | infer_ok env => check_env_preservation_ready env
  | infer_err _ => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

Example check_program_env_alpha_elab_accepts_ready_gap_let :
  check_program_env_alpha_elab ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Example check_program_env_alpha_validated_root_shadow_provenance_rejects_ready_gap_let :
  check_program_env_alpha_validated_root_shadow_provenance ex_ready_gap_let_env = false.
Proof. vm_compute. reflexivity. Qed.

(* Ordinary-checker accepted core shapes that the safety validator rejects. *)

Definition ex_ready_gap_let_annotated_fn : fn_def :=
  MkFnDef (("ready_gap_let_annotated"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("x"%string), 0)
      (MkTy UUnrestricted TIntegers)
      (ELit (LInt 1))
      EUnit) 0 [].

Definition ex_ready_gap_let_annotated_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_let_annotated_fn].

Example ready_gap_matrix_annotated_let_checker_accepts :
  check_program_env_alpha ex_ready_gap_let_annotated_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_annotated_let_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_let_annotated_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_annotated_let_provenance_summary_accepts :
  check_program_env_alpha_validated_root_shadow_provenance_summary
    ex_ready_gap_let_annotated_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_infer_let_checker_accepts :
  check_program_env_alpha ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_infer_let_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_let_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_infer_let_provenance_summary_accepts :
  check_program_env_alpha_validated_root_shadow_provenance_summary
    ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_deref_borrow_fn : fn_def :=
  MkFnDef (("ready_gap_deref_borrow"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TIntegers)
    (ELet MImmutable (("x"%string), 0)
      (MkTy UUnrestricted TIntegers)
      (ELit (LInt 1))
      (EDeref (EBorrow RShared (PVar (("x"%string), 0))))) 0 [].

Definition ex_ready_gap_deref_borrow_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_deref_borrow_fn].

Example ready_gap_matrix_deref_borrow_checker_accepts :
  check_program_env_alpha ex_ready_gap_deref_borrow_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_deref_borrow_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_deref_borrow_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_deref_borrow_provenance_summary_accepts :
  check_program_env_alpha_validated_root_shadow_provenance_summary
    ex_ready_gap_deref_borrow_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_call_callee_fn : fn_def :=
  MkFnDef (("ready_gap_call_callee"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    EUnit 0 [].

Definition ex_ready_gap_direct_call_fn : fn_def :=
  MkFnDef (("ready_gap_direct_call"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ECall (("ready_gap_call_callee"%string), 0) []) 0 [].

Definition ex_ready_gap_direct_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_ready_gap_call_callee_fn; ex_ready_gap_direct_call_fn].

Example ready_gap_matrix_direct_call_checker_accepts :
  check_program_env_alpha ex_ready_gap_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_direct_call_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_direct_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_direct_call_direct_call_summary_accepts :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_empty_capture_fn_value_accepts :
  infer_core_env ex_ready_gap_direct_call_env [] 0 []
    (EFn (("ready_gap_call_callee"%string), 0)) =
  infer_ok (fn_value_ty ex_ready_gap_call_callee_fn, []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_empty_capture_direct_call_accepts :
  infer_core_env ex_ready_gap_direct_call_env [] 0 []
    (ECall (("ready_gap_call_callee"%string), 0) []) =
  infer_ok (MkTy UUnrestricted TUnits, []).
Proof. vm_compute. reflexivity. Qed.

Definition ex_nonempty_capture_param : param :=
  MkParam MImmutable (("captured"%string), 0) (MkTy UUnrestricted TIntegers).

Definition ex_nonempty_capture_callee_fn : fn_def :=
  MkFnDef (("nonempty_capture_callee"%string), 0) 0 []
    [ex_nonempty_capture_param] []
    (MkTy UUnrestricted TUnits)
    EUnit 0 [].

Definition ex_nonempty_capture_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_nonempty_capture_callee_fn].

Example infer_core_env_nonempty_capture_fn_value_rejects :
  infer_core_env ex_nonempty_capture_env [] 0 []
    (EFn (("nonempty_capture_callee"%string), 0)) =
  infer_err ErrNotImplemented.
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_nonempty_capture_direct_call_rejects :
  infer_core_env ex_nonempty_capture_env [] 0 []
    (ECall (("nonempty_capture_callee"%string), 0) []) =
  infer_err ErrNotImplemented.
Proof. vm_compute. reflexivity. Qed.

Definition ex_shared_ref_capture_ty : Ty :=
  MkTy UUnrestricted (TRef (LVar 0) RShared (MkTy UUnrestricted TIntegers)).

Definition ex_shared_ref_capture_param : param :=
  MkParam MImmutable (("captured_ref"%string), 0) ex_shared_ref_capture_ty.

Definition ex_shared_ref_capture_callee_fn : fn_def :=
  MkFnDef (("shared_ref_capture_callee"%string), 0) 1 []
    [ex_shared_ref_capture_param] []
    (MkTy UUnrestricted TIntegers)
    (EDeref (EVar (("captured_ref"%string), 0))) 0 [].

Definition ex_shared_ref_capture_ctx : ctx :=
  [((("r"%string), 0), ex_shared_ref_capture_ty,
    MkBindingState false [], MImmutable)].

Definition ex_shared_ref_capture_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_shared_ref_capture_callee_fn].

Example infer_core_env_shared_ref_capture_accepts :
  infer_core_env ex_shared_ref_capture_env [] 1 ex_shared_ref_capture_ctx
    (EMakeClosure (("shared_ref_capture_callee"%string), 0)
      [(("r"%string), 0)]) =
  infer_ok
    (closure_value_ty_at (LVar 0) ex_shared_ref_capture_callee_fn
      [ex_shared_ref_capture_ty],
     ex_shared_ref_capture_ctx).
Proof. vm_compute. reflexivity. Qed.

Example exact_sctx_shared_ref_capture_still_rejects :
  check_make_closure_captures_exact_sctx ex_shared_ref_capture_env []
    (sctx_of_ctx ex_shared_ref_capture_ctx)
    [(("r"%string), 0)]
    [ex_shared_ref_capture_param] =
  infer_err (ErrNotAReference (TRef (LVar 0) RShared
    (MkTy UUnrestricted TIntegers))).
Proof. vm_compute. reflexivity. Qed.

Example exact_sctx_with_env_shared_ref_capture_accepts :
  check_make_closure_captures_exact_sctx_with_env ex_shared_ref_capture_env []
    (sctx_of_ctx ex_shared_ref_capture_ctx)
    [(("r"%string), 0)]
    [ex_shared_ref_capture_param] =
  infer_ok (LVar 0, [ex_shared_ref_capture_ty]).
Proof. vm_compute. reflexivity. Qed.

Definition ex_shared_ref_capture_ignore_callee_fn : fn_def :=
  MkFnDef (("shared_ref_capture_ignore_callee"%string), 0) 1 []
    [ex_shared_ref_capture_param] []
    (MkTy UUnrestricted TUnits)
    EUnit 0 [].

Definition ex_shared_ref_capture_direct_call_fn : fn_def :=
  MkFnDef (("shared_ref_capture_direct_call"%string), 0) 1 []
    [] [MkParam MImmutable (("r"%string), 0) ex_shared_ref_capture_ty]
    (MkTy UUnrestricted TUnits)
    (ECallExpr
      (EMakeClosure (("shared_ref_capture_ignore_callee"%string), 0)
        [(("r"%string), 0)])
      []) 0 [].

Definition ex_shared_ref_capture_direct_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_shared_ref_capture_ignore_callee_fn;
     ex_shared_ref_capture_direct_call_fn].

Example shared_ref_capture_direct_call_checker_accepts :
  check_program_env_alpha ex_shared_ref_capture_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example shared_ref_capture_direct_call_sidecar_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_shared_ref_capture_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_shared_ref_capture_local_let_call_fn : fn_def :=
  MkFnDef (("shared_ref_capture_local_let_call"%string), 0) 1 []
    [] [MkParam MImmutable (("r"%string), 0) ex_shared_ref_capture_ty]
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (closure_value_ty_at (LVar 0) ex_shared_ref_capture_ignore_callee_fn
        [ex_shared_ref_capture_ty])
      (EMakeClosure (("shared_ref_capture_ignore_callee"%string), 0)
        [(("r"%string), 0)])
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_shared_ref_capture_local_let_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_shared_ref_capture_ignore_callee_fn;
     ex_shared_ref_capture_local_let_call_fn].

Example shared_ref_capture_local_let_call_checker_accepts :
  check_program_env_alpha ex_shared_ref_capture_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example shared_ref_capture_local_let_call_sidecar_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_shared_ref_capture_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_call_expr : expr :=
  ELet MImmutable (("cap"%string), 0)
    (MkTy UUnrestricted TIntegers)
    (ELit (LInt 1))
    (ECallExpr
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      []).

Definition ex_ready_gap_captured_closure_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_call"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    ex_ready_gap_captured_closure_call_expr 0 [].

Definition ex_ready_gap_captured_closure_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_nonempty_capture_callee_fn; ex_ready_gap_captured_closure_call_fn].

Example ready_gap_matrix_captured_closure_call_checker_accepts :
  check_program_env_alpha ex_ready_gap_captured_closure_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_call_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_captured_closure_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_call_direct_call_summary_rejects :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_captured_closure_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_call_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_captured_closure_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_direct_param_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_direct_param_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    (ECallExpr
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      []) 0 [].

Definition ex_ready_gap_captured_closure_direct_param_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_direct_param_call_fn].

Example ready_gap_matrix_captured_closure_direct_param_call_checker_accepts :
  check_program_env_alpha
    ex_ready_gap_captured_closure_direct_param_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_call_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_call_captured_summary_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_direct_param_if_call_expr : expr :=
  EIf (ELit (LBool true))
    (ECallExpr
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      [])
    EUnit.

Definition ex_ready_gap_captured_closure_direct_param_if_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_direct_param_if_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    ex_ready_gap_captured_closure_direct_param_if_call_expr 0 [].

Definition ex_ready_gap_captured_closure_direct_param_if_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_direct_param_if_call_fn].

Example ready_gap_matrix_captured_closure_direct_param_if_call_checker_accepts :
  check_program_env_alpha
    ex_ready_gap_captured_closure_direct_param_if_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_if_call_helper_accepts :
  check_expr_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_if_call_env
    (fn_outlives ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (fn_lifetimes ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (initial_root_env_for_fn
      ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (fn_body_ctx ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (fn_body ex_ready_gap_captured_closure_direct_param_if_call_fn) = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_if_call_summary_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_if_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_local_let_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_local_let_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (closure_value_ty ex_nonempty_capture_callee_fn
        [MkTy UUnrestricted TIntegers])
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_captured_closure_local_let_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_local_let_call_fn].

Example ready_gap_matrix_captured_closure_local_let_call_checker_accepts :
  check_program_env_alpha
    ex_ready_gap_captured_closure_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_local_let_call_direct_summary_rejects :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_captured_closure_local_let_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_local_let_call_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_captured_closure_local_let_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_local_let_call_captured_summary_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_infer_local_let_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_infer_local_let_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    (ELetInfer MImmutable (("g"%string), 0)
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_captured_closure_infer_local_let_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_infer_local_let_call_fn].

Example ready_gap_matrix_captured_closure_infer_local_let_call_elab_checker_accepts :
  check_program_env_alpha_elab
    ex_ready_gap_captured_closure_infer_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_infer_local_let_call_original_summary_rejects :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_infer_local_let_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_infer_local_let_call_elab_summary_accepts :
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_infer_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_make_closure_preservation_ready_rejects :
  preservation_ready_expr_b
    (EMakeClosure (("nonempty_capture_callee"%string), 0)
      [(("cap"%string), 0)]) = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_make_closure_provenance_ready_rejects :
  provenance_ready_expr_b
    (EMakeClosure (("nonempty_capture_callee"%string), 0)
      [(("cap"%string), 0)]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_call_expr_fn : fn_def :=
  MkFnDef (("ready_gap_call_expr"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ECallExpr (EFn (("ready_gap_call_callee"%string), 0)) []) 0 [].

Definition ex_ready_gap_call_expr_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_ready_gap_call_callee_fn; ex_ready_gap_call_expr_fn].

Example ready_gap_matrix_call_expr_checker_accepts :
  check_program_env_alpha ex_ready_gap_call_expr_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_call_expr_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_call_expr_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_call_expr_direct_call_summary_accepts :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_call_expr_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_function_value_call_fn : fn_def :=
  MkFnDef (("ready_gap_function_value_call"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (fn_value_ty ex_ready_gap_call_callee_fn)
      (EFn (("ready_gap_call_callee"%string), 0))
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_function_value_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_ready_gap_call_callee_fn; ex_ready_gap_function_value_call_fn].

Example ready_gap_matrix_function_value_call_checker_accepts :
  check_program_env_alpha ex_ready_gap_function_value_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_function_value_call_direct_call_summary_rejects :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_function_value_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_function_value_call_non_capturing_summary_accepts :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_function_value_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_function_value_call_affine_annotated_fn : fn_def :=
  MkFnDef (("ready_gap_function_value_call_affine_annotated"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (MkTy UAffine (ty_core (fn_value_ty ex_ready_gap_call_callee_fn)))
      (EFn (("ready_gap_call_callee"%string), 0))
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_function_value_call_affine_annotated_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ ex_ready_gap_call_callee_fn
    ; ex_ready_gap_function_value_call_affine_annotated_fn
    ].

Example ready_gap_matrix_function_value_call_affine_annotation_checker_rejects :
  check_program_env_alpha
    ex_ready_gap_function_value_call_affine_annotated_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_function_value_call_affine_annotation_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_function_value_call_affine_annotated_env = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_struct_split : struct_def :=
  MkStructDef ("Split"%string) 0 0 []
    [ MkFieldDef ("x"%string) MImmutable (MkTy UAffine TIntegers)
    ; MkFieldDef ("y"%string) MImmutable (MkTy UUnrestricted TBooleans)
    ].

Definition ex_env_split : global_env :=
  MkGlobalEnv [ex_struct_split] [] [] [] [] [].

Definition ex_split_ty : Ty :=
  MkTy UAffine (TStruct ("Split"%string) [] []).

Definition ex_split_ctx : ctx :=
  [((("p"%string), 0), ex_split_ty, binding_state_of_bool false, MMutable)].

Definition ex_split_ctx_x_moved : ctx :=
  [((("p"%string), 0), ex_split_ty, MkBindingState false [["x"%string]], MMutable)].

Example auto_drop_live_paths_affine_struct_field :
  auto_drop_live_paths ex_env_split (("p"%string), 0) ex_split_ty ex_split_ctx =
  [["x"%string]].
Proof. vm_compute. reflexivity. Qed.

Example auto_drop_live_paths_affine_struct_moved_field_skipped :
  auto_drop_live_paths ex_env_split (("p"%string), 0) ex_split_ty ex_split_ctx_x_moved =
  [].
Proof. vm_compute. reflexivity. Qed.

Example auto_drop_paths_linear_not_generated :
  auto_drop_paths_for_ty ex_env_split (MkTy ULinear TIntegers) = [].
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_struct_instance_usage_after_args :
  infer_core_env
    (MkGlobalEnv
      [MkStructDef ("Box"%string) 0 1 []
        [MkFieldDef ("value"%string) MImmutable (MkTy UAffine (TParam 0))]]
      [] [] [] [] [])
    [] 0 []
    (EStruct ("Box"%string) [] [MkTy UAffine TIntegers]
      [(("value"%string), ELit (LInt 1))]) =
  infer_ok
    (MkTy UAffine (TStruct ("Box"%string) [] [MkTy UAffine TIntegers]), []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_moved_field_sibling_available :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EPlace (PField (PVar (("p"%string), 0)) ("y"%string)))) =
  infer_ok (MkTy UUnrestricted TBooleans, ex_split_ctx_x_moved).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_moved_field_blocks_parent_borrow :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EBorrow RShared (PVar (("p"%string), 0)))) =
  infer_err (ErrAlreadyConsumed (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_replace_rejects_moved_field :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (ELetInfer MImmutable (("old"%string), 0)
        (EReplace (PField (PVar (("p"%string), 0)) ("x"%string)) (ELit (LInt 1)))
        (EBorrow RShared (PVar (("p"%string), 0))))) =
  infer_err (ErrAlreadyConsumed (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_assign_rejects_moved_field :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EAssign (PField (PVar (("p"%string), 0)) ("x"%string)) (ELit (LInt 1)))) =
  infer_err (ErrAlreadyConsumed (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

Example borrow_check_env_sibling_fields_do_not_conflict :
  borrow_check_env ex_env_split [] ex_split_ctx
    (ELetInfer MImmutable (("b"%string), 0)
      (EBorrow RShared (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EBorrow RUnique (PField (PVar (("p"%string), 0)) ("y"%string)))) =
  infer_ok [PBMut (("p"%string), 0) [("y"%string)]].
Proof. vm_compute. reflexivity. Qed.

Example borrow_check_env_prefix_fields_conflict :
  borrow_check_env ex_env_split [] ex_split_ctx
    (ELetInfer MImmutable (("b"%string), 0)
      (EBorrow RShared (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EBorrow RUnique (PVar (("p"%string), 0)))) =
  infer_err (ErrBorrowConflict (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.


Definition ex_direct_self_rec_param : param :=
  MkParam MImmutable (("x"%string), 0) (MkTy UUnrestricted TIntegers).

Definition ex_direct_self_rec_loop_fn : fn_def :=
  MkFnDef (("direct_self_rec_loop"%string), 0) 0 [] []
    [ex_direct_self_rec_param]
    (MkTy UUnrestricted TIntegers)
    (ECall (("direct_self_rec_loop"%string), 0)
      [EVar (("x"%string), 0)]) 0 [].

Definition ex_direct_self_rec_main_fn : fn_def :=
  MkFnDef (("direct_self_rec_main"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TIntegers)
    (ECall (("direct_self_rec_loop"%string), 0)
      [ELit (LInt 1)]) 0 [].

Definition ex_direct_self_rec_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_direct_self_rec_loop_fn; ex_direct_self_rec_main_fn].

Example end2end_rejects_direct_self_recursion_current_gate :
  check_program_env_end2end ex_direct_self_rec_env = false.
Proof. vm_compute. reflexivity. Qed.

Example strict_exact_shadow_accepts_direct_self_recursion :
  check_program_env_end2end_strict_exact_closure ex_direct_self_rec_env = true.
Proof. vm_compute. reflexivity. Qed.
