From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Definition ex_struct_pair : struct_def :=
  MkStructDef ("Pair"%string) 0 0 []
    [ MkFieldDef ("x"%string) MImmutable (MkTy UUnrestricted TIntegers)
    ; MkFieldDef ("y"%string) MImmutable (MkTy UUnrestricted TBooleans)
    ].

Definition ex_env_struct_pair : global_env :=
  MkGlobalEnv [ex_struct_pair] [] [] [] [] [].

Example infer_core_env_roots_var_summary_ok :
  infer_core_env_roots ex_env_struct_pair [] 0
    [((("x"%string), 0), [RStore (("x"%string), 0)])]
    [((("x"%string), 0), MkTy UUnrestricted TIntegers,
      binding_state_of_bool false, MImmutable)]
    (EVar (("x"%string), 0)) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [((("x"%string), 0), MkTy UUnrestricted TIntegers,
       binding_state_of_bool false, MImmutable)],
     [((("x"%string), 0), [RStore (("x"%string), 0)])],
     [RStore (("x"%string), 0)]).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_roots_let_escape_rejected :
  infer_core_env_roots ex_env_struct_pair [] 0 [] []
    (ELet MImmutable (("x"%string), 0) (MkTy UUnrestricted TIntegers)
      (ELit (LInt 1))
      (EBorrow RShared (PVar (("x"%string), 0)))) =
  infer_err ErrContextCheckFailed.
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_roots_let_initializer_shadow_accepted :
  infer_core_env_roots ex_env_struct_pair [] 0 []
    [((("x"%string), 0), MkTy UUnrestricted TIntegers,
      binding_state_of_bool false, MImmutable)]
    (ELetInfer MImmutable (("x"%string), 0)
      (EBorrow RShared (PVar (("x"%string), 0)))
      EUnit) =
  infer_ok
    (MkTy UUnrestricted TUnits,
     [((("x"%string), 0), MkTy UUnrestricted TIntegers,
       binding_state_of_bool false, MImmutable)],
     [],
     []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_struct_literal_ok :
  infer_core_env ex_env_struct_pair [] 0 []
    (EStruct ("Pair"%string) [] []
      [(("y"%string), ELit (LBool true)); (("x"%string), ELit (LInt 1))]) =
  infer_ok (MkTy UUnrestricted (TStruct ("Pair"%string) [] []), []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_struct_field_ok :
  infer_core_env ex_env_struct_pair [] 0
    [((("p"%string), 0), MkTy UUnrestricted (TStruct ("Pair"%string) [] []),
      binding_state_of_bool false, MImmutable)]
    (EPlace (PField (PVar (("p"%string), 0)) ("x"%string))) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [((("p"%string), 0), MkTy UUnrestricted (TStruct ("Pair"%string) [] []),
       binding_state_of_bool false, MImmutable)]).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_elab_nested_letinfer_ok :
  infer_core_env_elab ex_env_struct_pair [] 0 []
    (ELetInfer MImmutable (("x"%string), 0)
      (ELit (LInt 1))
      (ELetInfer MImmutable (("y"%string), 0)
        (EVar (("x"%string), 0))
        (EVar (("y"%string), 0)))) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [],
     ELet MImmutable (("x"%string), 0) (MkTy UUnrestricted TIntegers)
       (ELit (LInt 1))
       (ELet MImmutable (("y"%string), 0) (MkTy UUnrestricted TIntegers)
         (EVar (("x"%string), 0))
         (EVar (("y"%string), 0)))).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_elab_no_letinfer_same_expr :
  infer_core_env_elab ex_env_struct_pair [] 0 []
    (EIf (ELit (LBool true)) (ELit (LInt 1)) (ELit (LInt 2))) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [],
     EIf (ELit (LBool true)) (ELit (LInt 1)) (ELit (LInt 2))).
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_shared_ref_covariant_inner :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TRef LStatic RShared (MkTy UUnrestricted TIntegers)))
    (MkTy UUnrestricted
      (TRef LStatic RShared (MkTy UAffine TIntegers))) = true.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_unique_ref_invariant_inner :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TRef LStatic RUnique (MkTy UUnrestricted TIntegers)))
    (MkTy UUnrestricted
      (TRef LStatic RUnique (MkTy UAffine TIntegers))) = false.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_closure_env_contra_params_covariant_ret :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TClosure LStatic
        [MkTy UAffine TIntegers]
        (MkTy UUnrestricted TBooleans)))
    (MkTy UAffine
      (TClosure (LVar 0)
        [MkTy UUnrestricted TIntegers]
        (MkTy UAffine TBooleans))) = true.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_fn_expected_closure_bridge :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TFn
        [MkTy UAffine TIntegers]
        (MkTy UUnrestricted TBooleans)))
    (MkTy UAffine
      (TClosure (LVar 0)
        [MkTy UUnrestricted TIntegers]
        (MkTy UAffine TBooleans))) = true.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_closure_not_expected_fn :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TClosure LStatic [] (MkTy UUnrestricted TBooleans)))
    (MkTy UUnrestricted
      (TFn [] (MkTy UUnrestricted TBooleans))) = false.
Proof. vm_compute. reflexivity. Qed.

Example ty_ref_free_b_rejects_closure_value :
  ty_ref_free_b
    (MkTy UUnrestricted
      (TClosure LStatic [] (MkTy UUnrestricted TBooleans))) = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_capture_ref_free_plain_struct : struct_def :=
  MkStructDef "PlainCapture"%string 0 0 [] [
    MkFieldDef "n"%string MImmutable (MkTy UUnrestricted TIntegers)
  ].

Definition ex_capture_ref_free_ref_struct : struct_def :=
  MkStructDef "RefCapture"%string 0 0 [] [
    MkFieldDef "r"%string MImmutable
      (MkTy UUnrestricted
        (TRef LStatic RShared (MkTy UUnrestricted TIntegers)))
  ].

Example capture_ref_free_ty_b_accepts_plain_struct :
  capture_ref_free_ty_b
    (MkGlobalEnv [ex_capture_ref_free_plain_struct] [] [] [] [] [])
    (MkTy UUnrestricted (TStruct "PlainCapture"%string [] [])) = true.
Proof. vm_compute. reflexivity. Qed.

Example capture_ref_free_ty_b_rejects_ref_struct :
  capture_ref_free_ty_b
    (MkGlobalEnv [ex_capture_ref_free_ref_struct] [] [] [] [] [])
    (MkTy UUnrestricted (TStruct "RefCapture"%string [] [])) = false.
Proof. vm_compute. reflexivity. Qed.

Example capture_ref_free_ty_b_rejects_closure_value :
  capture_ref_free_ty_b
    (MkGlobalEnv [] [] [] [] [] [])
    (MkTy UUnrestricted
      (TClosure LStatic [] (MkTy UUnrestricted TBooleans))) = false.
Proof. vm_compute. reflexivity. Qed.
