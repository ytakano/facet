From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram.
Export CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram.
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

(* ------------------------------------------------------------------ *)
(* Borrow conflict checker                                               *)
(*                                                                      *)
(* borrow_check traverses an expression and maintains a borrow_state.   *)
(* It is run after infer succeeds (infer handles structural well-        *)
(* formedness; borrow_check handles aliasing constraints).               *)
(* ------------------------------------------------------------------ *)

Fixpoint borrow_check (fenv : list fn_def) (BS : borrow_state) (Γ : ctx)
    (e : expr) : infer_result borrow_state :=
  match e with
  | EUnit | ELit _ | EVar _ | EPlace _ => infer_ok BS
  | EFn _ => infer_ok BS
  | EMakeClosure _ captures =>
      let fix go (captures0 : list ident) : infer_result borrow_state :=
        match captures0 with
        | [] => infer_ok BS
        | x :: rest =>
            if bs_has_mut x BS
            then infer_err (ErrBorrowConflict x)
            else go rest
        end
      in go captures
  | EStruct _ _ _ _ => infer_err ErrNotImplemented
  | EEnum _ _ _ _ payloads =>
      let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
        match as_ with
        | [] => infer_ok BS0
        | a :: rest =>
            match borrow_check fenv BS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok BS1 => go BS1 rest
            end
        end
      in go BS payloads
  | EMatch _ _ => infer_err ErrNotImplemented

  | EBorrow RShared (PVar x) =>
      if bs_has_mut x BS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (BEShared x :: BS)

  | EBorrow RUnique (PVar x) =>
      if bs_has_any x BS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (BEMut x :: BS)

  (* &*p / &mut *p: treat the root reference as the borrow target *)
  | EBorrow RShared (PDeref p) =>
      let r := place_root p in
      if bs_has_mut r BS
      then infer_err (ErrBorrowConflict r)
      else infer_ok (BEShared r :: BS)

  | EBorrow RUnique (PDeref p) =>
      let r := place_root p in
      if bs_has_any r BS
      then infer_err (ErrBorrowConflict r)
      else infer_ok (BEMut r :: BS)

  | EBorrow _ (PField _ _) => infer_err ErrNotImplemented

  | EDeref e1 =>
      match expr_ref_root e1 with
      | Some r =>
          if bs_has_mut r BS
          then infer_err (ErrBorrowConflict r)
          else borrow_check fenv BS Γ e1
      | None => borrow_check fenv BS Γ e1
      end

  | EDrop e1 =>
      borrow_check fenv BS Γ e1

  | EReplace (PVar _) e_new | EAssign (PVar _) e_new =>
      borrow_check fenv BS Γ e_new

  (* write-through blocked if root has any active re-borrow *)
  | EReplace (PDeref p) e_new | EAssign (PDeref p) e_new =>
      let r := place_root p in
      if bs_has_any r BS
      then infer_err (ErrBorrowConflict r)
      else borrow_check fenv BS Γ e_new

  | EReplace (PField _ _) _ | EAssign (PField _ _) _ =>
      infer_err ErrNotImplemented

  | ELet m x T e1 e2 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let new_from_e1 := bs_new_entries BS BS1 in
          match borrow_check fenv BS1 (ctx_add_b x T m Γ) e2 with
          | infer_err err => infer_err err
          | infer_ok BS2  => infer_ok (bs_remove_all new_from_e1 BS2)
          end
      end

  | ELetInfer m x e1 e2 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let new_from_e1 := bs_new_entries BS BS1 in
          match borrow_check fenv BS1 Γ e2 with
          | infer_err err => infer_err err
          | infer_ok BS2  => infer_ok (bs_remove_all new_from_e1 BS2)
          end
      end

  | EIf e1 e2 e3 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1  =>
          match borrow_check fenv BS1 Γ e2,
                borrow_check fenv BS1 Γ e3 with
          | infer_ok BS2, infer_ok BS3 =>
              if bs_eqb BS2 BS3
              then infer_ok BS2
              else infer_err ErrContextCheckFailed
          | infer_err err, _ | _, infer_err err => infer_err err
          end
      end

  | ECall _ args =>
      let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
        match as_ with
        | []      => infer_ok BS0
        | a :: rest =>
            match borrow_check fenv BS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok BS1  => go BS1 rest
            end
        end
      in go BS args
  | ECallGeneric _ _ args =>
      let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
        match as_ with
        | []      => infer_ok BS0
        | a :: rest =>
            match borrow_check fenv BS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok BS1  => go BS1 rest
            end
        end
      in go BS args
  | ECallExpr callee args =>
      match borrow_check fenv BS Γ callee with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
            match as_ with
            | []      => infer_ok BS0
            | a :: rest =>
                match borrow_check fenv BS0 Γ a with
                | infer_err err => infer_err err
                | infer_ok BS2  => go BS2 rest
                end
            end
          in go BS1 args
      end
  | ECallExprGeneric callee _ args =>
      match borrow_check fenv BS Γ callee with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
            match as_ with
            | []      => infer_ok BS0
            | a :: rest =>
                match borrow_check fenv BS0 Γ a with
                | infer_err err => infer_err err
                | infer_ok BS2  => go BS2 rest
                end
            end
          in go BS1 args
      end
  end.

(* Separate top-level borrow_check_args for BorrowCheckSoundness proofs. *)
Fixpoint borrow_check_args (fenv : list fn_def) (BS : borrow_state) (Γ : ctx)
    (args : list expr) : infer_result borrow_state :=
  match args with
  | []       => infer_ok BS
  | a :: rest =>
      match borrow_check fenv BS Γ a with
      | infer_err err => infer_err err
      | infer_ok BS1  => borrow_check_args fenv BS1 Γ rest
      end
  end.

Inductive path_borrow_entry : Type :=
  | PBShared : ident -> field_path -> path_borrow_entry
  | PBMut : ident -> field_path -> path_borrow_entry.

Definition path_borrow_state := list path_borrow_entry.

Definition pbe_target_eqb (x : ident) (p : field_path) (e : path_borrow_entry) : bool :=
  match e with
  | PBShared y q | PBMut y q => ident_eqb x y && path_conflict_b p q
  end.

Definition pbs_has_mut (x : ident) (p : field_path) (PBS : path_borrow_state) : bool :=
  existsb (fun e =>
    match e with
    | PBMut y q => ident_eqb x y && path_conflict_b p q
    | _ => false
    end) PBS.

Definition pbs_has_any (x : ident) (p : field_path) (PBS : path_borrow_state) : bool :=
  existsb (pbe_target_eqb x p) PBS.

Definition borrow_target_of_place (p : place) : ident * field_path :=
  (place_root p, place_suffix_path p).

Definition path_borrow_entry_eqb (a b : path_borrow_entry) : bool :=
  match a, b with
  | PBShared x p, PBShared y q
  | PBMut x p, PBMut y q => ident_eqb x y && path_eqb p q
  | _, _ => false
  end.

Fixpoint pbs_remove_one (e : path_borrow_entry) (PBS : path_borrow_state)
    : path_borrow_state :=
  match PBS with
  | [] => []
  | h :: rest =>
      if path_borrow_entry_eqb e h then rest else h :: pbs_remove_one e rest
  end.

Definition pbs_remove_all (to_remove PBS : path_borrow_state) : path_borrow_state :=
  fold_left (fun acc e => pbs_remove_one e acc) to_remove PBS.

Definition pbs_new_entries (before after : path_borrow_state) : path_borrow_state :=
  firstn (List.length after - List.length before) after.

Fixpoint pbs_eqb (a b : path_borrow_state) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => path_borrow_entry_eqb x y && pbs_eqb xs ys
  | _, _ => false
  end.

Definition pbs_access_allowed_b
    (x : ident) (p : field_path) (PBS : path_borrow_state) (T : Ty) : bool :=
  negb (pbs_has_mut x p PBS) &&
  (usage_eqb (ty_usage T) UUnrestricted || negb (pbs_has_any x p PBS)).

Definition borrow_check_place_access
    (env : global_env) (PBS : path_borrow_state) (Γ : ctx) (p : place)
    : infer_result unit :=
  match place_path p with
  | None => infer_ok tt
  | Some (x, path) =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          if pbs_access_allowed_b x path PBS T
          then infer_ok tt
          else infer_err (ErrBorrowConflict x)
      end
  end.

Fixpoint borrow_check_env (env : global_env) (PBS : path_borrow_state) (Γ : ctx)
    (e : expr) : infer_result path_borrow_state :=
  match e with
  | EUnit | ELit _ | EFn _ => infer_ok PBS
  | EMakeClosure _ captures =>
      let fix go (captures0 : list ident) : infer_result path_borrow_state :=
        match captures0 with
        | [] => infer_ok PBS
        | x :: rest =>
            if pbs_has_mut x [] PBS
            then infer_err (ErrBorrowConflict x)
            else go rest
        end
      in go captures
  | EVar x =>
      match borrow_check_place_access env PBS Γ (PVar x) with
      | infer_ok _ => infer_ok PBS
      | infer_err err => infer_err err
      end
  | EPlace p =>
      match borrow_check_place_access env PBS Γ p with
      | infer_ok _ => infer_ok PBS
      | infer_err err => infer_err err
      end
  | EStruct _ _ _ fields =>
      let fix go (PBS0 : path_borrow_state) (fields0 : list (string * expr))
          : infer_result path_borrow_state :=
        match fields0 with
        | [] => infer_ok PBS0
        | (_, e_field) :: rest =>
            match borrow_check_env env PBS0 Γ e_field with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS fields
  | EEnum _ _ _ _ payloads =>
      let fix go (PBS0 : path_borrow_state) (args0 : list expr)
          : infer_result path_borrow_state :=
        match args0 with
        | [] => infer_ok PBS0
        | a :: rest =>
            match borrow_check_env env PBS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS payloads
  | EMatch scrut branches =>
      match borrow_check_env env PBS Γ scrut with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let fix go (expected : option path_borrow_state)
              (branches0 : list (string * list ident * expr))
              : infer_result path_borrow_state :=
            match branches0 with
            | [] =>
                match expected with
                | Some PBS_out => infer_ok PBS_out
                | None => infer_err (ErrMissingVariant "")
                end
            | (_, binders, e_branch) :: rest =>
                let Γ_branch := ctx_add_params (unrestricted_unit_params_of_binders binders) Γ in
                match borrow_check_env env PBS1 Γ_branch e_branch with
                | infer_err err => infer_err err
                | infer_ok PBS_branch =>
                    match expected with
                    | None => go (Some PBS_branch) rest
                    | Some PBS_expected =>
                        if pbs_eqb PBS_branch PBS_expected
                        then go expected rest
                        else infer_err ErrContextCheckFailed
                    end
                end
            end
          in go None branches
      end
  | EBorrow RShared p =>
      let '(x, path) := borrow_target_of_place p in
      if pbs_has_mut x path PBS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (PBShared x path :: PBS)
  | EBorrow RUnique p =>
      let '(x, path) := borrow_target_of_place p in
      if pbs_has_any x path PBS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (PBMut x path :: PBS)
  | EReplace p e_new | EAssign p e_new =>
      let '(x, path) := borrow_target_of_place p in
      if pbs_has_any x path PBS
      then infer_err (ErrBorrowConflict x)
      else borrow_check_env env PBS Γ e_new
  | EDeref e1 =>
      match expr_ref_root e1 with
      | Some r =>
          if pbs_has_mut r [] PBS
          then infer_err (ErrBorrowConflict r)
          else borrow_check_env env PBS Γ e1
      | None => borrow_check_env env PBS Γ e1
      end
  | EDrop e1 => borrow_check_env env PBS Γ e1
  | ELet m x T e1 e2 =>
      match borrow_check_env env PBS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let new_from_e1 := pbs_new_entries PBS PBS1 in
          match borrow_check_env env PBS1 (ctx_add_b x T m Γ) e2 with
          | infer_err err => infer_err err
          | infer_ok PBS2 => infer_ok (pbs_remove_all new_from_e1 PBS2)
          end
      end
  | ELetInfer m x e1 e2 =>
      match borrow_check_env env PBS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let new_from_e1 := pbs_new_entries PBS PBS1 in
          match borrow_check_env env PBS1 Γ e2 with
          | infer_err err => infer_err err
          | infer_ok PBS2 => infer_ok (pbs_remove_all new_from_e1 PBS2)
          end
      end
  | EIf e1 e2 e3 =>
      match borrow_check_env env PBS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          match borrow_check_env env PBS1 Γ e2,
                borrow_check_env env PBS1 Γ e3 with
          | infer_ok PBS2, infer_ok PBS3 =>
              if pbs_eqb PBS2 PBS3
              then infer_ok PBS2
              else infer_err ErrContextCheckFailed
          | infer_err err, _ | _, infer_err err => infer_err err
          end
      end
  | ECall _ args =>
      let fix go (PBS0 : path_borrow_state) (args0 : list expr)
          : infer_result path_borrow_state :=
        match args0 with
        | [] => infer_ok PBS0
        | a :: rest =>
            match borrow_check_env env PBS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS args
  | ECallGeneric _ _ args =>
      let fix go (PBS0 : path_borrow_state) (args0 : list expr)
          : infer_result path_borrow_state :=
        match args0 with
        | [] => infer_ok PBS0
        | a :: rest =>
            match borrow_check_env env PBS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS args
  | ECallExpr callee args =>
      match borrow_check_env env PBS Γ callee with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let fix go (PBS0 : path_borrow_state) (args0 : list expr)
              : infer_result path_borrow_state :=
            match args0 with
            | [] => infer_ok PBS0
            | a :: rest =>
                match borrow_check_env env PBS0 Γ a with
                | infer_err err => infer_err err
                | infer_ok PBS2 => go PBS2 rest
                end
            end
          in go PBS1 args
      end
  | ECallExprGeneric callee _ args =>
      match borrow_check_env env PBS Γ callee with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let fix go (PBS0 : path_borrow_state) (args0 : list expr)
              : infer_result path_borrow_state :=
            match args0 with
            | [] => infer_ok PBS0
            | a :: rest =>
                match borrow_check_env env PBS0 Γ a with
                | infer_err err => infer_err err
                | infer_ok PBS2 => go PBS2 rest
                end
            end
          in go PBS1 args
      end
  end.

(* ------------------------------------------------------------------ *)
(* Combined type + borrow checker                                        *)
(* ------------------------------------------------------------------ *)

(* Legacy checker retained for proof compatibility only.  The OCaml CLI
   and extraction roots use the env/stateful checker below. *)
Definition infer_full (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer fenv f with
  | infer_err err => infer_err err
  | infer_ok res  =>
      let Γ := fn_body_ctx f in
      match borrow_check fenv [] Γ (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _    => infer_ok res
      end
  end.

Definition infer_full_env (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer_env env f with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition infer_full_env_elab (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * fn_def) :=
  match infer_env_elab env f with
  | infer_err err => infer_err err
  | infer_ok (T, Γ, f') =>
      match borrow_check_env env [] (fn_body_ctx f') (fn_body f') with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok (T, Γ, f')
      end
  end.

Definition infer_full_env_roots (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_env_roots env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition infer_full_env_roots_checked (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_env_roots_shadow_safe_checked env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition alpha_normalize_global_env (env : global_env) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    (env_local_bounds env) (alpha_rename_syntax (env_fns env)).

Fixpoint expr_vars_match_params (args : list expr) (ps : list param) : bool :=
  match args, ps with
  | [], [] => true
  | EVar x :: args', p :: ps' =>
      ident_eqb x (param_name p) && expr_vars_match_params args' ps'
  | _, _ => false
  end.

Definition specialize_simple_generic_wrapper_call
    (env : global_env) (fname : ident) (type_args : list Ty)
    (args : list expr) : option (ident * list Ty * list expr) :=
  match lookup_fn_b fname (env_fns env) with
  | None => None
  | Some fdef =>
      if no_captures_b fdef &&
         Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
      then
        match fn_body fdef with
        | ECallGeneric target nested_type_args wrapper_args =>
            if expr_vars_match_params wrapper_args (fn_params fdef)
            then Some (target,
              map (subst_type_params_ty type_args) nested_type_args, args)
            else None
        | _ => None
        end
      else None
  end.

Definition specialize_simple_generic_wrapper_calls_top
    (env : global_env) (e : expr) : expr :=
  match e with
  | ECallGeneric fname type_args args =>
      match specialize_simple_generic_wrapper_call env fname type_args args with
      | Some (target, target_type_args, target_args) =>
          ECallGeneric target target_type_args target_args
      | None => e
      end
  | _ => e
  end.

Definition simplify_local_fn_value_result_let_top (e : expr) : expr :=
  match e with
  | ELet m x T (EFn fname)
      (ELet m_res result T_res (ECallExpr (EVar y) args) (EVar result')) =>
      if ident_eqb x y && ident_eqb result result' &&
         usage_eqb (ty_usage T) UUnrestricted
      then ELet m x T (EFn fname) (ECallExpr (EVar y) args)
      else e
  | ELetInfer m x (EFn fname)
      (ELet m_res result T_res (ECallExpr (EVar y) args) (EVar result')) =>
      if ident_eqb x y && ident_eqb result result'
      then ELetInfer m x (EFn fname) (ECallExpr (EVar y) args)
      else e
  | _ => e
  end.

Definition specialize_simple_generic_wrapper_fn
    (env : global_env) (f : fn_def) : fn_def :=
  fn_with_body f
    (simplify_local_fn_value_result_let_top
      (specialize_simple_generic_wrapper_calls_top env (fn_body f))).

Fixpoint specialize_simple_generic_wrapper_fns
    (env : global_env) (fns : list fn_def) : list fn_def :=
  match fns with
  | [] => []
  | f :: rest =>
      specialize_simple_generic_wrapper_fn env f ::
      specialize_simple_generic_wrapper_fns env rest
  end.

Fixpoint infer_fns_env_elab (env : global_env) (fns : list fn_def)
    : infer_result (list fn_def) :=
  match fns with
  | [] => infer_ok []
  | f :: rest =>
      match infer_full_env_elab env f with
      | infer_err err => infer_err err
      | infer_ok (_, _, f') =>
          match infer_fns_env_elab env rest with
          | infer_err err => infer_err err
          | infer_ok rest' => infer_ok (f' :: rest')
          end
      end
  end.

Definition infer_program_env_alpha_elab (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  match infer_fns_env_elab env_alpha (env_fns env_alpha) with
  | infer_err err => infer_err err
  | infer_ok fns' =>
      let env_elab := MkGlobalEnv (env_structs env_alpha) (env_enums env_alpha)
        (env_traits env_alpha) (env_impls env_alpha)
        (env_local_bounds env_alpha) fns' in
      infer_ok (MkGlobalEnv (env_structs env_elab) (env_enums env_elab)
        (env_traits env_elab) (env_impls env_elab)
        (env_local_bounds env_elab)
        (specialize_simple_generic_wrapper_fns env_elab fns'))
  end.

Definition fn_params_roots_exclude_b (ps : list param) (roots : root_set) : bool :=
  forallb (fun x => roots_exclude_b x roots) (ctx_names (params_ctx ps)).

Definition fn_params_root_env_excludes_b (ps : list param) (R : root_env) : bool :=
  forallb (fun x => root_env_excludes_b x R) (ctx_names (params_ctx ps)).

Definition check_fn_root_shadow_summary (env : global_env) (fdef : fn_def) : bool :=
  preservation_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | infer_err _ => false
  end.

Definition check_env_root_shadow_summary (env : global_env) : bool :=
  forallb (check_fn_root_shadow_summary env) (env_fns env).

Definition check_fn_root_shadow_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  provenance_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | infer_err _ => false
  end.

Definition check_env_root_shadow_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_provenance_summary env) (env_fns env).

Fixpoint store_safe_function_value_call_args_b
    (env : global_env) (args : list expr) : bool :=
  match args with
  | [] => true
  | EUnit :: rest =>
      store_safe_function_value_call_args_b env rest
  | ELit _ :: rest =>
      store_safe_function_value_call_args_b env rest
  | EVar _ :: rest =>
      store_safe_function_value_call_args_b env rest
  | EFn fname :: rest =>
      match lookup_fn_b fname (env_fns env) with
      | Some callee =>
          check_fn_root_shadow_provenance_summary env callee &&
          store_safe_function_value_call_args_b env rest
      | None => false
      end
  | _ :: _ => false
  end.

Definition direct_call_target_expr (e : expr) : option (ident * list expr * expr) :=
  match e with
  | ECall fname args => Some (fname, args, ECall fname args)
  | ECallExpr (EFn fname) args => Some (fname, args, ECall fname args)
  | _ => None
  end.

Definition generic_direct_call_target_expr
    (e : expr) : option (ident * list Ty * list expr * expr) :=
  match e with
  | ECallGeneric fname type_args args =>
      Some (fname, type_args, args, ECallGeneric fname type_args args)
  | _ => None
  end.

Definition let_bound_generic_direct_call_target_expr
    (e : expr) : option (ident * list Ty * list expr * Ty * expr) :=
  match e with
  | ELet m x T_hidden (ECallGeneric fname type_args args) (EVar y) =>
      if ident_eqb x y
      then Some
        (fname, type_args, args, T_hidden,
          ELet m x T_hidden (ECallGeneric fname type_args args) (EVar y))
      else None
  | _ => None
  end.

Definition if_literal_generic_direct_call_target_expr
    (e : expr)
    : option (bool * ident * list Ty * list expr *
              ident * list Ty * list expr * expr) :=
  match e with
  | EIf (ELit (LBool b))
      (ECallGeneric fname_then type_args_then args_then)
      (ECallGeneric fname_else type_args_else args_else) =>
      if ident_eqb fname_then fname_else &&
         ty_list_eqb type_args_then type_args_else
      then
        match args_then, args_else with
        | [], [] => Some (b, fname_then, type_args_then, args_then,
            fname_else, type_args_else, args_else,
            EIf (ELit (LBool b))
              (ECallGeneric fname_then type_args_then args_then)
              (ECallGeneric fname_else type_args_else args_else))
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition direct_call_ready_expr_b (e : expr) : bool :=
  match direct_call_target_expr e with
  | Some (_, args, _) => preservation_ready_args_b args
  | None => false
  end.

Definition check_fn_root_shadow_direct_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_provenance_summary env fdef with
  | true => true
  | false =>
      match direct_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          end
      | None => false
      end
  end.

Definition local_fn_value_call_target_expr
    (e : expr) : option (ident * list expr * expr) :=
  match e with
  | ELet m x T (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted
      then Some (fname, args, ELet m x T (EFn fname) (ECall fname args))
      else None
  | ELetInfer m x (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y
      then Some (fname, args, ELetInfer m x (EFn fname) (ECall fname args))
      else None
  | _ => None
  end.

Definition local_fn_value_call_target_expr_with_binder
    (e : expr) : option (ident * ident * list expr * expr) :=
  match e with
  | ELet m x T (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted
      then Some (x, fname, args, ELet m x T (EFn fname) (ECall fname args))
      else None
  | ELetInfer m x (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y
      then Some (x, fname, args, ELetInfer m x (EFn fname) (ECall fname args))
      else None
  | _ => None
  end.

Definition supported_non_type_generic_function_value_call_callee_ty_b
    (T : Ty) : bool :=
  match ty_core T with
  | TFn _ _ => true
  | TForall _ _ body =>
      match ty_core body with
      | TFn _ _ => true
      | _ => false
      end
  | _ => false
  end.

Definition supported_type_generic_function_value_call_callee_ty_b
    (T : Ty) : bool :=
  match ty_core T with
  | TTypeForall _ bounds body =>
      match bounds with
      | [] =>
          match ty_core body with
          | TFn _ _ => true
          | _ => false
          end
      | _ :: _ => false
      end
  | _ => false
  end.

Definition type_arg_no_lifetime_forall_b (T : Ty) : bool :=
  match ty_core T with
  | TForall _ _ _ => false
  | _ => true
  end.

Definition type_args_no_lifetime_forall_b (type_args : list Ty) : bool :=
  forallb type_arg_no_lifetime_forall_b type_args.

Definition type_args_lbound_free_b (type_args : list Ty) : bool :=
  forallb (fun T => negb (contains_lbound_ty T)) type_args.

Definition check_supported_non_type_generic_function_value_call_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (callee : expr) : bool :=
  match callee with
  | EVar _ =>
      match infer_core_env_roots_shadow_safe env Ω n R Γ callee with
      | infer_ok (T_callee, _, _, _) =>
          supported_non_type_generic_function_value_call_callee_ty_b T_callee
      | infer_err _ => false
      end
  | _ => false
  end.

Definition check_supported_type_generic_function_value_call_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (callee : expr)
    (type_args : list Ty) : bool :=
  type_args_lbound_free_b type_args &&
  type_args_no_lifetime_forall_b type_args &&
  match callee with
  | EVar _ =>
      match infer_core_env_roots_shadow_safe env Ω n R Γ callee with
      | infer_ok (T_callee, _, _, _) =>
          match ty_core T_callee with
          | TTypeForall type_params bounds body =>
              Nat.eqb (Datatypes.length type_args) type_params &&
              match bounds with
              | [] =>
                  match ty_core body with
                  | TFn _ _ => true
                  | _ => false
                  end
              | _ :: _ => false
              end
          | _ => false
          end
      | infer_err _ => false
      end
  | _ => false
  end.

Definition check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
    (check_expr : nat -> global_env -> outlives_ctx -> nat ->
      root_env -> sctx -> expr -> bool)
    (fuel : nat) (env : global_env) (fdef : fn_def)
    (type_args : list Ty) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      let body_ctx := subst_type_params_ctx type_args (fn_body_ctx fdef) in
      let body := subst_type_params_expr type_args (fn_body fdef) in
      let params := apply_type_params type_args (fn_params fdef) in
      let body_env :=
        global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)) in
      match infer_env_roots_shadow_safe env fdef
              (initial_root_env_for_fn fdef) with
      | infer_err _ => false
      | infer_ok _ =>
          match infer_core_env_state_fuel_roots_shadow_safe fuel' body_env
                   (fn_outlives fdef)
                   (fn_lifetimes fdef)
                   (initial_root_env_for_fn fdef)
                   (sctx_of_ctx body_ctx) body with
          | infer_ok (T_body, _, R_body, roots_body) =>
              check_expr fuel' body_env (fn_outlives fdef) (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef) (sctx_of_ctx body_ctx) body &&
              ty_compatible_b (fn_outlives fdef) T_body
                (subst_type_params_ty type_args (fn_ret fdef)) &&
              fn_params_roots_exclude_b params roots_body &&
              fn_params_root_env_excludes_b params R_body
          | infer_err _ => false
          end
      end
  end.

Definition check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (check_expr : nat -> global_env -> outlives_ctx -> nat ->
      root_env -> sctx -> expr -> bool)
    (fuel : nat) (env : global_env) (type_args : list Ty) : bool :=
  forallb
    (fun fdef =>
      if Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
      then
        check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
          check_expr fuel env fdef type_args
      else true)
    (env_fns env).

Definition check_fn_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_direct_call_provenance_summary env fdef with
  | true => true
  | false =>
      match local_fn_value_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          end
      | None =>
          match fn_body fdef with
          | ECallExpr callee args =>
              preservation_ready_expr_b callee &&
              preservation_ready_args_b args &&
              check_supported_non_type_generic_function_value_call_expr
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef)
                (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef)
                (fn_body_ctx fdef)
                callee &&
              match infer_env_roots_shadow_safe env fdef
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          | _ => false
          end
      end
  end.

Definition captured_call_target_expr
    (e : expr) : option (ident * list ident * list expr) :=
  match e with
  | ECallExpr (EMakeClosure fname captures) args =>
      Some (fname, captures, args)
  | _ => None
  end.

Definition args_free_vars_checker (args : list expr) : list ident :=
  args_local_store_names_with free_vars_expr args.

Definition local_captured_call_target_expr
    (e : expr)
    : option (ident * list ident * list expr * mutability * ident * Ty *
        expr * expr) :=
  match e with
  | ELet m x T (EMakeClosure fname captures) (ECallExpr (EVar y) args) =>
      if ident_eqb x y &&
         usage_eqb (ty_usage T) UUnrestricted &&
         negb (existsb (ident_eqb x) captures) &&
         negb (existsb (ident_eqb x) (args_free_vars_checker args)) &&
         negb (existsb (ident_eqb x) (args_local_store_names args))
      then
        let direct_body := ECallExpr (EMakeClosure fname captures) args in
        Some (fname, captures, args, m, x, T, direct_body,
          ELet m x T (EMakeClosure fname captures) direct_body)
      else None
  | _ => None
  end.

Definition check_fn_root_shadow_captured_callee_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  provenance_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef
          (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef)) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef ++ fn_captures fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef ++ fn_captures fdef) R_out
  | infer_err _ => false
  end.

Fixpoint capture_root_bound
    (R : root_env) (captures : list ident) (caps : list param)
    : option root_set :=
  match captures, caps with
  | [], [] => Some []
  | x :: captures', _ :: caps' =>
      match root_env_lookup x R, capture_root_bound R captures' caps' with
      | Some roots, Some rest => Some (root_set_union roots rest)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition callee_hidden_capture_args_disjoint_b
    (callee : fn_def) (args : list expr) : bool :=
  forallb
    (fun x =>
       negb (existsb (ident_eqb x) (args_local_store_names args)))
    (ctx_names (params_ctx (fn_captures callee))).

Fixpoint check_expr_root_shadow_captured_call_provenance_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      provenance_ready_expr_b e ||
      match direct_call_target_expr e with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel env Ω n R Σ synthetic_body with
              | infer_ok _ => true
              | infer_err _ => false
              end
          end
      | None => false
      end ||
      match captured_call_target_expr e with
      | Some (fname, captures, args) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              match check_make_closure_captures_exact_sctx_with_env env
                      Ω Σ captures (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  match capture_root_bound R captures (fn_captures callee) with
                  | Some _ =>
                      check_fn_root_shadow_captured_callee_provenance_summary
                        env callee
                  | None => false
                  end
              end
          end
      | None => false
      end ||
      match local_captured_call_target_expr e with
      | Some (fname, captures, args, m, x, T_hidden, direct_body, let_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              negb (existsb (ident_eqb x)
                (ctx_names (params_ctx (fn_captures callee)))) &&
              match root_env_lookup x R with
              | Some _ => false
              | None =>
                  match check_make_closure_captures_exact_sctx_with_env env
                          Ω Σ captures (fn_captures callee) with
                  | infer_err _ => false
                  | infer_ok _ =>
                      match capture_root_bound R captures
                              (fn_captures callee) with
                      | None => false
                      | Some _ =>
                          check_fn_root_shadow_captured_callee_provenance_summary
                            env callee &&
                          match
                            infer_core_env_state_fuel_roots_shadow_safe
                              fuel env Ω n R Σ direct_body,
                            infer_core_env_state_fuel_roots_shadow_safe
                              fuel env Ω n R Σ e
                          with
	                          | infer_ok (T_direct, Σ_direct, R_direct, _),
	                            infer_ok (T_let, Σ_let, R_let, _) =>
	                              sctx_eqb Σ_direct Σ_let &&
	                              root_env_eqb R_direct R_let &&
	                              ty_compatible_b Ω T_direct T_let
                          | _, _ => false
                          end
                      end
                  end
              end
          end
      | None => false
      end ||
      match e with
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              provenance_ready_expr_b e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      capture_ref_free_ty_b env T2 &&
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_captured_call_provenance_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | _ => false
      end ||
      match e with
      | EIf e1 e2 e3 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T_cond, Σ1, R1, _) =>
              ty_core_eqb (ty_core T_cond) TBooleans &&
              provenance_ready_expr_b e1 &&
              check_expr_root_shadow_captured_call_provenance_summary_fuel
                fuel' env Ω n R1 Σ1 e2 &&
              check_expr_root_shadow_captured_call_provenance_summary_fuel
                fuel' env Ω n R1 Σ1 e3
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_captured_call_provenance_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_captured_call_provenance_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint non_function_value_ty_b (T : Ty) : bool :=
  match T with
  | MkTy _ (TFn _ _) => false
  | MkTy _ (TClosure _ _ _) => false
  | MkTy _ (TForall _ _ body) => non_function_value_ty_b body
  | MkTy _ (TTypeForall _ _ body) => non_function_value_ty_b body
  | _ => true
  end.

Fixpoint check_expr_root_shadow_store_safe_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      check_expr_root_shadow_captured_call_provenance_summary_fuel
        fuel env Ω n R Σ e ||
      match e with
      | ECallExpr callee args =>
          preservation_ready_args_b args &&
          check_supported_non_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee
      | _ => false
      end ||
      match e with
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      capture_ref_free_ty_b env T2 &&
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | _ => false
      end ||
      match e with
      | EIf e1 e2 e3 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T_cond, Σ1, R1, _) =>
              ty_core_eqb (ty_core T_cond) TBooleans &&
              provenance_ready_expr_b e1 &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R1 Σ1 e2 &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R1 Σ1 e3
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_store_safe_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint check_expr_root_shadow_store_safe_narrow_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok (T, Σ', R', roots) =>
      match e with
      | EUnit => true
      | EStruct name _ _ [] =>
          match lookup_struct name env with
          | Some sdef =>
              match struct_bounds sdef with
              | [] => capture_ref_free_ty_b env T
              | _ :: _ => false
              end
          | None => false
          end
      | EVar _ => non_function_value_ty_b T
      | EAssign _ (ELit _) => true
      | EAssign (PVar x) (ECallGeneric fname type_args []) =>
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              match fn_bounds callee with
              | [] =>
                  match fn_params callee with
                  | [] =>
                      Nat.eqb (Datatypes.length type_args) (fn_type_params callee) &&
                      let body_ctx :=
                        subst_type_params_ctx type_args (fn_body_ctx callee) in
                      let body :=
                        subst_type_params_expr type_args (fn_body callee) in
                      match body_ctx with
                      | [] =>
                      match body with
                      | EStruct _ _ _ [] =>
                          let params := apply_type_params type_args (fn_params callee) in
                          match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env (fn_outlives callee)
                                  (fn_lifetimes callee)
                                  (initial_root_env_for_fn callee)
                                  (sctx_of_ctx body_ctx) body,
                                infer_env_roots_shadow_safe env callee
                                  (initial_root_env_for_fn callee),
                                infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env Ω n R Σ
                                  (ECallGeneric fname type_args []),
                                infer_place_sctx env Σ (PVar x) with
                          | infer_ok (T_body, _, R_body, roots_body),
                            infer_ok _,
                            infer_ok (T_rhs, _, _, _),
                            infer_ok T_old =>
                              check_expr_root_shadow_store_safe_narrow_summary_fuel
                                fuel' env (fn_outlives callee)
                                (fn_lifetimes callee)
                                (initial_root_env_for_fn callee)
                                (sctx_of_ctx body_ctx) body &&
                              ty_compatible_b (fn_outlives callee) T_body
                                (subst_type_params_ty type_args (fn_ret callee)) &&
                              fn_params_roots_exclude_b params roots_body &&
                              fn_params_root_env_excludes_b params R_body &&
                              ty_compatible_b Ω T_rhs T_old
                          | _, _, _, _ => false
                          end
                      | _ => false
                      end
                      | _ :: _ => false
                      end
                  | _ :: _ => false
                  end
              | _ :: _ => false
              end
          end
      | EAssign _ _ => false
      | EDrop (EPlace p) =>
          match place_path p with
          | Some _ => true
          | None => false
          end
      | EDrop _ => false
      | EBorrow rk p =>
          match place_path p with
          | Some _ => true
          | None =>
              match rk with
              | RShared => false
              | RUnique =>
                  place_resolved_write_writable_chain_b env R Σ p &&
                  match place_resolved_write_target R p with
                  | Some root_x =>
                      match singleton_store_root roots with
                      | Some root_y => ident_eqb root_x root_y
                      | None => false
                      end
                  | None => false
                  end
              end
          end
      | ECallExpr callee args =>
          store_safe_function_value_call_args_b env args &&
          check_supported_non_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee
      | ECallExprGeneric callee type_args args =>
          store_safe_function_value_call_args_b env args &&
          check_supported_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee type_args &&
          check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
            check_expr_root_shadow_store_safe_narrow_summary_fuel
            (S fuel') env type_args
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              non_function_value_ty_b T_hidden &&
              check_expr_root_shadow_store_safe_narrow_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_narrow_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | ELetInfer m x e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              non_function_value_ty_b T1 &&
              check_expr_root_shadow_store_safe_narrow_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T1 m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      sctx_check_ok env x T1 Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_narrow_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T1 m Σ1) e2
                  end
              end
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_store_safe_narrow_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_narrow_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (fuel : nat) (env : global_env) (fdef : fn_def)
    (type_args : list Ty) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      let body_ctx := subst_type_params_ctx type_args (fn_body_ctx fdef) in
      let body := subst_type_params_expr type_args (fn_body fdef) in
      let params := apply_type_params type_args (fn_params fdef) in
      let body_env :=
        global_env_with_local_bounds env
          (subst_type_params_trait_bounds type_args (fn_bounds fdef)) in
      match infer_env_roots_shadow_safe env fdef
              (initial_root_env_for_fn fdef) with
      | infer_err _ => false
      | infer_ok _ =>
          check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
            check_expr_root_shadow_store_safe_narrow_summary_fuel
            (S fuel') env fdef type_args ||
          match generic_direct_call_target_expr body with
          | Some (fname, nested_type_args, args, synthetic_body) =>
              store_safe_function_value_call_args_b env args &&
              match lookup_fn_b fname (env_fns env) with
              | None => false
              | Some fcallee =>
                  Nat.eqb (Datatypes.length nested_type_args)
                    (fn_type_params fcallee) &&
                  match check_struct_bounds body_env (fn_bounds fcallee)
                          nested_type_args with
                  | Some _ => false
                  | None =>
                      match infer_core_env_roots_shadow_safe body_env
                              (fn_outlives fdef) (fn_lifetimes fdef)
                              (initial_root_env_for_fn fdef) body_ctx
                              synthetic_body with
                      | infer_ok (T_synth, _, R_synth, roots_synth) =>
                          check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
                            fuel' env fcallee nested_type_args &&
                          ty_compatible_b (fn_outlives fdef) T_synth
                            (subst_type_params_ty type_args (fn_ret fdef)) &&
                          fn_params_roots_exclude_b params roots_synth &&
                          fn_params_root_env_excludes_b params R_synth
                      | infer_err _ => false
                      end
                  end
              end
          | None => false
          end
      end
  end.

Definition check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
    (env : global_env) (fdef : fn_def) (type_args : list Ty) : bool :=
  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    10000 env fdef type_args.

Fixpoint check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match check_expr_root_shadow_store_safe_narrow_summary_fuel
          fuel env Ω n R Σ e with
  | true => true
  | false =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
      | infer_ok (T, _, _, _) =>
          match e with
          | EDeref (EBorrow RShared _) => capture_ref_free_ty_b env T
          | EStruct _ _ _ [] => capture_ref_free_ty_b env T
          | ELet m x T_hidden e1 e2 =>
              match fuel with
              | 0 => false
              | S fuel' =>
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n R Σ e1 with
                  | infer_err _ => false
                  | infer_ok (T1, Σ1, R1, roots1) =>
                      ty_compatible_b Ω T1 T_hidden &&
                      non_function_value_ty_b T_hidden &&
                      (check_expr_root_shadow_store_safe_narrow_summary_fuel
                         fuel' env Ω n R Σ e1 ||
                       (capture_ref_free_ty_b env T1 &&
                        check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                          fuel' env Ω n R Σ e1)) &&
                      match root_env_lookup x R1 with
                      | Some _ => false
                      | None =>
                          roots_exclude_b x roots1 &&
                          root_env_excludes_b x R1 &&
                          match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env Ω n
                                  (root_env_add x roots1 R1)
                                  (sctx_add x T_hidden m Σ1) e2 with
                          | infer_err _ => false
                          | infer_ok (T2, Σ2, R2, _) =>
                              sctx_check_ok env x T_hidden Σ2 &&
                              capture_ref_free_ty_b env T2 &&
                              root_env_excludes_b x (root_env_remove x R2) &&
                              check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env Ω n
                                (root_env_add x roots1 R1)
                                (sctx_add x T_hidden m Σ1) e2
                          end
                      end
                  end
              end
          | ELetInfer m x e1 e2 =>
              match fuel with
              | 0 => false
              | S fuel' =>
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n R Σ e1 with
                  | infer_err _ => false
                  | infer_ok (T1, Σ1, R1, roots1) =>
                      non_function_value_ty_b T1 &&
                      (check_expr_root_shadow_store_safe_narrow_summary_fuel
                         fuel' env Ω n R Σ e1 ||
                       (capture_ref_free_ty_b env T1 &&
                        check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                          fuel' env Ω n R Σ e1)) &&
                      match root_env_lookup x R1 with
                      | Some _ => false
                      | None =>
                          roots_exclude_b x roots1 &&
                          root_env_excludes_b x R1 &&
                          match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env Ω n
                                  (root_env_add x roots1 R1)
                                  (sctx_add x T1 m Σ1) e2 with
                          | infer_err _ => false
                          | infer_ok (T2, Σ2, R2, _) =>
                              sctx_check_ok env x T1 Σ2 &&
                              capture_ref_free_ty_b env T2 &&
                              root_env_excludes_b x (root_env_remove x R2) &&
                              check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env Ω n
                                (root_env_add x roots1 R1)
                                (sctx_add x T1 m Σ1) e2
                          end
                      end
                  end
              end
          | _ => false
          end
      | infer_err _ =>
      match fuel with
      | 0 => false
      | S fuel' =>
          match e with
          | ELet m x T_hidden e1 e2 =>
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel' env Ω n R Σ e1 with
              | infer_err _ => false
              | infer_ok (T1, Σ1, R1, roots1) =>
                  ty_compatible_b Ω T1 T_hidden &&
                  non_function_value_ty_b T_hidden &&
                  (check_expr_root_shadow_store_safe_narrow_summary_fuel
                     fuel' env Ω n R Σ e1 ||
                   (capture_ref_free_ty_b env T1 &&
                    check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                      fuel' env Ω n R Σ e1)) &&
                  match root_env_lookup x R1 with
                  | Some _ => false
                  | None =>
                      roots_exclude_b x roots1 &&
                      root_env_excludes_b x R1 &&
                      match infer_core_env_state_fuel_roots_shadow_safe_checked
                              fuel' env Ω n
                              (root_env_add x roots1 R1)
                              (sctx_add x T_hidden m Σ1) e2 with
                      | infer_err _ => false
                      | infer_ok (T2, Σ2, R2, roots2) =>
                          sctx_check_ok env x T_hidden Σ2 &&
                          capture_ref_free_ty_b env T2 &&
                          root_env_excludes_b x (root_env_remove x R2) &&
                          check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env Ω n
                            (root_env_add x roots1 R1)
                            (sctx_add x T_hidden m Σ1) e2
                      end
                  end
              end
          | ELetInfer m x e1 e2 =>
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel' env Ω n R Σ e1 with
              | infer_err _ => false
              | infer_ok (T1, Σ1, R1, roots1) =>
                  non_function_value_ty_b T1 &&
                  (check_expr_root_shadow_store_safe_narrow_summary_fuel
                     fuel' env Ω n R Σ e1 ||
                   (capture_ref_free_ty_b env T1 &&
                    check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                      fuel' env Ω n R Σ e1)) &&
                  match root_env_lookup x R1 with
                  | Some _ => false
                  | None =>
                      roots_exclude_b x roots1 &&
                      root_env_excludes_b x R1 &&
                      match infer_core_env_state_fuel_roots_shadow_safe_checked
                              fuel' env Ω n
                              (root_env_add x roots1 R1)
                              (sctx_add x T1 m Σ1) e2 with
                      | infer_err _ => false
                      | infer_ok (T2, Σ2, R2, roots2) =>
                          sctx_check_ok env x T1 Σ2 &&
                          capture_ref_free_ty_b env T2 &&
                          root_env_excludes_b x (root_env_remove x R2) &&
                          check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env Ω n
                            (root_env_add x roots1 R1)
                            (sctx_add x T1 m Σ1) e2
                      end
                  end
              end
          | _ => false
          end
      end
      end
  end.

Definition check_expr_root_shadow_store_safe_narrow_summary_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Definition check_fn_root_shadow_generic_direct_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match generic_direct_call_target_expr (fn_body fdef) with
  | Some (fname, type_args, args, synthetic_body) =>
      store_safe_function_value_call_args_b env args &&
      match lookup_fn_b fname (env_fns env) with
      | None => false
      | Some callee =>
          Nat.eqb (Datatypes.length type_args) (fn_type_params callee) &&
          match check_struct_bounds
                  (global_env_with_local_bounds env (fn_bounds fdef))
                  (fn_bounds callee) type_args with
          | Some _ => false
          | None =>
              let callee_body_env :=
                global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args (fn_bounds callee)) in
              match infer_core_env_roots_shadow_safe callee_body_env
                        (fn_outlives callee)
                        (fn_lifetimes callee)
                        (initial_root_env_for_fn callee)
                        (subst_type_params_ctx type_args (fn_body_ctx callee))
                        (subst_type_params_expr type_args (fn_body callee)),
                    infer_env_roots_shadow_safe env callee
                      (initial_root_env_for_fn callee),
                    infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (T_callee, _, R_callee, roots_callee),
                infer_ok _,
                infer_ok (T_body, _, R_out, roots) =>
                  preservation_ready_expr_b
                    (subst_type_params_expr type_args (fn_body callee)) &&
                  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                    env callee type_args &&
                  ty_compatible_b (fn_outlives callee) T_callee
                    (subst_type_params_ty type_args (fn_ret callee)) &&
                  fn_params_roots_exclude_b
                    (apply_type_params type_args (fn_params callee))
                    roots_callee &&
                  fn_params_root_env_excludes_b
                    (apply_type_params type_args (fn_params callee))
                    R_callee &&
                  ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | _, _, _ => false
              end
          end
      end
  | None => false
  end.

Definition check_fn_root_shadow_captured_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_non_capturing_call_provenance_summary env fdef with
  | true => true
  | false =>
      (preservation_ready_expr_b (fn_body fdef) &&
       check_fn_root_shadow_captured_callee_provenance_summary env fdef) ||
      (match captured_call_target_expr (fn_body fdef) with
      | Some (fname, captures, args) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              match check_make_closure_captures_exact_sctx_with_env env
                      (fn_outlives fdef)
                      (sctx_of_ctx (fn_body_ctx fdef))
                      captures
                      (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  check_fn_root_shadow_captured_callee_provenance_summary
                    env callee &&
                  match infer_env_roots_shadow_safe env fdef
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (_, _, R_out, roots) =>
                      fn_params_roots_exclude_b (fn_params fdef) roots &&
                      fn_params_root_env_excludes_b (fn_params fdef) R_out
                  | infer_err _ => false
                  end
              end
          end
      | None => false
      end ||
      (match infer_core_env_roots_shadow_safe env
                  (fn_outlives fdef)
                  (fn_lifetimes fdef)
                  (initial_root_env_for_fn fdef)
                  (fn_body_ctx fdef)
                  (fn_body fdef),
                infer_env_roots_shadow_safe env fdef
                  (initial_root_env_for_fn fdef) with
          | infer_ok (T_body, _, R_out, roots), infer_ok _ =>
              check_expr_root_shadow_captured_call_provenance_summary
                env (fn_outlives fdef) (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef)
                (fn_body_ctx fdef) (fn_body fdef) &&
              ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
              fn_params_roots_exclude_b (fn_params fdef) roots &&
              fn_params_root_env_excludes_b (fn_params fdef) R_out
          | _, _ => false
          end) ||
      match local_captured_call_target_expr (fn_body fdef) with
      | Some (fname, captures, args, m, x, T, direct_body, let_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              negb (existsb (ident_eqb x)
                (ctx_names (params_ctx (fn_captures callee)))) &&
              match check_make_closure_captures_exact_sctx_with_env env
                      (fn_outlives fdef)
                      (sctx_of_ctx (fn_body_ctx fdef))
                      captures
                      (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  check_fn_root_shadow_captured_callee_provenance_summary
                    env callee &&
                  match infer_env_roots_shadow_safe env
                          (fn_with_body fdef direct_body)
                          (initial_root_env_for_fn fdef),
                        infer_env_roots_shadow_safe env
                          (fn_with_body fdef let_body)
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (_, _, R_direct, roots_direct),
                    infer_ok (_, _, _, _) =>
                      fn_params_roots_exclude_b (fn_params fdef)
                        roots_direct &&
                      fn_params_root_env_excludes_b (fn_params fdef)
                        R_direct
                  | _, _ => false
                  end
              end
          end
      | None => false
      end)
  end.

Definition check_fn_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  (check_fn_root_shadow_captured_call_provenance_summary env fdef ||
  (match direct_call_target_expr (fn_body fdef) with
   | Some (fname, args, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           match infer_core_env_roots_shadow_safe env
                     (fn_outlives callee)
                     (fn_lifetimes callee)
                     (initial_root_env_for_fn callee)
                     (fn_body_ctx callee)
                     (fn_body callee),
                 infer_env_roots_shadow_safe env callee
                   (initial_root_env_for_fn callee),
                 infer_env_roots_shadow_safe env
                   (fn_with_body fdef synthetic_body)
                   (initial_root_env_for_fn fdef) with
           | infer_ok (T_callee, _, R_callee, roots_callee),
             infer_ok _,
             infer_ok (T_body, _, R_out, roots) =>
               check_expr_root_shadow_store_safe_narrow_summary
                 env (fn_outlives callee) (fn_lifetimes callee)
                 (initial_root_env_for_fn callee)
                 (fn_body_ctx callee) (fn_body callee) &&
               ty_compatible_b (fn_outlives callee) T_callee
                 (fn_ret callee) &&
               fn_params_roots_exclude_b (fn_params callee) roots_callee &&
               fn_params_root_env_excludes_b (fn_params callee) R_callee &&
               ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
               fn_params_roots_exclude_b (fn_params fdef) roots &&
               fn_params_root_env_excludes_b (fn_params fdef) R_out
           | _, _, _ => false
           end
       end
   | None => false
   end) ||
  check_fn_root_shadow_generic_direct_store_safe_summary env fdef) ||
  (match let_bound_generic_direct_call_target_expr (fn_body fdef) with
   | Some (fname, type_args, args, T_hidden, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           Nat.eqb (Datatypes.length type_args) (fn_type_params callee) &&
           match check_struct_bounds
                   (global_env_with_local_bounds env (fn_bounds fdef))
                   (fn_bounds callee) type_args with
           | Some _ => false
           | None =>
               let callee_body_env :=
                 global_env_with_local_bounds env
                   (subst_type_params_trait_bounds type_args (fn_bounds callee)) in
               match infer_core_env_roots_shadow_safe callee_body_env
                         (fn_outlives callee)
                         (fn_lifetimes callee)
                         (initial_root_env_for_fn callee)
                         (subst_type_params_ctx type_args (fn_body_ctx callee))
                         (subst_type_params_expr type_args (fn_body callee)),
                     infer_env_roots_shadow_safe env callee
                       (initial_root_env_for_fn callee),
                     infer_env_roots_shadow_safe env
                       (fn_with_body fdef synthetic_body)
                       (initial_root_env_for_fn fdef) with
               | infer_ok (T_callee, _, R_callee, roots_callee),
                 infer_ok _,
                 infer_ok (T_body, _, R_out, roots) =>
                   check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                     env callee type_args &&
                   ty_compatible_b (fn_outlives callee) T_callee
                     (subst_type_params_ty type_args (fn_ret callee)) &&
                   fn_params_roots_exclude_b
                     (apply_type_params type_args (fn_params callee))
                     roots_callee &&
                   fn_params_root_env_excludes_b
                     (apply_type_params type_args (fn_params callee))
                     R_callee &&
                   ty_compatible_b (fn_outlives fdef) T_hidden (fn_ret fdef) &&
                   fn_params_roots_exclude_b (fn_params fdef) roots &&
                   fn_params_root_env_excludes_b (fn_params fdef) R_out
               | _, _, _ => false
               end
           end
       end
   | None => false
   end) ||
  (match if_literal_generic_direct_call_target_expr (fn_body fdef) with
   | Some (b, fname_then, type_args_then, args_then,
       fname_else, type_args_else, args_else, synthetic_body) =>
       store_safe_function_value_call_args_b env args_then &&
       store_safe_function_value_call_args_b env args_else &&
       match lookup_fn_b fname_then (env_fns env),
             lookup_fn_b fname_else (env_fns env) with
       | Some callee_then, Some callee_else =>
           Nat.eqb (Datatypes.length type_args_then)
             (fn_type_params callee_then) &&
           Nat.eqb (Datatypes.length type_args_else)
             (fn_type_params callee_else) &&
           match check_struct_bounds
                   (global_env_with_local_bounds env (fn_bounds fdef))
                   (fn_bounds callee_then) type_args_then,
                 check_struct_bounds
                   (global_env_with_local_bounds env (fn_bounds fdef))
                   (fn_bounds callee_else) type_args_else with
           | None, None =>
               match infer_core_env_roots_shadow_safe env
                         (fn_outlives callee_then)
                         (fn_lifetimes callee_then)
                         (initial_root_env_for_fn callee_then)
                         (subst_type_params_ctx type_args_then
                           (fn_body_ctx callee_then))
                         (subst_type_params_expr type_args_then
                           (fn_body callee_then)),
                     infer_env_roots_shadow_safe env callee_then
                       (initial_root_env_for_fn callee_then),
                     infer_core_env_roots_shadow_safe env
                         (fn_outlives callee_else)
                         (fn_lifetimes callee_else)
                         (initial_root_env_for_fn callee_else)
                         (subst_type_params_ctx type_args_else
                           (fn_body_ctx callee_else))
                         (subst_type_params_expr type_args_else
                           (fn_body callee_else)),
                     infer_env_roots_shadow_safe env callee_else
                       (initial_root_env_for_fn callee_else),
                     infer_env_roots_shadow_safe env
                       (fn_with_body fdef synthetic_body)
                       (initial_root_env_for_fn fdef) with
               | infer_ok (T_then, _, R_then, roots_then),
                 infer_ok _,
                 infer_ok (T_else, _, R_else, roots_else),
                 infer_ok _,
                 infer_ok (T_body, _, R_out, roots) =>
                   check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                     env callee_then type_args_then &&
                   ty_compatible_b (fn_outlives callee_then) T_then
                     (subst_type_params_ty type_args_then
                       (fn_ret callee_then)) &&
                   fn_params_roots_exclude_b
                     (apply_type_params type_args_then (fn_params callee_then))
                     roots_then &&
                   fn_params_root_env_excludes_b
                     (apply_type_params type_args_then (fn_params callee_then))
                     R_then &&
                   check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                     env callee_else type_args_else &&
                   ty_compatible_b (fn_outlives callee_else) T_else
                     (subst_type_params_ty type_args_else
                       (fn_ret callee_else)) &&
                   fn_params_roots_exclude_b
                     (apply_type_params type_args_else (fn_params callee_else))
                     roots_else &&
                   fn_params_root_env_excludes_b
                     (apply_type_params type_args_else (fn_params callee_else))
                     R_else &&
                   ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
                   fn_params_roots_exclude_b (fn_params fdef) roots &&
                   fn_params_root_env_excludes_b (fn_params fdef) R_out
               | _, _, _, _, _ => false
               end
           | _, _ => false
           end
       | _, _ => false
       end
   | None => false
   end) ||
  (match local_fn_value_call_target_expr_with_binder (fn_body fdef) with
   | Some (x, fname, args, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       negb (ident_in_b x (args_free_vars_checker args)) &&
       negb (ident_in_b x (args_local_store_names args)) &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           check_fn_root_shadow_generic_direct_store_safe_summary env callee &&
           match infer_env_roots_shadow_safe env
                   (fn_with_body fdef synthetic_body)
                   (initial_root_env_for_fn fdef) with
           | infer_ok (T_body, _, R_out, roots) =>
               ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
               fn_params_roots_exclude_b (fn_params fdef) roots &&
               fn_params_root_env_excludes_b (fn_params fdef) R_out
           | infer_err _ => false
           end
       end
   | None => false
   end) ||
  match infer_core_env_roots_shadow_safe_checked env
              (fn_outlives fdef)
              (fn_lifetimes fdef)
              (initial_root_env_for_fn fdef)
              (fn_body_ctx fdef)
              (fn_body fdef),
            infer_env_roots_shadow_safe_checked env fdef
              (initial_root_env_for_fn fdef) with
  | infer_ok (T_body, _, R_out, roots), infer_ok _ =>
      check_expr_root_shadow_store_safe_narrow_summary_checked
        env (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (fn_body_ctx fdef) (fn_body fdef) &&
      ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | _, _ => false
  end.

Definition check_env_root_shadow_captured_call_store_safe_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_captured_call_store_safe_summary env)
    (env_fns env).

Definition check_env_root_shadow_direct_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_direct_call_provenance_summary env)
    (env_fns env).

Definition check_env_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_non_capturing_call_provenance_summary env)
    (env_fns env).

Definition check_env_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_captured_call_provenance_summary env)
    (env_fns env).

Definition check_fn_ordinary_safety_gate
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_provenance_summary env fdef.

Definition check_program_env (env : global_env) : bool :=
  forallb (fun f =>
    match infer_full_env env f with
    | infer_ok _ => check_fn_ordinary_safety_gate env f
    | infer_err _ => false
    end) (env_fns env).

Definition check_program_env_alpha (env : global_env) : bool :=
  global_names_unique_b (alpha_normalize_global_env env) &&
  check_program_env (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated (env : global_env) : bool :=
  check_program_env_alpha env.

Definition check_program_env_alpha_elab (env : global_env) : bool :=
  global_names_unique_b (alpha_normalize_global_env env) &&
  match infer_program_env_alpha_elab env with
  | infer_ok env' => check_program_env env'
  | infer_err _ => false
  end.

Definition check_env_preservation_ready (env : global_env) : bool :=
  forallb (fun fdef => preservation_ready_expr_b (fn_body fdef))
    (env_fns env).

Definition check_program_env_alpha_validated_root_shadow (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_summary (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_provenance_summary (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_direct_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_non_capturing_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_captured_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  top_level_names_unique_b (alpha_normalize_global_env env) &&
  match infer_program_env_alpha_elab env with
  | infer_ok env' =>
      check_env_root_shadow_captured_call_provenance_summary env'
  | infer_err _ => false
  end.

Definition check_program_env_alpha_validated_root_shadow_provenance
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  (check_env_root_shadow_provenance_summary
     (alpha_normalize_global_env env) &&
   check_env_preservation_ready (alpha_normalize_global_env env)).

Definition infer_fn_env_end2end (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let R0 := initial_root_env_for_params (fn_params f ++ fn_captures f) in
  match infer_full_env_roots_checked env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      if check_fn_root_shadow_captured_call_store_safe_summary env f
      then infer_ok res
      else infer_err ErrEndToEndSafetyGateFailed
  end.

Fixpoint infer_fns_env_end2end (env : global_env) (fns : list fn_def)
    : infer_result unit :=
  match fns with
  | [] => infer_ok tt
  | f :: rest =>
      match infer_fn_env_end2end env f with
      | infer_err err => infer_err (ErrInFunction (fn_name f) err)
      | infer_ok _ => infer_fns_env_end2end env rest
      end
  end.

Definition infer_program_env_end2end (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  if global_names_unique_b env_alpha then
    match infer_program_env_alpha_elab env with
    | infer_err err => infer_err err
    | infer_ok env_elab =>
        match infer_fns_env_end2end env_elab (env_fns env_elab) with
        | infer_err err => infer_err err
        | infer_ok _ => infer_ok env_elab
        end
    end
  else infer_err ErrGlobalNamesNotUnique.

Definition check_program_env_end2end (env : global_env) : bool :=
  match infer_program_env_end2end env with
  | infer_ok _ => true
  | infer_err _ => false
  end.

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

(* ------------------------------------------------------------------ *)
(* Direct variant (no alpha renaming) — for differential testing only   *)
(* ------------------------------------------------------------------ *)

(* infer_direct skips alpha_rename_for_infer and calls infer_core directly.
   If the parser's de Bruijn indexing is correct, infer_direct fenv f and
   infer fenv f should always agree.  Run both at development time to
   validate that alpha renaming is indeed a no-op. *)
Definition infer_direct (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core fenv Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_b (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

(* ------------------------------------------------------------------ *)
(* Surface closure elaboration                                          *)
(* ------------------------------------------------------------------ *)

Inductive raw_expr : Type :=
| RawUnit : raw_expr
| RawLit : literal -> raw_expr
| RawVar : ident -> raw_expr
| RawFn : ident -> raw_expr
| RawPlace : place -> raw_expr
| RawLet : mutability -> ident -> Ty -> raw_expr -> raw_expr -> raw_expr
| RawLetInfer : mutability -> ident -> raw_expr -> raw_expr -> raw_expr
| RawCall : ident -> list raw_expr -> raw_expr
| RawCallGeneric : ident -> list Ty -> list raw_expr -> raw_expr
| RawCallExpr : raw_expr -> list raw_expr -> raw_expr
| RawStruct : string -> list lifetime -> list Ty -> list (string * raw_expr) -> raw_expr
| RawEnum : string -> string -> list lifetime -> list Ty -> list raw_expr -> raw_expr
| RawMatch : raw_expr -> list (string * list ident * raw_expr) -> raw_expr
| RawReplace : place -> raw_expr -> raw_expr
| RawAssign : place -> raw_expr -> raw_expr
| RawBorrow : ref_kind -> place -> raw_expr
| RawDeref : raw_expr -> raw_expr
| RawDrop : raw_expr -> raw_expr
| RawIf : raw_expr -> raw_expr -> raw_expr -> raw_expr
| RawClosure : list ident -> list param -> Ty -> raw_expr -> raw_expr
| RawCore : expr -> raw_expr.

Record raw_fn_def : Type := MkRawFnDef {
  raw_fn_name      : ident;
  raw_fn_lifetimes : nat;
  raw_fn_outlives  : outlives_ctx;
  raw_fn_params    : list param;
  raw_fn_ret       : Ty;
  raw_fn_body      : raw_expr;
  raw_fn_type_params : nat;
  raw_fn_bounds    : list trait_bound
}.

Definition fn_stub_of_raw (f : raw_fn_def) : fn_def :=
  MkFnDef (raw_fn_name f) (raw_fn_lifetimes f) (raw_fn_outlives f)
    [] (raw_fn_params f) (raw_fn_ret f) EUnit
    (raw_fn_type_params f) (raw_fn_bounds f).

Definition append_env_fns (env : global_env) (fns : list fn_def) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    (env_local_bounds env) (env_fns env ++ fns).

Fixpoint closure_elab_suffix (idx : nat) : string :=
  match idx with
  | O => EmptyString
  | S idx' => String.append "_"%string (closure_elab_suffix idx')
  end.

Definition closure_elab_name (idx : nat) : ident :=
  (String.append "__facet_closure"%string (closure_elab_suffix idx), 0).

Definition generic_fn_value_wrapper_name (idx : nat) : ident :=
  (String.append "__facet_generic_fn_value"%string (closure_elab_suffix idx), 0).

Fixpoint wrapper_params_from_tys_from
    (idx : nat) (tys : list Ty) : list param :=
  match tys with
  | [] => []
  | T :: rest =>
      MkParam MImmutable ("__facet_generic_arg"%string, idx) T ::
      wrapper_params_from_tys_from (S idx) rest
  end.

Definition wrapper_params_from_tys (tys : list Ty) : list param :=
  wrapper_params_from_tys_from 0 tys.

Fixpoint expr_vars_of_params (ps : list param) : list expr :=
  match ps with
  | [] => []
  | p :: rest => EVar (param_name p) :: expr_vars_of_params rest
  end.


Definition infer_fn_value_type_args_expected
    (fdef : fn_def) (expected : option Ty) : option (list Ty * list Ty * Ty) :=
  match expected with
  | Some (MkTy _ (TFn param_tys ret)) =>
      match infer_call_type_args_expected fdef param_tys (Some ret) with
      | Some type_args => Some (type_args, param_tys, ret)
      | None => None
      end
  | _ => None
  end.

Definition auto_drop_ret_name (idx : nat) : ident :=
  ("__facet_auto_drop_ret"%string, idx).

Definition auto_drop_tmp_name (idx : nat) : ident :=
  ("__facet_auto_drop"%string, idx).

Fixpoint place_of_path_from (base : place) (p : field_path) : place :=
  match p with
  | [] => base
  | field :: rest => place_of_path_from (PField base field) rest
  end.

Definition place_of_field_path (x : ident) (p : field_path) : place :=
  place_of_path_from (PVar x) p.

Fixpoint wrap_auto_drop_expr
    (x : ident) (paths : list field_path) (ret : expr) (next : nat)
    : expr * nat :=
  match paths with
  | [] => (ret, next)
  | path :: rest =>
      let tmp := auto_drop_tmp_name next in
      let '(tail, next') := wrap_auto_drop_expr x rest ret (S next) in
      (ELet MImmutable tmp (MkTy UUnrestricted TUnits)
        (EDrop (EPlace (place_of_field_path x path))) tail, next')
  end.

Definition wrap_let_body_auto_drops
    (env : global_env) (x : ident) (T : Ty) (Σ_body : sctx)
    (body_ty : Ty) (body : expr) (next : nat) : expr * nat :=
  match auto_drop_live_paths env x T Σ_body with
  | [] => (body, next)
  | paths =>
      let ret := auto_drop_ret_name next in
      let '(tail, next') := wrap_auto_drop_expr x paths (EVar ret) (S next) in
      (ELet MImmutable ret body_ty body tail, next')
  end.

Definition closure_elab_capture_param
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx) (x : ident)
    : infer_result param :=
  match sctx_lookup x Σ with
  | None => infer_err (ErrUnknownVar x)
  | Some (T, st) =>
      if negb (binding_available_b st [])
      then infer_err (ErrAlreadyConsumed x)
      else
      match sctx_lookup_mut x Σ with
      | Some MImmutable =>
          if usage_eqb (ty_usage T) UUnrestricted
          then
            if capture_ref_free_ty_b env T
            then infer_ok (MkParam MImmutable x T)
            else
              match T with
              | MkTy _ (TRef _ RShared _) => infer_ok (MkParam MImmutable x T)
              | _ => infer_err (ErrNotAReference (ty_core T))
              end
          else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
      | Some MMutable => infer_err (ErrNotMutable x)
      | None => infer_err (ErrUnknownVar x)
      end
  end.

Fixpoint closure_elab_capture_params
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx) (captures : list ident)
    : infer_result (list param) :=
  match captures with
  | [] => infer_ok []
  | x :: xs =>
      match closure_elab_capture_param env Ω Σ x with
      | infer_err err => infer_err err
      | infer_ok p =>
          match closure_elab_capture_params env Ω Σ xs with
          | infer_err err => infer_err err
          | infer_ok ps => infer_ok (p :: ps)
          end
      end
  end.

Definition infer_elaborated_expr_state
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (e : expr) : infer_result sctx :=
  match infer_core_env_state_fuel fuel env Ω n Σ e with
  | infer_err err => infer_err err
  | infer_ok (_, Σ') => infer_ok Σ'
  end.

Fixpoint elaborate_raw_expr_fuel
    (fuel : nat) (expected : option Ty)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (next : nat) (e : raw_expr)
    : infer_result (expr * sctx * list fn_def * nat) :=
  let finish env' e' extras next' :=
    match infer_elaborated_expr_state fuel env' Ω n Σ e' with
    | infer_err err => infer_err err
    | infer_ok Σ' => infer_ok (e', Σ', extras, next')
    end in
  let fix go_args fuel0 env0 Σ0 next0 args :=
    match args with
    | [] => infer_ok ([], Σ0, [], next0)
    | a :: rest =>
        match elaborate_raw_expr_fuel fuel0 None env0 Ω n Σ0 next0 a with
        | infer_err err => infer_err err
        | infer_ok (a', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_args fuel0 env1 Σ1 next1 rest with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok (a' :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    end in
  let fix go_args_expected fuel0 env0 Σ0 next0 args params :=
    match args, params with
    | [], [] => infer_ok ([], Σ0, [], next0)
    | a :: rest, p :: ps =>
        match elaborate_raw_expr_fuel fuel0 (Some (param_ty p)) env0 Ω n Σ0 next0 a with
        | infer_err err => infer_err err
        | infer_ok (a', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_args_expected fuel0 env1 Σ1 next1 rest ps with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok (a' :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    | _, _ => infer_err ErrArityMismatch
    end in
  let fix infer_arg_tys_state fuel0 env0 Σ0 args :=
    match args with
    | [] => infer_ok ([], Σ0)
    | a :: rest =>
        match infer_core_env_state_fuel fuel0 env0 Ω n Σ0 a with
        | infer_err err => infer_err err
        | infer_ok (T, Σ1) =>
            match infer_arg_tys_state fuel0 env0 Σ1 rest with
            | infer_err err => infer_err err
            | infer_ok (Ts, Σ2) => infer_ok (T :: Ts, Σ2)
            end
        end
    end in
  let fix go_fields fuel0 env0 Σ0 next0 fields :=
    match fields with
    | [] => infer_ok ([], Σ0, [], next0)
    | (fname, fe) :: rest =>
        match elaborate_raw_expr_fuel fuel0 None env0 Ω n Σ0 next0 fe with
        | infer_err err => infer_err err
        | infer_ok (fe', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_fields fuel0 env1 Σ1 next1 rest with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok ((fname, fe') :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    end in
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
      match e with
      | RawUnit => finish env EUnit [] next
      | RawLit lit => finish env (ELit lit) [] next
      | RawVar x => finish env (EVar x) [] next
      | RawFn fname =>
          match lookup_fn_b fname (env_fns env) with
          | None => finish env (EFn fname) [] next
          | Some fdef =>
              if Nat.eqb (fn_type_params fdef) 0
              then finish env (EFn fname) [] next
              else
                if negb (no_captures_b fdef)
                then infer_err ErrNotImplemented
                else
                  match expected with
                  | Some T_expected =>
                      if ty_compatible_b Ω (fn_value_ty fdef) T_expected
                      then finish env (EFn fname) [] next
                      else if negb (Nat.eqb (fn_lifetimes fdef) 0)
                      then infer_err ErrTypeArgInferenceFailed
                      else
                        match infer_fn_value_type_args_expected fdef expected with
                        | None => infer_err ErrTypeArgInferenceFailed
                        | Some (type_args, param_tys, ret) =>
                            match check_struct_bounds env (fn_bounds fdef) type_args with
                            | Some err => infer_err err
                            | None =>
                                let wrapper_name := generic_fn_value_wrapper_name next in
                                let wrapper_params := wrapper_params_from_tys param_tys in
                                let wrapper_body :=
                                  ECallGeneric fname type_args
                                    (expr_vars_of_params wrapper_params) in
                                let wrapper :=
                                  MkFnDef wrapper_name 0 [] [] wrapper_params ret
                                    wrapper_body 0 [] in
                                let env' := append_env_fns env [wrapper] in
                                finish env' (EFn wrapper_name) [wrapper] (S next)
                            end
                        end
                  | None => infer_err ErrTypeArgInferenceFailed
                  end
          end
      | RawPlace p => finish env (EPlace p) [] next
      | RawCore ecore => finish env ecore [] next
      | RawBorrow rk p => finish env (EBorrow rk p) [] next
      | RawLet m x T e1 e2 =>
          match elaborate_raw_expr_fuel fuel' (Some T) env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match elaborate_raw_expr_fuel fuel' expected env1 Ω n
                      (sctx_add x T m Σ1) next1 e2 with
              | infer_err err => infer_err err
              | infer_ok (e2', Σ2, extras2, next2) =>
                  let extras := extras1 ++ extras2 in
                  let env2 := append_env_fns env extras in
                  match infer_core_env_state_fuel fuel' env2 Ω n
                          (sctx_add x T m Σ1) e2' with
                  | infer_err err => infer_err err
                  | infer_ok (T2, _) =>
                      let '(e2'', next3) :=
                        wrap_let_body_auto_drops env2 x T Σ2 T2 e2' next2 in
                      let e' := ELet m x T e1' e2'' in
                      finish env2 e' extras next3
                  end
              end
          end
      | RawLetInfer m x e1 e2 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              match infer_core_env_state_fuel fuel' (append_env_fns env extras1)
                      Ω n Σ e1' with
              | infer_err err => infer_err err
              | infer_ok (T1, _) =>
                  let env1 := append_env_fns env extras1 in
                  match elaborate_raw_expr_fuel fuel' expected env1 Ω n
                          (sctx_add x T1 m Σ1) next1 e2 with
                  | infer_err err => infer_err err
                  | infer_ok (e2', Σ2, extras2, next2) =>
                      let extras := extras1 ++ extras2 in
                      let env2 := append_env_fns env extras in
                      match infer_core_env_state_fuel fuel' env2 Ω n
                              (sctx_add x T1 m Σ1) e2' with
                      | infer_err err => infer_err err
                      | infer_ok (T2, _) =>
                          let '(e2'', next3) :=
                            wrap_let_body_auto_drops env2 x T1 Σ2 T2 e2' next2 in
                          let e' := ELet m x T1 e1' e2'' in
                          finish env2 e' extras next3
                      end
                  end
              end
          end
      | RawCall fname args =>
          let infer_plain :=
            match go_args fuel' env Σ next args with
            | infer_err err => infer_err err
            | infer_ok (args', _, extras, next') =>
                let env' := append_env_fns env extras in
                match lookup_fn_b fname (env_fns env') with
                | None => finish env' (ECall fname args') extras next'
                | Some fdef =>
                    if Nat.eqb (fn_type_params fdef) 0
                    then finish env' (ECall fname args') extras next'
                    else
                      match infer_arg_tys_state fuel' env' Σ args' with
                      | infer_err err => infer_err err
                      | infer_ok (arg_tys, _) =>
                          match infer_call_type_args_expected fdef arg_tys expected with
                          | None => infer_err ErrTypeArgInferenceFailed
                          | Some type_args =>
                              match check_struct_bounds env' (fn_bounds fdef) type_args with
                              | Some err => infer_err err
                              | None =>
                                  match specialize_simple_generic_wrapper_call env' fname type_args args' with
                                  | Some (target, target_type_args, target_args) =>
                                      finish env'
                                        (ECallGeneric target target_type_args target_args)
                                        extras next'
                                  | None =>
                                      finish env' (ECallGeneric fname type_args args')
                                        extras next'
                                  end
                              end
                          end
                      end
                end
            end in
          match lookup_fn_b fname (env_fns env) with
          | Some fdef =>
	              if Nat.eqb (fn_type_params fdef) 0
              then
                match go_args_expected fuel' env Σ next args (fn_params fdef) with
                | infer_err _ => infer_plain
                | infer_ok (args', _, extras, next') =>
                    finish (append_env_fns env extras)
                      (ECall fname args') extras next'
                end
              else infer_plain
          | None => infer_plain
          end
      | RawCallGeneric fname type_args args =>
          match go_args fuel' env Σ next args with
          | infer_err err => infer_err err
          | infer_ok (args', _, extras, next') =>
              let env' := append_env_fns env extras in
              match specialize_simple_generic_wrapper_call env' fname type_args args' with
              | Some (target, target_type_args, target_args) =>
                  finish env' (ECallGeneric target target_type_args target_args)
                    extras next'
              | None =>
                  finish env' (ECallGeneric fname type_args args')
                    extras next'
              end
          end
      | RawCallExpr callee args =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next callee with
          | infer_err err => infer_err err
          | infer_ok (callee', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match go_args fuel' env1 Σ1 next1 args with
              | infer_err err => infer_err err
              | infer_ok (args', _, extras2, next2) =>
                  let extras := extras1 ++ extras2 in
                  finish (append_env_fns env extras)
                    (ECallExpr callee' args') extras next2
              end
          end
      | RawStruct sname lts tys fields =>
          match go_fields fuel' env Σ next fields with
          | infer_err err => infer_err err
          | infer_ok (fields', _, extras, next') =>
              finish (append_env_fns env extras)
                (EStruct sname lts tys fields') extras next'
          end
      | RawEnum enum_name variant_name lts tys payloads =>
          match go_args fuel' env Σ next payloads with
          | infer_err err => infer_err err
          | infer_ok (payloads', _, extras, next') =>
              finish (append_env_fns env extras)
                (EEnum enum_name variant_name lts tys payloads') extras next'
          end
      | RawMatch scrut branches =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next scrut with
          | infer_err err => infer_err err
          | infer_ok (scrut', Σ1, extras_scrut, next1) =>
              let env1 := append_env_fns env extras_scrut in
              match infer_core_env_state_fuel fuel' env1 Ω n Σ scrut' with
              | infer_err err => infer_err err
              | infer_ok (T_scrut, _) =>
                  match ty_core T_scrut with
                  | TEnum enum_name lts args =>
                      match lookup_enum enum_name env1 with
                      | None => infer_err (ErrEnumNotFound enum_name)
                      | Some edef =>
                          let fix go_branches env0 next0 branches0 :=
                            match branches0 with
                            | [] => infer_ok ([], [], next0)
                            | (variant_name, binders, e_branch) :: rest =>
                                match lookup_enum_variant variant_name (enum_variants edef) with
	                                | None => infer_err (ErrVariantNotFound variant_name)
	                                | Some vdef =>
	                                    match match_payload_params binders lts args vdef with
                                    | infer_err err => infer_err err
                                    | infer_ok ps =>
                                        if params_names_nodup_b ps &&
                                           ctx_lookup_params_none_b ps Σ1
                                        then
                                        match elaborate_raw_expr_fuel fuel' expected env0 Ω n
                                                (sctx_add_params ps Σ1) next0 e_branch with
                                        | infer_err err => infer_err err
                                        | infer_ok (e_branch', _, extras_branch, next_branch) =>
                                            let env_branch := append_env_fns env0 extras_branch in
                                            match go_branches env_branch next_branch rest with
                                            | infer_err err => infer_err err
                                            | infer_ok (rest', extras_rest, next_rest) =>
                                                infer_ok ((variant_name, binders, e_branch') :: rest',
                                                          extras_branch ++ extras_rest, next_rest)
                                            end
                                        end
	                                        else infer_err ErrContextCheckFailed
	                                    end
	                                end
                            end
                          in
                          match go_branches env1 next1 branches with
                          | infer_err err => infer_err err
                          | infer_ok (branches', extras_branches, next') =>
                              let extras := extras_scrut ++ extras_branches in
                              let env' := append_env_fns env extras in
                              match infer_core_env_state_fuel_elab fuel env' Ω n Σ
                                      (EMatch scrut' branches') with
                              | infer_err err => infer_err err
                              | infer_ok (_, Σ', e_match') =>
                                  infer_ok (e_match', Σ', extras, next')
                              end
                          end
                      end
                  | c => infer_err (ErrNotAnEnum c)
                  end
              end
          end
      | RawReplace p e1 =>
          let expected_rhs :=
            match infer_place_sctx env Σ p with
            | infer_ok T => Some T
            | infer_err _ => None
            end in
          match elaborate_raw_expr_fuel fuel' expected_rhs env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EReplace p e1') extras next'
          end
      | RawAssign p e1 =>
          let expected_rhs :=
            match infer_place_sctx env Σ p with
            | infer_ok T => Some T
            | infer_err _ => None
            end in
          match elaborate_raw_expr_fuel fuel' expected_rhs env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EAssign p e1') extras next'
          end
      | RawDeref e1 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EDeref e1') extras next'
          end
      | RawDrop e1 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EDrop e1') extras next'
          end
      | RawIf e1 e2 e3 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match elaborate_raw_expr_fuel fuel' expected env1 Ω n Σ1 next1 e2 with
              | infer_err err => infer_err err
              | infer_ok (e2', _, extras2, next2) =>
                  let env2 := append_env_fns env1 extras2 in
                  match elaborate_raw_expr_fuel fuel' expected env2 Ω n Σ1 next2 e3 with
                  | infer_err err => infer_err err
                  | infer_ok (e3', _, extras3, next3) =>
                      let extras := extras1 ++ extras2 ++ extras3 in
                      finish (append_env_fns env extras)
                        (EIf e1' e2' e3') extras next3
                  end
              end
          end
      | RawClosure captures params ret body =>
          match closure_elab_capture_params env Ω Σ captures with
          | infer_err err => infer_err err
          | infer_ok cap_params =>
              let fname := closure_elab_name next in
              let body_ctx := sctx_of_ctx (params_ctx (cap_params ++ params)) in
              match elaborate_raw_expr_fuel fuel' (Some ret) env Ω n body_ctx (S next) body with
              | infer_err err => infer_err err
              | infer_ok (body', _, body_extras, next') =>
                  let fdef := MkFnDef fname n Ω cap_params params ret body' 0 [] in
                  let env_with_closure := append_env_fns env (body_extras ++ [fdef]) in
                  match infer_full_env env_with_closure fdef with
                  | infer_err err => infer_err err
                  | infer_ok _ =>
                      finish env_with_closure (EMakeClosure fname captures)
                        (body_extras ++ [fdef]) next'
                  end
              end
          end
      end
  end.

Definition elaborate_raw_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx)
    (e : raw_expr) : infer_result (expr * list fn_def) :=
  match elaborate_raw_expr_fuel 10000 None env Ω n Σ 0 e with
  | infer_err err => infer_err err
  | infer_ok (e', _, extras, _) => infer_ok (e', extras)
  end.

Definition raw_fn_body_ctx (f : raw_fn_def) : ctx :=
  params_ctx (raw_fn_params f).

Fixpoint elaborate_raw_fns_fuel
    (fuel : nat) (base_env : global_env) (done : list fn_def)
    (next : nat) (fs : list raw_fn_def)
    : infer_result (list fn_def * nat) :=
  match fs with
  | [] => infer_ok ([], next)
  | f :: rest =>
      let env0 := append_env_fns base_env done in
      let body_env := global_env_with_local_bounds env0 (raw_fn_bounds f) in
      match elaborate_raw_expr_fuel fuel (Some (raw_fn_ret f))
              body_env (raw_fn_outlives f)
              (raw_fn_lifetimes f) (sctx_of_ctx (raw_fn_body_ctx f))
              next (raw_fn_body f) with
      | infer_err err => infer_err err
      | infer_ok (body', _, extras, next1) =>
          let f' := MkFnDef (raw_fn_name f) (raw_fn_lifetimes f)
                      (raw_fn_outlives f) [] (raw_fn_params f)
                      (raw_fn_ret f) body'
                      (raw_fn_type_params f) (raw_fn_bounds f) in
          match elaborate_raw_fns_fuel fuel base_env (done ++ extras ++ [f'])
                  next1 rest with
          | infer_err err => infer_err err
          | infer_ok (rest', next2) => infer_ok (extras ++ f' :: rest', next2)
          end
      end
  end.

Definition elaborate_raw_global_env (env : global_env) (fs : list raw_fn_def)
    : infer_result global_env :=
  let stubs := map fn_stub_of_raw fs in
  let base := MkGlobalEnv (env_structs env) (env_enums env)
    (env_traits env) (env_impls env)
    [] stubs in
  match elaborate_raw_fns_fuel 10000 base [] 0 fs with
  | infer_err err => infer_err err
  | infer_ok (fns, _) =>
      infer_ok (MkGlobalEnv (env_structs env) (env_enums env)
        (env_traits env) (env_impls env) [] fns)
  end.

(* ------------------------------------------------------------------ *)
(* OCaml extraction                                                      *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
Extraction "../fixtures/TypeChecker.ml"
  infer_core_env_roots infer_env_roots infer_full_env_roots
  infer_env infer_full_env check_program_env
  infer_core_env_elab infer_env_elab infer_full_env_elab
  infer_program_env_alpha_elab check_program_env_alpha_elab
  elaborate_raw_expr elaborate_raw_global_env
  alpha_normalize_global_env check_program_env_alpha
  check_program_env_alpha_validated
  preservation_ready_expr_b preservation_ready_args_b
  preservation_ready_fields_b
  provenance_ready_expr_b provenance_ready_args_b
  provenance_ready_fields_b
  infer_core_env_state_fuel_roots_shadow_safe
  infer_core_env_roots_shadow_safe infer_env_roots_shadow_safe
  check_fn_root_shadow_summary check_env_root_shadow_summary
  check_fn_root_shadow_provenance_summary
  check_env_root_shadow_provenance_summary
  direct_call_ready_expr_b
  check_fn_root_shadow_direct_call_provenance_summary
  check_env_root_shadow_direct_call_provenance_summary
  check_env_preservation_ready
  check_program_env_alpha_validated_root_shadow
  check_program_env_alpha_validated_root_shadow_provenance_summary
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
  check_program_env_alpha_validated_root_shadow_provenance
  infer_fn_env_end2end infer_program_env_end2end check_program_env_end2end.
