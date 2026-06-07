From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerProgram.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

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
  | EEnum _ _ _ _ _ payloads =>
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
  | EEnum _ _ _ _ _ payloads =>
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

