From Facet.TypeSystem Require Import Types Syntax TypingRules.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Decidable equality helpers                                            *)
(* ------------------------------------------------------------------ *)

Definition usage_eqb (u1 u2 : usage) : bool :=
  match u1, u2 with
  | ULinear,       ULinear       => true
  | UAffine,       UAffine       => true
  | UUnrestricted, UUnrestricted => true
  | _,             _             => false
  end.

(* usage_sub_bool u1 u2 = true iff u1 <: u2 (unrestricted <: affine <: linear) *)
Definition usage_sub_bool (u1 u2 : usage) : bool :=
  match u1, u2 with
  | UUnrestricted, _          => true
  | UAffine,       UAffine    => true
  | UAffine,       ULinear    => true
  | ULinear,       ULinear    => true
  | _,             _          => false
  end.

(* Compare cores; TFn/TRef are out of scope so we return false for them. *)
Definition ty_core_eqb (c1 c2 : TypeCore Ty) : bool :=
  match c1, c2 with
  | TUnits,    TUnits    => true
  | TIntegers, TIntegers => true
  | TFloats,   TFloats   => true
  | TBooleans, TBooleans => true
  | TNamed s1, TNamed s2 => String.eqb s1 s2
  | _,         _         => false
  end.

(* ------------------------------------------------------------------ *)
(* Decidable context operations                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lookup_b (x : ident) (Γ : ctx) : option (Ty * bool) :=
  match Γ with
  | []              => None
  | (n, T, b) :: t => if ident_eqb x n then Some (T, b)
                      else ctx_lookup_b x t
  end.

Fixpoint ctx_consume_b (x : ident) (Γ : ctx) : option ctx :=
  match Γ with
  | []              => None
  | (n, T, b) :: t =>
      if ident_eqb x n
      then Some ((n, T, true) :: t)
      else match ctx_consume_b x t with
           | None    => None
           | Some t' => Some ((n, T, b) :: t')
           end
  end.

Definition ctx_add_b (x : ident) (T : Ty) (Γ : ctx) : ctx :=
  (x, T, false) :: Γ.

Fixpoint ctx_remove_b (x : ident) (Γ : ctx) : ctx :=
  match Γ with
  | []              => []
  | (n, T, b) :: t =>
      if ident_eqb x n then t
      else (n, T, b) :: ctx_remove_b x t
  end.

(* Returns true iff x's usage constraint is satisfied after its scope:
   - linear: x must be consumed (found with consumed=true)
   - affine/unrestricted: always ok *)
Definition ctx_check_ok (x : ident) (T : Ty) (Γ : ctx) : bool :=
  match ty_usage T with
  | ULinear =>
      match ctx_lookup_b x Γ with
      | Some (_, true) => true
      | _              => false
      end
  | _ => true
  end.

(* ------------------------------------------------------------------ *)
(* Function environment lookup                                           *)
(* ------------------------------------------------------------------ *)

Fixpoint lookup_fn_b (name : ident) (fenv : list fn_def) : option fn_def :=
  match fenv with
  | []     => None
  | f :: t => if ident_eqb name (fn_name f) then Some f
              else lookup_fn_b name t
  end.

(* ------------------------------------------------------------------ *)
(* Alpha renaming                                                       *)
(* ------------------------------------------------------------------ *)

Definition rename_env : Type := list (ident * ident).

Fixpoint ident_in (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: ys => if ident_eqb x y then true else ident_in x ys
  end.

Fixpoint lookup_rename (x : ident) (ρ : rename_env) : ident :=
  match ρ with
  | [] => x
  | (old, fresh) :: ρ' =>
      if ident_eqb x old then fresh else lookup_rename x ρ'
  end.

Fixpoint max_ident_index (base : string) (used : list ident) : nat :=
  match used with
  | [] => O
  | (base0, n) :: used' =>
      if String.eqb base base0
      then Nat.max n (max_ident_index base used')
      else max_ident_index base used'
  end.

Definition fresh_ident (x : ident) (used : list ident) : ident :=
  (fst x, S (max_ident_index (fst x) used)).

Fixpoint ctx_names (Γ : ctx) : list ident :=
  match Γ with
  | [] => []
  | (x, _, _) :: Γ' => x :: ctx_names Γ'
  end.

Definition place_name (p : place) : ident :=
  match p with
  | PVar x => x
  end.

(* ------------------------------------------------------------------ *)
(* Checker result/error types                                            *)
(* ------------------------------------------------------------------ *)

Inductive infer_error : Type :=
  | ErrUnknownVar : ident -> infer_error
  | ErrAlreadyConsumed : ident -> infer_error
  | ErrTypeMismatch : TypeCore Ty -> TypeCore Ty -> infer_error
  | ErrUsageMismatch : usage -> usage -> infer_error
  | ErrFunctionNotFound : ident -> infer_error
  | ErrArityMismatch : infer_error
  | ErrContextCheckFailed : infer_error
  | ErrNotImplemented : infer_error.

Inductive infer_result (A : Type) : Type :=
  | infer_ok : A -> infer_result A
  | infer_err : infer_error -> infer_result A.

Arguments infer_ok {_} _.
Arguments infer_err {_} _.

Fixpoint free_vars_expr (e : expr) : list ident :=
  match e with
  | EUnit => []
  | ELit _ => []
  | EVar x => [x]
  | ELet _ x _ e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
  | ELetInfer _ x e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
  | ECall _ args =>
      let fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end
      in go args
  | EReplace p e_new => place_name p :: free_vars_expr e_new
  | EDrop e1 => free_vars_expr e1
  | EIf e1 e2 e3 => free_vars_expr e1 ++ free_vars_expr e2 ++ free_vars_expr e3
  end.

Fixpoint param_names (ps : list param) : list ident :=
  match ps with
  | [] => []
  | p :: ps' => param_name p :: param_names ps'
  end.

Definition rename_place (ρ : rename_env) (p : place) : place :=
  match p with
  | PVar x => PVar (lookup_rename x ρ)
  end.

Fixpoint alpha_rename_expr (ρ : rename_env) (used : list ident)
    (e : expr) : expr * list ident :=
  match e with
  | EUnit => (EUnit, used)
  | ELit l => (ELit l, used)
  | EVar x => (EVar (lookup_rename x ρ), used)
  | ECall fname args =>
      let fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end
      in
      let (args', used') := go used args in
      (ECall fname args', used')
  | EReplace p e_new =>
      let (e_new', used') := alpha_rename_expr ρ used e_new in
      (EReplace (rename_place ρ p) e_new', used')
  | EDrop e1 =>
      let (e1', used') := alpha_rename_expr ρ used e1 in
      (EDrop e1', used')
  | ELet m x T e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let used1' := x :: free_vars_expr e2 ++ used1 in
      let x' := fresh_ident x used1' in
      let used2 := x' :: used1' in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELet m x' T e1' e2', used3)
  | ELetInfer m x e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let used1' := x :: free_vars_expr e2 ++ used1 in
      let x' := fresh_ident x used1' in
      let used2 := x' :: used1' in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELetInfer m x' e1' e2', used3)
  | EIf e1 e2 e3 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let (e2', used2) := alpha_rename_expr ρ used1 e2 in
      let (e3', used3) := alpha_rename_expr ρ used2 e3 in
      (EIf e1' e2' e3', used3)
  end.

Fixpoint alpha_rename_params (ρ : rename_env) (used : list ident)
    (ps : list param) : list param * rename_env * list ident :=
  match ps with
  | [] => ([], ρ, used)
  | p :: ps' =>
      let x := param_name p in
      let x' := fresh_ident x used in
      let p' := MkParam (param_mutability p) x' (param_ty p) in
      let '(ps'', ρ', used') :=
        alpha_rename_params ((x, x') :: ρ) (x' :: used) ps' in
      (p' :: ps'', ρ', used')
  end.

Definition alpha_rename_fn_def (used : list ident)
    (f : fn_def) : fn_def * list ident :=
  let used0 := param_names (fn_params f) ++ free_vars_expr (fn_body f) ++ used in
  let '(params', ρ, used1) := alpha_rename_params [] used0 (fn_params f) in
  let (body', used2) := alpha_rename_expr ρ used1 (fn_body f) in
  (MkFnDef (fn_name f) params' (fn_ret f) body', used2).

Fixpoint alpha_rename_syntax_go (used : list ident) (s : Syntax)
    : Syntax * list ident :=
  match s with
  | [] => ([], used)
  | f :: fs =>
      let (f', used1) := alpha_rename_fn_def used f in
      let (fs', used2) := alpha_rename_syntax_go used1 fs in
      (f' :: fs', used2)
  end.

Definition alpha_rename_syntax (s : Syntax) : Syntax :=
  fst (alpha_rename_syntax_go [] s).

Definition alpha_rename_for_infer (Γ : ctx) (fenv : list fn_def)
    (e : expr) : list fn_def * expr :=
  let (fenv', used) :=
    alpha_rename_syntax_go (free_vars_expr e ++ ctx_names Γ) fenv in
  let (e', _) := alpha_rename_expr [] used e in
  (fenv', e').

(* ------------------------------------------------------------------ *)
(* Type inference                                                        *)
(*                                                                      *)
(* infer_core fenv Γ e = Some (T, Γ')                                   *)
(*   Returns the type T and the updated context Γ' after e is typed.      *)
(*   Returns infer_err on any type or usage error.                       *)
(*                                                                      *)
(* The ECall case uses an inline local fixpoint to process the argument  *)
(* list without requiring a mutual fixpoint (which complicates           *)
(* termination checking).                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_core (fenv : list fn_def) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match e with

  | EUnit =>
      infer_ok (MkTy UUnrestricted TUnits, Γ)

  | ELit (LInt _) =>
      infer_ok (MkTy UUnrestricted TIntegers, Γ)

  | ELit (LFloat _) =>
      infer_ok (MkTy UUnrestricted TFloats, Γ)

  | ELit (LBool _) =>
      infer_ok (MkTy UUnrestricted TBooleans, Γ)

  | EVar x =>
      match ctx_lookup_b x Γ with
      | None        => infer_err (ErrUnknownVar x)
      | Some (T, b) =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else if b
               then infer_err (ErrAlreadyConsumed x)
               else match ctx_consume_b x Γ with
                    | None    => infer_err (ErrUnknownVar x)
                    | Some Γ' => infer_ok (T, Γ')
                    end
      end

  | ELet m x T e1 e2 =>
      match infer_core fenv Γ e1 with
      | infer_err err          => infer_err err
      | infer_ok (T1, Γ1) =>
          if ty_core_eqb (ty_core T1) (ty_core T) then
            if usage_sub_bool (ty_usage T1) (ty_usage T) then
            match infer_core fenv (ctx_add_b x T Γ1) e2 with
            | infer_err err          => infer_err err
            | infer_ok (T2, Γ2) =>
                if ctx_check_ok x T Γ2
                then infer_ok (T2, ctx_remove_b x Γ2)
                else infer_err ErrContextCheckFailed
            end
            else infer_err (ErrUsageMismatch (ty_usage T1) (ty_usage T))
          else infer_err (ErrTypeMismatch (ty_core T1) (ty_core T))
      end

  | EDrop e1 =>
      match infer_core fenv Γ e1 with
      | infer_err err          => infer_err err
      | infer_ok (_, Γ') => infer_ok (MkTy UUnrestricted TUnits, Γ')
      end

  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None              => infer_err (ErrUnknownVar x)
      | Some (_, true)    => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match infer_core fenv Γ e_new with
          | infer_err err            => infer_err err
          | infer_ok (T_new, Γ') =>
              if ty_core_eqb (ty_core T_new) (ty_core T_x) then
                if usage_sub_bool (ty_usage T_new) (ty_usage T_x)
                then infer_ok (T_x, Γ')
                else infer_err (ErrUsageMismatch (ty_usage T_new) (ty_usage T_x))
              else infer_err (ErrTypeMismatch (ty_core T_new) (ty_core T_x))
          end
      end

  | ECall fname args =>
      match lookup_fn_b fname fenv with
      | None      => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          (* Process argument list with an inline fixpoint so that
             Rocq's termination checker sees the structural recursion
             clearly: each arg is a sub-term of the args field of ECall. *)
          let fix go (Γ0 : ctx) (as_ : list expr) (ps : list param)
              : infer_result ctx :=
            match as_, ps with
            | [],       []       => infer_ok Γ0
            | [],       _ :: _   => infer_err ErrArityMismatch
            | _ :: _,   []       => infer_err ErrArityMismatch
            | e' :: es, p :: ps' =>
                match infer_core fenv Γ0 e' with
                | infer_err err            => infer_err err
                | infer_ok (T_e, Γ1) =>
                    if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) then
                      if usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
                      then go Γ1 es ps'
                      else infer_err
                        (ErrUsageMismatch (ty_usage T_e) (ty_usage (param_ty p)))
                    else infer_err
                      (ErrTypeMismatch (ty_core T_e) (ty_core (param_ty p)))
                end
            end
          in
          match go Γ args (fn_params fdef) with
          | infer_err err => infer_err err
          | infer_ok Γ' => infer_ok (fn_ret fdef, Γ')
          end
      end

  | ELetInfer m x e1 e2 =>
      match infer_core fenv Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          match infer_core fenv (ctx_add_b x T1 Γ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Γ2) =>
              if ctx_check_ok x T1 Γ2
              then infer_ok (T2, ctx_remove_b x Γ2)
              else infer_err ErrContextCheckFailed
          end
      end

  | EIf e1 e2 e3 =>
      match infer_core fenv Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Γ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans then
            match infer_core fenv Γ1 e2 with
            | infer_err err => infer_err err
            | infer_ok (T2, Γ2) =>
                match infer_core fenv Γ1 e3 with
                | infer_err err => infer_err err
                | infer_ok (T3, Γ3) =>
                    if ty_core_eqb (ty_core T2) (ty_core T3) then
                      match ctx_merge Γ2 Γ3 with
                      | None    => infer_err ErrContextCheckFailed
                      | Some Γ4 =>
                          infer_ok (MkTy (usage_max (ty_usage T2) (ty_usage T3))
                                         (ty_core T2), Γ4)
                      end
                    else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                end
            end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end

  end.

Definition infer_body (fenv : list fn_def) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  let (fenv', e') := alpha_rename_for_infer Γ fenv e in
  infer_core fenv' Γ e'.

(* ------------------------------------------------------------------ *)
(* Expose infer_args as a top-level definition for CheckerSoundness      *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_args (fenv : list fn_def) (Γ : ctx)
    (args : list expr) (params : list param) : infer_result ctx :=
  match args, params with
  | [],       []       => infer_ok Γ
  | [],       _ :: _   => infer_err ErrArityMismatch
  | _ :: _,   []       => infer_err ErrArityMismatch
  | e :: es,  p :: ps  =>
      match infer_core fenv Γ e with
      | infer_err err            => infer_err err
      | infer_ok (T_e, Γ1) =>
          if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) then
            if usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
            then infer_args fenv Γ1 es ps
            else infer_err (ErrUsageMismatch (ty_usage T_e) (ty_usage (param_ty p)))
          else infer_err (ErrTypeMismatch (ty_core T_e) (ty_core (param_ty p)))
      end
  end.

(* ------------------------------------------------------------------ *)
(* Function-definition-level type checker                                *)
(* ------------------------------------------------------------------ *)

Fixpoint params_ok_b (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: ps' =>
      ctx_check_ok (param_name p) (param_ty p) Γ &&
      params_ok_b ps' Γ
  end.

(* Check a single function definition:
   - infer the body type
   - verify it matches fn_ret (core type + exact usage)
   - verify all linear/affine parameters are consumed *)
Definition infer (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer_body fenv (params_ctx (fn_params f)) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if ty_core_eqb (ty_core T_body) (ty_core (fn_ret f)) then
        if usage_eqb (ty_usage T_body) (ty_usage (fn_ret f)) then
          if params_ok_b (fn_params f) Γ_out
          then infer_ok (fn_ret f, Γ_out)
          else infer_err ErrContextCheckFailed
        else infer_err (ErrUsageMismatch (ty_usage (fn_ret f)) (ty_usage T_body))
      else infer_err (ErrTypeMismatch (ty_core (fn_ret f)) (ty_core T_body))
  end.

(* Check all functions in the program *)
Definition check_program (fenv : list fn_def) : bool :=
  forallb (fun f =>
    match infer fenv f with
    | infer_ok _ => true
    | infer_err _ => false
    end) fenv.

(* ------------------------------------------------------------------ *)
(* OCaml extraction                                                      *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
Extraction "../fixtures/TypeChecker.ml" infer check_program.
