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
  | TNamed s1, TNamed s2 => String.eqb s1 s2
  | _,         _         => false
  end.

(* ------------------------------------------------------------------ *)
(* Decidable context operations                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lookup_b (x : ident) (Γ : ctx) : option (Ty * bool) :=
  match Γ with
  | []              => None
  | (n, T, b) :: t => if String.eqb x n then Some (T, b)
                      else ctx_lookup_b x t
  end.

Fixpoint ctx_consume_b (x : ident) (Γ : ctx) : option ctx :=
  match Γ with
  | []              => None
  | (n, T, b) :: t =>
      if String.eqb x n
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
      if String.eqb x n then t
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
  | f :: t => if String.eqb name (fn_name f) then Some f
              else lookup_fn_b name t
  end.

(* ------------------------------------------------------------------ *)
(* Alpha renaming                                                       *)
(* ------------------------------------------------------------------ *)

Definition rename_env : Type := list (ident * ident).

Fixpoint ident_in (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: ys => if String.eqb x y then true else ident_in x ys
  end.

Fixpoint lookup_rename (x : ident) (ρ : rename_env) : ident :=
  match ρ with
  | [] => x
  | (old, fresh) :: ρ' =>
      if String.eqb x old then fresh else lookup_rename x ρ'
  end.

Fixpoint fresh_ident_go (fuel : nat) (candidate : ident)
    (used : list ident) : ident :=
  match fuel with
  | O => candidate
  | S fuel' =>
      if ident_in candidate used
      then fresh_ident_go fuel' (String.append candidate "_") used
      else candidate
  end.

Definition fresh_ident (x : ident) (used : list ident) : ident :=
  fresh_ident_go (S (List.length used)) x used.

Fixpoint ctx_names (Γ : ctx) : list ident :=
  match Γ with
  | [] => []
  | (x, _, _) :: Γ' => x :: ctx_names Γ'
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
      let x' := fresh_ident x used1 in
      let used2 := x' :: used1 in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELet m x' T e1' e2', used3)
  | ELetInfer m x e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let x' := fresh_ident x used1 in
      let used2 := x' :: used1 in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELetInfer m x' e1' e2', used3)
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
  let '(params', ρ, used1) := alpha_rename_params [] used (fn_params f) in
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
  let (fenv', used) := alpha_rename_syntax_go (ctx_names Γ) fenv in
  let (e', _) := alpha_rename_expr [] used e in
  (fenv', e').

(* ------------------------------------------------------------------ *)
(* Type inference                                                        *)
(*                                                                      *)
(* infer_core fenv Γ e = Some (T, Γ')                                   *)
(*   Returns the type T and the updated context Γ' after e is typed.    *)
(* Returns None on any type or usage error.                              *)
(*                                                                      *)
(* The ECall case uses an inline local fixpoint to process the argument  *)
(* list without requiring a mutual fixpoint (which complicates           *)
(* termination checking).                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_core (fenv : list fn_def) (Γ : ctx) (e : expr)
    : option (Ty * ctx) :=
  match e with

  | EUnit =>
      Some (MkTy UUnrestricted TUnits, Γ)

  | ELit (LInt _) =>
      Some (MkTy UUnrestricted TIntegers, Γ)

  | ELit (LFloat _) =>
      Some (MkTy UUnrestricted TFloats, Γ)

  | EVar x =>
      match ctx_lookup_b x Γ with
      | None        => None
      | Some (T, b) =>
          if usage_eqb (ty_usage T) UUnrestricted
          then Some (T, Γ)
          else if b
               then None  (* already consumed *)
               else match ctx_consume_b x Γ with
                    | None    => None
                    | Some Γ' => Some (T, Γ')
                    end
      end

  | ELet m x T e1 e2 =>
      match infer_core fenv Γ e1 with
      | None          => None
      | Some (T1, Γ1) =>
          if ty_core_eqb (ty_core T1) (ty_core T) &&
             usage_sub_bool (ty_usage T1) (ty_usage T)
          then
            match infer_core fenv (ctx_add_b x T Γ1) e2 with
            | None          => None
            | Some (T2, Γ2) =>
                if ctx_check_ok x T Γ2
                then Some (T2, ctx_remove_b x Γ2)
                else None
            end
          else None
      end

  | EDrop e1 =>
      match infer_core fenv Γ e1 with
      | None         => None
      | Some (_, Γ') => Some (MkTy UUnrestricted TUnits, Γ')
      end

  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None              => None
      | Some (_, true)    => None
      | Some (T_x, false) =>
          match infer_core fenv Γ e_new with
          | None            => None
          | Some (T_new, Γ') =>
              if ty_core_eqb (ty_core T_new) (ty_core T_x) &&
                 usage_sub_bool (ty_usage T_new) (ty_usage T_x)
              then Some (T_x, Γ')
              else None
          end
      end

  | ECall fname args =>
      match lookup_fn_b fname fenv with
      | None      => None
      | Some fdef =>
          (* Process argument list with an inline fixpoint so that
             Rocq's termination checker sees the structural recursion
             clearly: each arg is a sub-term of the args field of ECall. *)
          let fix go (Γ0 : ctx) (as_ : list expr) (ps : list param)
              : option ctx :=
            match as_, ps with
            | [],       []       => Some Γ0
            | [],       _ :: _   => None
            | _ :: _,   []       => None
            | e' :: es, p :: ps' =>
                match infer_core fenv Γ0 e' with
                | None            => None
                | Some (T_e, Γ1) =>
                    if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) &&
                       usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
                    then go Γ1 es ps'
                    else None
                end
            end
          in
          match go Γ args (fn_params fdef) with
          | None    => None
          | Some Γ' => Some (fn_ret fdef, Γ')
          end
      end

  | ELetInfer _ _ _ _ => None  (* out of scope *)

  end.

Definition infer (fenv : list fn_def) (Γ : ctx) (e : expr)
    : option (Ty * ctx) :=
  let (fenv', e') := alpha_rename_for_infer Γ fenv e in
  infer_core fenv' Γ e'.

(* ------------------------------------------------------------------ *)
(* Expose infer_args as a top-level definition for CheckerSoundness      *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_args (fenv : list fn_def) (Γ : ctx)
    (args : list expr) (params : list param) : option ctx :=
  match args, params with
  | [],       []       => Some Γ
  | [],       _ :: _   => None
  | _ :: _,   []       => None
  | e :: es,  p :: ps  =>
      match infer_core fenv Γ e with
      | None           => None
      | Some (T_e, Γ1) =>
          if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) &&
             usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
          then infer_args fenv Γ1 es ps
          else None
      end
  end.

(* ------------------------------------------------------------------ *)
(* OCaml extraction                                                      *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
Extraction "../fixtures/TypeChecker.ml" infer.
