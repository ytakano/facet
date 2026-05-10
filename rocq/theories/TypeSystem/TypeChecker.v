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
(* Type inference                                                        *)
(*                                                                      *)
(* infer fenv Γ e = Some (T, Γ')                                        *)
(*   Returns the type T and the updated context Γ' after e is typed.    *)
(* Returns None on any type or usage error.                              *)
(*                                                                      *)
(* The ECall case uses an inline local fixpoint to process the argument  *)
(* list without requiring a mutual fixpoint (which complicates           *)
(* termination checking).                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint infer (fenv : list fn_def) (Γ : ctx) (e : expr) : option (Ty * ctx) :=
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
      match infer fenv Γ e1 with
      | None          => None
      | Some (T1, Γ1) =>
          if ty_core_eqb (ty_core T1) (ty_core T) &&
             usage_sub_bool (ty_usage T1) (ty_usage T)
          then
            match infer fenv (ctx_add_b x T Γ1) e2 with
            | None          => None
            | Some (T2, Γ2) =>
                if ctx_check_ok x T Γ2
                then Some (T2, ctx_remove_b x Γ2)
                else None
            end
          else None
      end

  | EDrop e1 =>
      match infer fenv Γ e1 with
      | None         => None
      | Some (_, Γ') => Some (MkTy UUnrestricted TUnits, Γ')
      end

  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None              => None
      | Some (_, true)    => None
      | Some (T_x, false) =>
          match infer fenv Γ e_new with
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
                match infer fenv Γ0 e' with
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
      match infer fenv Γ e with
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
