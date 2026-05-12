From Facet.TypeSystem Require Import Types Syntax.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Typing context                                                        *)
(*                                                                      *)
(* Each entry is (variable_name, type, consumed?).                      *)
(* consumed = true means the binding has been moved/used.               *)
(* ------------------------------------------------------------------ *)

Definition ctx_entry : Type := (ident * Ty * bool * mutability)%type.
Definition ctx : Type := list ctx_entry.

(* ------------------------------------------------------------------ *)
(* Context helpers                                                       *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lookup (x : ident) (Γ : ctx) : option (Ty * bool) :=
  match Γ with
  | []              => None
  | (n, T, b, _) :: t => if ident_eqb x n then Some (T, b)
                      else ctx_lookup x t
  end.

(* Mark variable x as consumed. Returns None if x is not found. *)
Fixpoint ctx_consume (x : ident) (Γ : ctx) : option ctx :=
  match Γ with
  | []              => None
  | (n, T, b, m) :: t =>
      if ident_eqb x n
      then Some ((n, T, true, m) :: t)
      else match ctx_consume x t with
           | None    => None
           | Some t' => Some ((n, T, b, m) :: t')
           end
  end.

Fixpoint ctx_lookup_mut (x : ident) (Γ : ctx) : option mutability :=
  match Γ with
  | [] => None
  | (n, _, _, m) :: t => if ident_eqb x n then Some m else ctx_lookup_mut x t
  end.

(* Add a fresh (unconsumed) binding at the front. *)
Definition ctx_add (x : ident) (T : Ty) (m : mutability) (Γ : ctx) : ctx :=
  (x, T, false, m) :: Γ.

(* Remove the first occurrence of x. *)
Fixpoint ctx_remove (x : ident) (Γ : ctx) : ctx :=
  match Γ with
  | []              => []
  | (n, T, b, m) :: t =>
      if ident_eqb x n then t
      else (n, T, b, m) :: ctx_remove x t
  end.

(* Check scope-exit constraint for variable x with declared type T.
   - linear: x must have been consumed (consumed = true)
   - affine:  x may or may not have been consumed (always OK)
   - unrestricted: always OK *)
Definition ctx_is_ok (x : ident) (T : Ty) (Γ : ctx) : Prop :=
  match ty_usage T with
  | ULinear =>
      match ctx_lookup x Γ with
      | Some (_, true) => True
      | _              => False
      end
  | _ => True
  end.

(* Build the initial context for checking a function body from its
   parameters. Scope-exit checks reuse ctx_is_ok for each parameter. *)
Definition param_ctx_entry (p : param) : ctx_entry :=
  (param_name p, param_ty p, false, param_mutability p).

Fixpoint params_ctx (ps : list param) : ctx :=
  match ps with
  | [] => []
  | p :: ps' => param_ctx_entry p :: params_ctx ps'
  end.

Fixpoint params_ok (ps : list param) (Γ : ctx) : Prop :=
  match ps with
  | [] => True
  | p :: ps' =>
      ctx_is_ok (param_name p) (param_ty p) Γ /\ params_ok ps' Γ
  end.

(* ------------------------------------------------------------------ *)
(* Subtyping on usage qualifiers                                         *)
(*                                                                      *)
(* unrestricted <: affine <: linear                                      *)
(*                                                                      *)
(* u1 <: u2 means "a value with qualifier u1 may be used where          *)
(* qualifier u2 is expected."                                            *)
(* ------------------------------------------------------------------ *)

Inductive usage_sub : usage -> usage -> Prop :=
  | US_refl    : forall u,    usage_sub u u
  | US_unr_aff :              usage_sub UUnrestricted UAffine
  | US_aff_lin :              usage_sub UAffine       ULinear
  | US_unr_lin :              usage_sub UUnrestricted ULinear.

Definition usage_max (u1 u2 : usage) : usage :=
  match u1, u2 with
  | ULinear,       _             => ULinear
  | _,             ULinear       => ULinear
  | UAffine,       _             => UAffine
  | _,             UAffine       => UAffine
  | UUnrestricted, UUnrestricted => UUnrestricted
  end.

(* Merge two output contexts from if-branches.
   Linear variables must have the same consumed state in both branches.
   Affine/unrestricted variables: consumed if consumed in either branch. *)
Fixpoint ctx_merge (Γ2 Γ3 : ctx) : option ctx :=
  match Γ2, Γ3 with
  | [], [] => Some []
  | (n, T, b2, m) :: t2, (n', _, b3, _) :: t3 =>
      if negb (ident_eqb n n') then None
      else
        match ctx_merge t2 t3 with
        | None => None
        | Some rest =>
            match ty_usage T with
            | ULinear =>
                if Bool.eqb b2 b3 then Some ((n, T, b2, m) :: rest) else None
            | _ => Some ((n, T, orb b2 b3, m) :: rest)
            end
        end
  | _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(* Typing judgement                                                      *)
(*                                                                      *)
(* typed fenv Γ e T Γ'                                                   *)
(*   Under function environment fenv and input context Γ,               *)
(*   expression e has type T and the context becomes Γ' after           *)
(*   accounting for variable consumption.                                *)
(* ------------------------------------------------------------------ *)

Inductive typed (fenv : list fn_def) : ctx -> expr -> Ty -> ctx -> Prop :=

  | T_Unit : forall Γ,
      typed fenv Γ EUnit (MkTy UUnrestricted TUnits) Γ

  | T_LitInt : forall Γ n,
      typed fenv Γ (ELit (LInt n)) (MkTy UUnrestricted TIntegers) Γ

  | T_LitFloat : forall Γ f,
      typed fenv Γ (ELit (LFloat f)) (MkTy UUnrestricted TFloats) Γ

  | T_LitBool : forall Γ b,
      typed fenv Γ (ELit (LBool b)) (MkTy UUnrestricted TBooleans) Γ

  (* Linear/affine variable: consume the binding. *)
  | T_Var_Consume : forall Γ Γ' x T,
      ctx_lookup x Γ = Some (T, false) ->
      ty_usage T <> UUnrestricted ->
      ctx_consume x Γ = Some Γ' ->
      typed fenv Γ (EVar x) T Γ'

  (* Unrestricted variable: copy without consuming. *)
  | T_Var_Copy : forall Γ x T b,
      ctx_lookup x Γ = Some (T, b) ->
      ty_usage T = UUnrestricted ->
      typed fenv Γ (EVar x) T Γ

  (* let x: T = e1 in e2
     1. Type e1; the result type T1 must have the same core type as T
        and T1's usage must be a subtype of T's usage.
     2. Add x:T (fresh) to the post-e1 context.
     3. Type e2; afterwards check that x satisfies its usage constraint.
     4. Remove x from the output context. *)
  | T_Let : forall Γ Γ1 Γ2 m x T T1 e1 e2 T2,
      typed fenv Γ e1 T1 Γ1 ->
      ty_core T1 = ty_core T ->
      usage_sub (ty_usage T1) (ty_usage T) ->
      typed fenv (ctx_add x T m Γ1) e2 T2 Γ2 ->
      ctx_is_ok x T Γ2 ->
      typed fenv Γ (ELet m x T e1 e2) T2 (ctx_remove x Γ2)

  (* let x = e1 in e2 (no annotation): infer T1 from e1, bind x:T1. *)
  | T_LetInfer : forall Γ Γ1 Γ2 m x T1 e1 e2 T2,
      typed fenv Γ e1 T1 Γ1 ->
      typed fenv (ctx_add x T1 m Γ1) e2 T2 Γ2 ->
      ctx_is_ok x T1 Γ2 ->
      typed fenv Γ (ELetInfer m x e1 e2) T2 (ctx_remove x Γ2)

  (* drop(e): evaluate e (consuming it) and return unit. *)
  | T_Drop : forall Γ Γ' e T,
      typed fenv Γ e T Γ' ->
      typed fenv Γ (EDrop e) (MkTy UUnrestricted TUnits) Γ'

  (* replace(x, e_new):
     - x must be present and unconsumed (it is NOT consumed by replace).
     - x must be mutable.
     - The new value's core type must match x's core type.
     - The new value's usage must be a subtype of x's usage.
     - Returns the old value of x (same type as x). *)
  | T_Replace : forall Γ Γ' x T T_new e_new,
      ctx_lookup x Γ = Some (T, false) ->
      ctx_lookup_mut x Γ = Some MMutable ->
      typed fenv Γ e_new T_new Γ' ->
      ty_core T_new = ty_core T ->
      usage_sub (ty_usage T_new) (ty_usage T) ->
      typed fenv Γ (EReplace (PVar x) e_new) T Γ'

  | T_Assign : forall Γ Γ' x T T_new e_new,
      ctx_lookup x Γ = Some (T, false) ->
      ctx_lookup_mut x Γ = Some MMutable ->
      ty_usage T <> ULinear ->
      typed fenv Γ e_new T_new Γ' ->
      ty_core T_new = ty_core T ->
      usage_sub (ty_usage T_new) (ty_usage T) ->
      typed fenv Γ (EAssign (PVar x) e_new) (MkTy UUnrestricted TUnits) Γ'

  (* if e1 { e2 } else { e3 }:
     - e1 must have bool type (any usage)
     - e2, e3 must have the same core type
     - linear variables must be consumed by both branches or neither
     - result usage = max(usage of e2, usage of e3) *)
  | T_If : forall Γ Γ1 Γ2 Γ3 Γ4 e1 e2 e3 T_cond T2 T3,
      typed fenv Γ e1 T_cond Γ1 ->
      ty_core T_cond = TBooleans ->
      typed fenv Γ1 e2 T2 Γ2 ->
      typed fenv Γ1 e3 T3 Γ3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge Γ2 Γ3 = Some Γ4 ->
      typed fenv Γ (EIf e1 e2 e3)
           (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)) Γ4

  (* f(args): look up function definition, type-check arguments. *)
  | T_Call : forall Γ Γ' fname fdef args,
      In fdef fenv ->
      fn_name fdef = fname ->
      typed_args fenv Γ args (fn_params fdef) Γ' ->
      typed fenv Γ (ECall fname args) (fn_ret fdef) Γ'

(* Type-check a list of arguments against a list of parameters.
   Each argument's type must have the same core type as the parameter's
   declared type and a compatible usage (subtype). The context threads
   through left-to-right, consuming linear/affine arguments. *)
with typed_args (fenv : list fn_def)
    : ctx -> list expr -> list param -> ctx -> Prop :=

  | TArgs_Nil : forall Γ,
      typed_args fenv Γ [] [] Γ

  | TArgs_Cons : forall Γ Γ1 Γ2 e es p ps T_e,
      typed fenv Γ e T_e Γ1 ->
      ty_core T_e = ty_core (param_ty p) ->
      usage_sub (ty_usage T_e) (ty_usage (param_ty p)) ->
      typed_args fenv Γ1 es ps Γ2 ->
      typed_args fenv Γ (e :: es) (p :: ps) Γ2.

Definition typed_fn_def (fenv : list fn_def) (f : fn_def) : Prop :=
  exists Γ',
    typed fenv (params_ctx (fn_params f)) (fn_body f) (fn_ret f) Γ' /\
    params_ok (fn_params f) Γ'.
