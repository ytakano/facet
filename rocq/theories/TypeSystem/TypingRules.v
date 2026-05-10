From Facet.TypeSystem Require Import Types Syntax.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Typing context                                                        *)
(*                                                                      *)
(* Each entry is (variable_name, type, consumed?).                      *)
(* consumed = true means the binding has been moved/used.               *)
(* ------------------------------------------------------------------ *)

Definition ctx_entry : Type := (ident * Ty * bool)%type.
Definition ctx : Type := list ctx_entry.

(* ------------------------------------------------------------------ *)
(* Context helpers                                                       *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lookup (x : ident) (Γ : ctx) : option (Ty * bool) :=
  match Γ with
  | []              => None
  | (n, T, b) :: t => if ident_eqb x n then Some (T, b)
                      else ctx_lookup x t
  end.

(* Mark variable x as consumed. Returns None if x is not found. *)
Fixpoint ctx_consume (x : ident) (Γ : ctx) : option ctx :=
  match Γ with
  | []              => None
  | (n, T, b) :: t =>
      if ident_eqb x n
      then Some ((n, T, true) :: t)
      else match ctx_consume x t with
           | None    => None
           | Some t' => Some ((n, T, b) :: t')
           end
  end.

(* Add a fresh (unconsumed) binding at the front. *)
Definition ctx_add (x : ident) (T : Ty) (Γ : ctx) : ctx :=
  (x, T, false) :: Γ.

(* Remove the first occurrence of x. *)
Fixpoint ctx_remove (x : ident) (Γ : ctx) : ctx :=
  match Γ with
  | []              => []
  | (n, T, b) :: t =>
      if ident_eqb x n then t
      else (n, T, b) :: ctx_remove x t
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
  (param_name p, param_ty p, false).

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
      typed fenv (ctx_add x T Γ1) e2 T2 Γ2 ->
      ctx_is_ok x T Γ2 ->
      typed fenv Γ (ELet m x T e1 e2) T2 (ctx_remove x Γ2)

  (* drop(e): evaluate e (consuming it) and return unit. *)
  | T_Drop : forall Γ Γ' e T,
      typed fenv Γ e T Γ' ->
      typed fenv Γ (EDrop e) (MkTy UUnrestricted TUnits) Γ'

  (* replace(x, e_new):
     - x must be present and unconsumed (it is NOT consumed by replace).
     - The new value's core type must match x's core type.
     - The new value's usage must be a subtype of x's usage.
     - Returns the old value of x (same type as x). *)
  | T_Replace : forall Γ Γ' x T T_new e_new,
      ctx_lookup x Γ = Some (T, false) ->
      typed fenv Γ e_new T_new Γ' ->
      ty_core T_new = ty_core T ->
      usage_sub (ty_usage T_new) (ty_usage T) ->
      typed fenv Γ (EReplace (PVar x) e_new) T Γ'

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
