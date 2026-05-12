From Facet.TypeSystem Require Import Lifetime Types Syntax.
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

  (* &x — shared borrow
     - x is present and unconsumed
     - x must not be linear (linear values must be consumed, not borrowed)
     - x is NOT consumed; ownership stays with the original binding
     - result type is &'static T (LStatic is a v1 approximation) *)
  | T_BorrowShared : forall Γ x T,
      ctx_lookup x Γ = Some (T, false) ->
      ty_usage T <> ULinear ->
      typed fenv Γ (EBorrow RShared (PVar x))
        (MkTy UUnrestricted (TRef LStatic RShared T)) Γ

  (* &mut x — mutable borrow
     - x is present and unconsumed
     - x must not be linear
     - x must be declared mutable (Rust: cannot &mut an immutable binding)
     - x is NOT consumed
     - result type is &'static mut T *)
  | T_BorrowMut : forall Γ x T,
      ctx_lookup x Γ = Some (T, false) ->
      ty_usage T <> ULinear ->
      ctx_lookup_mut x Γ = Some MMutable ->
      typed fenv Γ (EBorrow RUnique (PVar x))
        (MkTy UUnrestricted (TRef LStatic RUnique T)) Γ

  (* *r — dereference
     - r has reference type &'a rk T (with any usage u_r)
     - T must be UUnrestricted: move-out through a reference is forbidden
       (Rust semantics; affine/linear values can only be accessed via EReplace)
     - the reference usage u_r determines whether r itself is consumed *)
  | T_Deref : forall Γ Γ' r la rk T u_r,
      ty_usage T = UUnrestricted ->
      typed fenv Γ r (MkTy u_r (TRef la rk T)) Γ' ->
      typed fenv Γ (EDeref r) T Γ'

  (* &*r — shared re-borrow: r has any reference type &'a rk T *)
  | T_ReBorrowShared : forall Γ r la rk T u_r,
      ctx_lookup r Γ = Some (MkTy u_r (TRef la rk T), false) ->
      ty_usage (MkTy u_r (TRef la rk T)) <> ULinear ->
      typed fenv Γ (EBorrow RShared (PDeref (PVar r)))
        (MkTy UUnrestricted (TRef LStatic RShared T)) Γ

  (* &mut *r — mutable re-borrow: r must have &mut T and be mutable *)
  | T_ReBorrowMut : forall Γ r la T u_r,
      ctx_lookup r Γ = Some (MkTy u_r (TRef la RUnique T), false) ->
      ty_usage (MkTy u_r (TRef la RUnique T)) <> ULinear ->
      ctx_lookup_mut r Γ = Some MMutable ->
      typed fenv Γ (EBorrow RUnique (PDeref (PVar r)))
        (MkTy UUnrestricted (TRef LStatic RUnique T)) Γ

  (* *r <- e_new where r : &mut T: write through mutable reference, return old T *)
  | T_Replace_Deref : forall Γ Γ' r la T T_new e_new u_r,
      ctx_lookup r Γ = Some (MkTy u_r (TRef la RUnique T), false) ->
      ctx_lookup_mut r Γ = Some MMutable ->
      typed fenv Γ e_new T_new Γ' ->
      ty_core T_new = ty_core T ->
      usage_sub (ty_usage T_new) (ty_usage T) ->
      typed fenv Γ (EReplace (PDeref (PVar r)) e_new) T Γ'

  (* *r = e_new where r : &mut T (non-linear): assign through reference, return unit *)
  | T_Assign_Deref : forall Γ Γ' r la T T_new e_new u_r,
      ctx_lookup r Γ = Some (MkTy u_r (TRef la RUnique T), false) ->
      ctx_lookup_mut r Γ = Some MMutable ->
      ty_usage T <> ULinear ->
      typed fenv Γ e_new T_new Γ' ->
      ty_core T_new = ty_core T ->
      usage_sub (ty_usage T_new) (ty_usage T) ->
      typed fenv Γ (EAssign (PDeref (PVar r)) e_new) (MkTy UUnrestricted TUnits) Γ'

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

(* ------------------------------------------------------------------ *)
(* BorrowState: track active borrows for conflict checking              *)
(*                                                                      *)
(* borrow_ok is a separate judgment from typed; a well-typed program    *)
(* must satisfy both. This avoids changing typed's signature and        *)
(* breaking existing proofs.                                             *)
(* ------------------------------------------------------------------ *)

Inductive borrow_entry : Type :=
  | BEShared : ident -> borrow_entry   (* &x is active    *)
  | BEMut    : ident -> borrow_entry.  (* &mut x is active *)

Definition borrow_state := list borrow_entry.

Definition be_eqb (e1 e2 : borrow_entry) : bool :=
  match e1, e2 with
  | BEShared x, BEShared y => ident_eqb x y
  | BEMut x,    BEMut y    => ident_eqb x y
  | _,          _          => false
  end.

Fixpoint bs_eqb (bs1 bs2 : borrow_state) : bool :=
  match bs1, bs2 with
  | [],       []       => true
  | e1 :: t1, e2 :: t2 => be_eqb e1 e2 && bs_eqb t1 t2
  | _,        _        => false
  end.

(* x has an active mutable borrow *)
Definition bs_has_mut (x : ident) (bs : borrow_state) : bool :=
  existsb (fun e => match e with
    | BEMut y => ident_eqb x y | _ => false end) bs.

(* x has any active borrow (shared or mutable) *)
Definition bs_has_any (x : ident) (bs : borrow_state) : bool :=
  existsb (fun e => match e with
    | BEShared y | BEMut y => ident_eqb x y end) bs.

(* shared borrow allowed: no active mut borrow on x *)
Definition bs_can_shared (x : ident) (bs : borrow_state) : Prop :=
  bs_has_mut x bs = false.

(* mutable borrow allowed: no active borrow of any kind on x *)
Definition bs_can_mut (x : ident) (bs : borrow_state) : Prop :=
  bs_has_any x bs = false.

(* EDeref e is safe: if e = EVar r, r must not be mutably re-borrowed *)
Definition borrow_ok_deref_check (BS : borrow_state) (e : expr) : Prop :=
  match e with
  | EVar r => bs_can_shared r BS   (* = bs_has_mut r BS = false *)
  | _      => True
  end.

Fixpoint bs_remove_one (e : borrow_entry) (bs : borrow_state) : borrow_state :=
  match bs with
  | []     => []
  | h :: t => if be_eqb e h then t else h :: bs_remove_one e t
  end.

(* Remove all entries in to_remove from bs (scope-exit release) *)
Definition bs_remove_all (to_remove bs : borrow_state) : borrow_state :=
  fold_left (fun acc e => bs_remove_one e acc) to_remove bs.

(* Entries prepended to bs by a sub-expression.
   Relies on prepend-only invariant: bs_after = new ++ bs_before. *)
Definition bs_new_entries (bs_before bs_after : borrow_state) : borrow_state :=
  firstn (List.length bs_after - List.length bs_before) bs_after.

(* ------------------------------------------------------------------ *)
(* borrow_ok judgment                                                    *)
(*                                                                      *)
(* borrow_ok fenv BS Γ e BS'                                            *)
(*   Starting with borrow state BS and typing context Γ,                *)
(*   expression e is borrow-conflict-free and produces borrow state BS'. *)
(*   ctx Γ is input-only (no output Γ'); context changes are tracked    *)
(*   by typed separately.                                                *)
(* ------------------------------------------------------------------ *)

Inductive borrow_ok (fenv : list fn_def)
    : borrow_state -> ctx -> expr -> borrow_state -> Prop :=

  | BO_Unit : forall BS Γ,
      borrow_ok fenv BS Γ EUnit BS

  | BO_Lit : forall BS Γ l,
      borrow_ok fenv BS Γ (ELit l) BS

  | BO_Var : forall BS Γ x,
      borrow_ok fenv BS Γ (EVar x) BS

  (* shared borrow: OK if no active mut borrow on x *)
  | BO_BorrowShared : forall BS Γ x,
      bs_can_shared x BS ->
      borrow_ok fenv BS Γ (EBorrow RShared (PVar x)) (BEShared x :: BS)

  (* mutable borrow: OK if no active borrow of any kind on x *)
  | BO_BorrowMut : forall BS Γ x,
      bs_can_mut x BS ->
      borrow_ok fenv BS Γ (EBorrow RUnique (PVar x)) (BEMut x :: BS)

  | BO_Deref : forall BS BS' Γ e,
      borrow_ok_deref_check BS e ->
      borrow_ok fenv BS Γ e BS' ->
      borrow_ok fenv BS Γ (EDeref e) BS'

  | BO_Drop : forall BS BS' Γ e,
      borrow_ok fenv BS Γ e BS' ->
      borrow_ok fenv BS Γ (EDrop e) BS'

  | BO_Replace : forall BS BS' Γ x e_new,
      borrow_ok fenv BS Γ e_new BS' ->
      borrow_ok fenv BS Γ (EReplace (PVar x) e_new) BS'

  | BO_Assign : forall BS BS' Γ x e_new,
      borrow_ok fenv BS Γ e_new BS' ->
      borrow_ok fenv BS Γ (EAssign (PVar x) e_new) BS'

  (* write-through-reference: blocked if r has active re-borrow *)
  | BO_Replace_Deref : forall BS BS' Γ r e_new,
      bs_can_mut r BS ->
      borrow_ok fenv BS Γ e_new BS' ->
      borrow_ok fenv BS Γ (EReplace (PDeref (PVar r)) e_new) BS'

  | BO_Assign_Deref : forall BS BS' Γ r e_new,
      bs_can_mut r BS ->
      borrow_ok fenv BS Γ e_new BS' ->
      borrow_ok fenv BS Γ (EAssign (PDeref (PVar r)) e_new) BS'

  (* shared re-borrow: OK if no active mut borrow on r *)
  | BO_ReBorrowShared : forall BS Γ r,
      bs_can_shared r BS ->
      borrow_ok fenv BS Γ (EBorrow RShared (PDeref (PVar r))) (BEShared r :: BS)

  (* mutable re-borrow: OK if no active borrow of any kind on r *)
  | BO_ReBorrowMut : forall BS Γ r,
      bs_can_mut r BS ->
      borrow_ok fenv BS Γ (EBorrow RUnique (PDeref (PVar r))) (BEMut r :: BS)

  (* let: e1 produces BS1; e2 (with x in ctx) produces BS2.
     On scope exit, borrows introduced by e1 are released. *)
  | BO_Let : forall BS BS1 BS2 Γ m x T e1 e2,
      borrow_ok fenv BS Γ e1 BS1 ->
      borrow_ok fenv BS1 (ctx_add x T m Γ) e2 BS2 ->
      borrow_ok fenv BS Γ (ELet m x T e1 e2)
                (bs_remove_all (bs_new_entries BS BS1) BS2)

  (* let-infer: type of e1 not needed for borrow checking,
     so we do not extend Γ for e2 (conservative). *)
  | BO_LetInfer : forall BS BS1 BS2 Γ m x e1 e2,
      borrow_ok fenv BS Γ e1 BS1 ->
      borrow_ok fenv BS1 Γ e2 BS2 ->
      borrow_ok fenv BS Γ (ELetInfer m x e1 e2)
                (bs_remove_all (bs_new_entries BS BS1) BS2)

  (* if: both branches must produce the same borrow state *)
  | BO_If : forall BS BS1 BS2 BS3 Γ e1 e2 e3,
      borrow_ok fenv BS  Γ e1 BS1 ->
      borrow_ok fenv BS1 Γ e2 BS2 ->
      borrow_ok fenv BS1 Γ e3 BS3 ->
      BS2 = BS3 ->
      borrow_ok fenv BS Γ (EIf e1 e2 e3) BS2

  | BO_Call : forall BS BS' Γ fname args,
      borrow_ok_args fenv BS Γ args BS' ->
      borrow_ok fenv BS Γ (ECall fname args) BS'

with borrow_ok_args (fenv : list fn_def)
    : borrow_state -> ctx -> list expr -> borrow_state -> Prop :=

  | BO_Args_Nil : forall BS Γ,
      borrow_ok_args fenv BS Γ [] BS

  | BO_Args_Cons : forall BS BS1 BS2 Γ a rest,
      borrow_ok fenv BS Γ a BS1 ->
      borrow_ok_args fenv BS1 Γ rest BS2 ->
      borrow_ok_args fenv BS Γ (a :: rest) BS2.

Definition borrow_ok_fn_def (fenv : list fn_def) (f : fn_def) : Prop :=
  exists BS',
    borrow_ok fenv [] (params_ctx (fn_params f)) (fn_body f) BS'.
