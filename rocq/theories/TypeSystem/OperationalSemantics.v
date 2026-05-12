From Facet.TypeSystem Require Import Types Syntax.
From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Values                                                               *)
(* ------------------------------------------------------------------ *)

Inductive value : Type :=
  | VUnit  : value
  | VInt   : Z -> value
  | VFloat : string -> value
  | VBool  : bool -> value
  | VRef   : ident -> value.   (* reference: holds the name of the referred variable *)

(* ------------------------------------------------------------------ *)
(* Runtime store                                                        *)
(* ------------------------------------------------------------------ *)

Record store_entry : Type := MkStoreEntry {
  se_name : ident;
  se_ty   : Ty;
  se_val  : value;
  se_used : bool   (* true = already consumed *)
}.

Definition store := list store_entry.

(* ------------------------------------------------------------------ *)
(* Store helpers (defined before eval to avoid forward references)      *)
(* ------------------------------------------------------------------ *)

Fixpoint store_lookup (x : ident) (s : store) : option store_entry :=
  match s with
  | []     => None
  | e :: t => if ident_eqb x (se_name e) then Some e
              else store_lookup x t
  end.

Fixpoint store_mark_used (x : ident) (s : store) : store :=
  match s with
  | []     => []
  | e :: t =>
      if ident_eqb x (se_name e)
      then MkStoreEntry (se_name e) (se_ty e) (se_val e) true :: t
      else e :: store_mark_used x t
  end.

Fixpoint store_update_val (x : ident) (v : value) (s : store) : option store :=
  match s with
  | []     => None
  | e :: t =>
      if ident_eqb x (se_name e)
      then Some (MkStoreEntry (se_name e) (se_ty e) v (se_used e) :: t)
      else match store_update_val x v t with
           | None    => None
           | Some t' => Some (e :: t')
           end
  end.

Definition store_add (x : ident) (T : Ty) (v : value) (s : store) : store :=
  MkStoreEntry x T v false :: s.

Fixpoint store_remove (x : ident) (s : store) : store :=
  match s with
  | []     => []
  | e :: t =>
      if ident_eqb x (se_name e) then t
      else e :: store_remove x t
  end.

Fixpoint store_remove_params (params : list param) (s : store) : store :=
  match params with
  | []      => s
  | p :: ps => store_remove_params ps (store_remove (param_name p) s)
  end.

Fixpoint bind_params (params : list param) (vs : list value) (s : store) : store :=
  match params, vs with
  | [],      _        => s
  | _,       []       => s
  | p :: ps, v :: vs' =>
      bind_params ps vs' (store_add (param_name p) (param_ty p) v s)
  end.

Definition needs_consume (T : Ty) : bool :=
  match ty_usage T with
  | UUnrestricted => false
  | _             => true
  end.

Fixpoint lookup_fn (name : ident) (fenv : list fn_def) : option fn_def :=
  match fenv with
  | []     => None
  | f :: t => if ident_eqb name (fn_name f) then Some f
              else lookup_fn name t
  end.

Inductive eval_place : store -> place -> ident -> Prop :=
  | EvalPlace_Var : forall s x e,
      store_lookup x s = Some e ->
      eval_place s (PVar x) x
  | EvalPlace_Deref : forall s p r x se_r,
      eval_place s p r ->
      store_lookup r s = Some se_r ->
      se_val se_r = VRef x ->
      eval_place s (PDeref p) x.

(* ------------------------------------------------------------------ *)
(* Big-step evaluation                                                  *)
(*                                                                      *)
(* eval fenv s e s' v                                                   *)
(*   Expression e evaluates to v, transforming store s into s'.         *)
(*                                                                      *)
(* Usage violations result in no derivation (evaluation gets stuck):    *)
(*   - reading an already-consumed affine/linear variable               *)
(* ------------------------------------------------------------------ *)

Inductive eval (fenv : list fn_def) : store -> expr -> store -> value -> Prop :=

  | Eval_Unit : forall s,
      eval fenv s EUnit s VUnit

  | Eval_LitInt : forall s n,
      eval fenv s (ELit (LInt n)) s (VInt n)

  | Eval_LitFloat : forall s f,
      eval fenv s (ELit (LFloat f)) s (VFloat f)

  | Eval_LitBool : forall s b,
      eval fenv s (ELit (LBool b)) s (VBool b)

  (* Unrestricted variable: copy without consuming. *)
  | Eval_Var_Copy : forall s x e,
      store_lookup x s = Some e ->
      needs_consume (se_ty e) = false ->
      eval fenv s (EVar x) s (se_val e)

  (* Linear/affine variable: consume on read (must not be consumed yet). *)
  | Eval_Var_Consume : forall s x e,
      store_lookup x s = Some e ->
      needs_consume (se_ty e) = true ->
      se_used e = false ->
      eval fenv s (EVar x) (store_mark_used x s) (se_val e)

  (* let x: T = e1 in e2 *)
  | Eval_Let : forall s s1 s2 m x T e1 e2 v1 v2,
      eval fenv s e1 s1 v1 ->
      eval fenv (store_add x T v1 s1) e2 s2 v2 ->
      eval fenv s (ELet m x T e1 e2) (store_remove x s2) v2

  (* drop(e): evaluate and discard. *)
  | Eval_Drop : forall s s' e v,
      eval fenv s e s' v ->
      eval fenv s (EDrop e) s' VUnit

  (* replace(x, e_new): update x in-place, return old value.
     x itself is NOT consumed. *)
  | Eval_Replace : forall s s1 s2 x old_e e_new v_new,
      store_lookup x s = Some old_e ->
      eval fenv s e_new s1 v_new ->
      store_update_val x v_new s1 = Some s2 ->
      eval fenv s (EReplace (PVar x) e_new) s2 (se_val old_e)

  | Eval_Assign : forall s s1 s2 x old_e e_new v_new,
      store_lookup x s = Some old_e ->
      eval fenv s e_new s1 v_new ->
      store_update_val x v_new s1 = Some s2 ->
      eval fenv s (EAssign (PVar x) e_new) s2 VUnit

  (* &x or &mut x: confirm x exists in the store, return VRef x.
     The store is unchanged — borrowing does not transfer ownership. *)
  | Eval_Borrow : forall s x e rk,
      store_lookup x s = Some e ->
      eval fenv s (EBorrow rk (PVar x)) s (VRef x)

  (* *p <- e_new: p resolves to a reference target x, return old value *)
  | Eval_Replace_Deref : forall s s1 s2 p x old_e e_new v_new,
      eval_place s (PDeref p) x ->
      store_lookup x s = Some old_e ->
      eval fenv s e_new s1 v_new ->
      store_update_val x v_new s1 = Some s2 ->
      eval fenv s (EReplace (PDeref p) e_new) s2 (se_val old_e)

  (* *p = e_new: p resolves to a reference target x, return unit *)
  | Eval_Assign_Deref : forall s s1 s2 p x old_e e_new v_new,
      eval_place s (PDeref p) x ->
      store_lookup x s = Some old_e ->
      eval fenv s e_new s1 v_new ->
      store_update_val x v_new s1 = Some s2 ->
      eval fenv s (EAssign (PDeref p) e_new) s2 VUnit

  (* &*p — re-borrow: p resolves to a reference target x *)
  | Eval_ReBorrow : forall s p x rk,
      eval_place s (PDeref p) x ->
      eval fenv s (EBorrow rk (PDeref p)) s (VRef x)

  (* *r: evaluate r to VRef x, then copy the value of x from the store.
     Only applicable when the inner type is UUnrestricted (copy semantics).
     The type checker enforces this; the store is unchanged. *)
  | Eval_Deref : forall s s_r r x e,
      eval fenv s r s_r (VRef x) ->
      store_lookup x s_r = Some e ->
      ty_usage (se_ty e) = UUnrestricted ->
      eval fenv s (EDeref r) s_r (se_val e)

  | Eval_If_True : forall s s1 s2 e1 e2 e3 v,
      eval fenv s e1 s1 (VBool true) ->
      eval fenv s1 e2 s2 v ->
      eval fenv s (EIf e1 e2 e3) s2 v

  | Eval_If_False : forall s s1 s2 e1 e2 e3 v,
      eval fenv s e1 s1 (VBool false) ->
      eval fenv s1 e3 s2 v ->
      eval fenv s (EIf e1 e2 e3) s2 v

  (* f(args): look up function, evaluate arguments, evaluate body. *)
  | Eval_Call : forall s s_args s_body fname fdef args vs ret,
      lookup_fn fname fenv = Some fdef ->
      eval_args fenv s args s_args vs ->
      eval fenv (bind_params (fn_params fdef) vs s_args)
                (fn_body fdef) s_body ret ->
      eval fenv s (ECall fname args)
               (store_remove_params (fn_params fdef) s_body) ret

(* Evaluate argument list left-to-right, threading the store. *)
with eval_args (fenv : list fn_def)
    : store -> list expr -> store -> list value -> Prop :=

  | EvalArgs_Nil : forall s,
      eval_args fenv s [] s []

  | EvalArgs_Cons : forall s s1 s2 e es v vs,
      eval fenv s e s1 v ->
      eval_args fenv s1 es s2 vs ->
      eval_args fenv s (e :: es) s2 (v :: vs).
