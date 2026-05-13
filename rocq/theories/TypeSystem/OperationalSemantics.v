From Facet.TypeSystem Require Import Types Syntax PathState.
From Stdlib Require Import List String ZArith Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Values                                                               *)
(* ------------------------------------------------------------------ *)

Inductive value : Type :=
  | VUnit    : value
  | VInt     : Z -> value
  | VFloat   : string -> value
  | VBool    : bool -> value
  | VStruct  : string -> list (string * value) -> value
  | VRef     : ident -> value
  | VClosure : ident -> list store_entry -> value
with store_entry : Type :=
  | MkStoreEntry : ident -> Ty -> value -> binding_state -> store_entry.

Definition se_name (e : store_entry) : ident :=
  match e with
  | MkStoreEntry x _ _ _ => x
  end.

Definition se_ty (e : store_entry) : Ty :=
  match e with
  | MkStoreEntry _ T _ _ => T
  end.

Definition se_val (e : store_entry) : value :=
  match e with
  | MkStoreEntry _ _ v _ => v
  end.

Definition se_state (e : store_entry) : binding_state :=
  match e with
  | MkStoreEntry _ _ _ st => st
  end.

Definition se_used (e : store_entry) : bool :=
  st_consumed (se_state e).

(* ------------------------------------------------------------------ *)
(* Runtime store                                                        *)
(* ------------------------------------------------------------------ *)

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
      then MkStoreEntry (se_name e) (se_ty e) (se_val e)
             (state_consume_path [] (se_state e)) :: t
      else e :: store_mark_used x t
  end.

Fixpoint store_update_val (x : ident) (v : value) (s : store) : option store :=
  match s with
  | []     => None
  | e :: t =>
      if ident_eqb x (se_name e)
      then Some (MkStoreEntry (se_name e) (se_ty e) v (se_state e) :: t)
      else match store_update_val x v t with
           | None    => None
           | Some t' => Some (e :: t')
           end
  end.

Definition store_add (x : ident) (T : Ty) (v : value) (s : store) : store :=
  MkStoreEntry x T v (binding_state_of_bool false) :: s.

Fixpoint value_lookup_path (v : value) (p : field_path) : option value :=
  match p with
  | [] => Some v
  | f :: rest =>
      match v with
      | VStruct _ fields =>
          let fix lookup (fields : list (string * value)) : option value :=
              match fields with
              | [] => None
              | (name, fv) :: tail =>
                  if String.eqb f name then Some fv else lookup tail
              end
          in match lookup fields with
          | Some fv => value_lookup_path fv rest
          | None => None
          end
      | _ => None
      end
  end.

Fixpoint value_update_path (v : value) (p : field_path) (v_new : value) : option value :=
  match p with
  | [] => Some v_new
  | f :: rest =>
      match v with
      | VStruct sname fields =>
          let fix update (fields : list (string * value)) : option (list (string * value)) :=
            match fields with
            | [] => None
            | (name, fv) :: tail =>
                if String.eqb f name
                then match value_update_path fv rest v_new with
                     | Some fv' => Some ((name, fv') :: tail)
                     | None => None
                     end
                else match update tail with
                     | Some tail' => Some ((name, fv) :: tail')
                     | None => None
                     end
            end
          in
          match update fields with
          | Some fields' => Some (VStruct sname fields')
          | None => None
          end
      | _ => None
      end
  end.

Definition store_lookup_path (x : ident) (p : field_path) (s : store) : option value :=
  match store_lookup x s with
  | Some e => value_lookup_path (se_val e) p
  | None => None
  end.

Fixpoint store_update_path (x : ident) (p : field_path) (v_new : value) (s : store)
    : option store :=
  match s with
  | [] => None
  | e :: t =>
      if ident_eqb x (se_name e)
      then match value_update_path (se_val e) p v_new with
           | Some v' => Some (MkStoreEntry (se_name e) (se_ty e) v' (se_state e) :: t)
           | None => None
           end
      else match store_update_path x p v_new t with
           | Some t' => Some (e :: t')
           | None => None
           end
  end.

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

  | Eval_Place : forall s p x path e v,
      place_path p = Some (x, path) ->
      store_lookup x s = Some e ->
      value_lookup_path (se_val e) path = Some v ->
      eval fenv s (EPlace p) s v

  | Eval_Struct : forall s s' name lts args fields values,
      eval_struct_fields fenv s fields s' values ->
      eval fenv s (EStruct name lts args fields) s' (VStruct name values)

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

  | Eval_Replace_Field : forall s s1 s2 p x path old_v e_new v_new,
      place_path p = Some (x, path) ->
      store_lookup_path x path s = Some old_v ->
      eval fenv s e_new s1 v_new ->
      store_update_path x path v_new s1 = Some s2 ->
      eval fenv s (EReplace p e_new) s2 old_v

  | Eval_Assign_Field : forall s s1 s2 p x path e_new v_new,
      place_path p = Some (x, path) ->
      eval fenv s e_new s1 v_new ->
      store_update_path x path v_new s1 = Some s2 ->
      eval fenv s (EAssign p e_new) s2 VUnit

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
  | Eval_Deref_Place : forall s r p x e,
      expr_as_place r = Some p ->
      eval_place s p x ->
      store_lookup x s = Some e ->
      ty_usage (se_ty e) = UUnrestricted ->
      eval fenv s (EDeref r) s (se_val e)

  | Eval_Deref : forall s s_r r x e,
      expr_as_place r = None ->
      eval fenv s r s_r (VRef x) ->
      store_lookup x s_r = Some e ->
      ty_usage (se_ty e) = UUnrestricted ->
      eval fenv s (EDeref r) s_r (se_val e)

  | Eval_Fn : forall s fname,
      eval fenv s (EFn fname) s (VClosure fname [])

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

  | Eval_CallExpr : forall s s_fn s_args s_body callee args fname captured fdef vs ret,
      eval fenv s callee s_fn (VClosure fname captured) ->
      lookup_fn fname fenv = Some fdef ->
      eval_args fenv s_fn args s_args vs ->
      eval fenv (bind_params (fn_params fdef) vs (captured ++ s_args))
                (fn_body fdef) s_body ret ->
      eval fenv s (ECallExpr callee args)
               (store_remove_params (fn_params fdef) s_body) ret

(* Evaluate argument list left-to-right, threading the store. *)
with eval_args (fenv : list fn_def)
    : store -> list expr -> store -> list value -> Prop :=

  | EvalArgs_Nil : forall s,
      eval_args fenv s [] s []

  | EvalArgs_Cons : forall s s1 s2 e es v vs,
      eval fenv s e s1 v ->
      eval_args fenv s1 es s2 vs ->
      eval_args fenv s (e :: es) s2 (v :: vs)

with eval_struct_fields (fenv : list fn_def)
    : store -> list (string * expr) -> store -> list (string * value) -> Prop :=

  | EvalStructFields_Nil : forall s,
      eval_struct_fields fenv s [] s []

  | EvalStructFields_Cons : forall s s1 s2 name e rest v values,
      eval fenv s e s1 v ->
      eval_struct_fields fenv s1 rest s2 values ->
      eval_struct_fields fenv s ((name, e) :: rest) s2 ((name, v) :: values).
