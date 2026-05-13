From Stdlib.Strings Require Import String.
From Stdlib Require Import List PeanoNat Bool.
Import ListNotations.
From Facet.TypeSystem Require Import Lifetime.

Inductive mutability :=
| MImmutable
| MMutable.

Inductive usage :=
| ULinear
| UAffine
| UUnrestricted.

Inductive ref_kind :=
| RShared      (* &T *)
| RUnique.     (* &mut T *)

Inductive TypeCore (A : Type) : Type :=
| TUnits    : TypeCore A
| TIntegers : TypeCore A
| TFloats   : TypeCore A
| TBooleans : TypeCore A
| TNamed    : string -> TypeCore A
| TParam    : nat -> TypeCore A
| TStruct   : string -> list lifetime -> list A -> TypeCore A
| TFn       : list A -> A -> TypeCore A
| TForall   : nat -> outlives_ctx -> A -> TypeCore A
| TRef      : lifetime -> ref_kind -> A -> TypeCore A.

Arguments TUnits {A}.
Arguments TIntegers {A}.
Arguments TFloats {A}.
Arguments TBooleans {A}.
Arguments TNamed {A} _.
Arguments TParam {A} _.
Arguments TStruct {A} _ _ _.
Arguments TFn {A} _ _.
Arguments TForall {A} _ _ _.
Arguments TRef {A} _ _ _.

Inductive Ty : Type :=
| MkTy : usage -> TypeCore Ty -> Ty.

Definition ty_usage (T : Ty) : usage :=
  match T with
  | MkTy u _ => u
  end.

Definition ty_core (T : Ty) : TypeCore Ty :=
match T with
| MkTy _ c => c
end.

Definition ref_usage_ok_b (u : usage) (rk : ref_kind) : bool :=
  match rk with
  | RShared => true
  | RUnique =>
      match u with
      | UUnrestricted => false
      | UAffine | ULinear => true
      end
  end.


(* ------------------------------------------------------------------ *)
(* Lifetime substitution on types                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint apply_lt_lifetime (σ : list lifetime) (l : lifetime) : lifetime :=
  match l with
  | LStatic => LStatic
  | LVar i  =>
      match nth_error σ i with
      | Some l' => l'
      | None    => LVar i
      end
  | LBound i => LBound i
  end.

Definition apply_lt_outlives (σ : list lifetime) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (apply_lt_lifetime σ a, apply_lt_lifetime σ b)) Ω.

Definition close_fn_lifetime (m : nat) (l : lifetime) : lifetime :=
  match l with
  | LVar i => if Nat.ltb i m then LBound i else l
  | _ => l
  end.

Fixpoint apply_lt_ty (σ : list lifetime) (T : Ty) {struct T} : Ty :=
  match T with
  | MkTy u TUnits => MkTy u TUnits
  | MkTy u TIntegers => MkTy u TIntegers
  | MkTy u TFloats => MkTy u TFloats
  | MkTy u TBooleans => MkTy u TBooleans
  | MkTy u (TNamed s) => MkTy u (TNamed s)
  | MkTy u (TParam i) => MkTy u (TParam i)
  | MkTy u (TStruct name lts args) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TStruct name (map (apply_lt_lifetime σ) lts) (map_lt args))
  | MkTy u (TFn ts r) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TFn (map_lt ts) (apply_lt_ty σ r))
  | MkTy u (TForall n Ω body) =>
      MkTy u (TForall n (apply_lt_outlives σ Ω) (apply_lt_ty σ body))
  | MkTy u (TRef l rk t) =>
      MkTy u (TRef (apply_lt_lifetime σ l) rk (apply_lt_ty σ t))
  end.

Fixpoint map_lifetimes_ty
    (f : lifetime -> lifetime) (T : Ty) {struct T} : Ty :=
  match T with
  | MkTy u TUnits => MkTy u TUnits
  | MkTy u TIntegers => MkTy u TIntegers
  | MkTy u TFloats => MkTy u TFloats
  | MkTy u TBooleans => MkTy u TBooleans
  | MkTy u (TNamed s) => MkTy u (TNamed s)
  | MkTy u (TParam i) => MkTy u (TParam i)
  | MkTy u (TStruct name lts args) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => map_lifetimes_ty f x :: go xs'
        end
      in
      MkTy u (TStruct name (map f lts) (go args))
  | MkTy u (TFn ts r) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => map_lifetimes_ty f x :: go xs'
        end
      in
      MkTy u (TFn (go ts) (map_lifetimes_ty f r))
  | MkTy u (TForall n Ω body) =>
      MkTy u (TForall n (map (fun '(a, b) => (f a, f b)) Ω)
        (map_lifetimes_ty f body))
  | MkTy u (TRef l rk t) =>
      MkTy u (TRef (f l) rk (map_lifetimes_ty f t))
  end.

Definition close_fn_ty (m : nat) (T : Ty) : Ty :=
  map_lifetimes_ty (close_fn_lifetime m) T.

Definition close_fn_outlives (m : nat) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (close_fn_lifetime m a, close_fn_lifetime m b)) Ω.

Definition open_bound_lifetime (σ : list (option lifetime)) (l : lifetime) : lifetime :=
  match l with
  | LBound i =>
      match nth_error σ i with
      | Some (Some l') => l'
      | _ => LBound i
      end
  | _ => l
  end.

Definition open_bound_ty (σ : list (option lifetime)) (T : Ty) : Ty :=
  map_lifetimes_ty (open_bound_lifetime σ) T.

Definition open_bound_outlives (σ : list (option lifetime)) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (open_bound_lifetime σ a, open_bound_lifetime σ b)) Ω.

Definition contains_lbound_lifetime (l : lifetime) : bool :=
  match l with
  | LBound _ => true
  | _ => false
  end.

Definition contains_lbound_outlives (Ω : outlives_ctx) : bool :=
  existsb (fun '(a, b) => contains_lbound_lifetime a || contains_lbound_lifetime b) Ω.

Fixpoint contains_lbound_ty (T : Ty) : bool :=
  match T with
  | MkTy _ (TStruct _ lts args) =>
      existsb contains_lbound_lifetime lts || existsb contains_lbound_ty args
  | MkTy _ (TFn ts r) =>
      existsb contains_lbound_ty ts || contains_lbound_ty r
  | MkTy _ (TForall _ Ω body) =>
      contains_lbound_outlives Ω || contains_lbound_ty body
  | MkTy _ (TRef l _ t) =>
      contains_lbound_lifetime l || contains_lbound_ty t
  | _ => false
  end.
