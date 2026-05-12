From Stdlib.Strings Require Import String.
From Stdlib Require Import List.
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
| TFn       : list A -> A -> TypeCore A
| TRef      : lifetime -> ref_kind -> A -> TypeCore A.

Arguments TUnits {A}.
Arguments TIntegers {A}.
Arguments TFloats {A}.
Arguments TBooleans {A}.
Arguments TNamed {A} _.
Arguments TFn {A} _ _.
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
  end.

Fixpoint apply_lt_ty (σ : list lifetime) (T : Ty) {struct T} : Ty :=
  match T with
  | MkTy u TUnits => MkTy u TUnits
  | MkTy u TIntegers => MkTy u TIntegers
  | MkTy u TFloats => MkTy u TFloats
  | MkTy u TBooleans => MkTy u TBooleans
  | MkTy u (TNamed s) => MkTy u (TNamed s)
  | MkTy u (TFn ts r) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TFn (map_lt ts) (apply_lt_ty σ r))
  | MkTy u (TRef l rk t) =>
      MkTy u (TRef (apply_lt_lifetime σ l) rk (apply_lt_ty σ t))
  end.


Definition apply_lt_outlives (σ : list lifetime) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (apply_lt_lifetime σ a, apply_lt_lifetime σ b)) Ω.
