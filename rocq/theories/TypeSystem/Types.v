From Stdlib.Strings Require Import String.

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
| TNamed    : string -> TypeCore A
| TFn       : list A -> A -> TypeCore A
| TRef      : ref_kind -> A -> TypeCore A.

Arguments TUnits {A}.
Arguments TIntegers {A}.
Arguments TFloats {A}.
Arguments TNamed {A} _.
Arguments TFn {A} _ _.
Arguments TRef {A} _ _.

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
