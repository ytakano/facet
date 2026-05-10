From Facet.TypeSystem Require Import Types.
From Stdlib Require Import String ZArith.

Definition ident := string.

Inductive literal : Type :=
| LInt   : Z -> literal
| LFloat : string -> literal.

Inductive place : Type :=
| PVar : ident -> place.

Inductive expr : Type :=
| EUnit     : expr
| ELit      : literal -> expr
| EVar      : ident -> expr
| ELet      : mutability -> ident -> Ty -> expr -> expr -> expr
| ELetInfer : mutability -> ident -> expr -> expr -> expr
| ECall     : ident -> list expr -> expr
| EReplace  : place -> expr -> expr
| EDrop     : expr -> expr.

Record param : Type := MkParam {
  param_mutability : mutability;
  param_name       : ident;
  param_ty         : Ty
}.

Record fn_def : Type := MkFnDef {
  fn_name   : ident;
  fn_params : list param;
  fn_ret    : Ty;
  fn_body   : expr
}.

Definition Syntax := list fn_def.