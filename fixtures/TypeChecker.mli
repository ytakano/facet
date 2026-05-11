
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val max : nat -> nat -> nat
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

type mutability =
| MImmutable
| MMutable

type usage =
| ULinear
| UAffine
| UUnrestricted

type ref_kind =
| RShared
| RUnique

type 'a typeCore =
| TUnits
| TIntegers
| TFloats
| TNamed of string
| TFn of 'a list * 'a
| TRef of ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

val ty_usage : ty -> usage

val ty_core : ty -> ty typeCore

type ident = (string, nat) prod

val ident_eqb : ident -> ident -> bool

type literal =
| LInt of z
| LFloat of string

type place = ident
  (* singleton inductive, whose constructor was PVar *)

type expr =
| EUnit
| ELit of literal
| EVar of ident
| ELet of mutability * ident * ty * expr * expr
| ELetInfer of mutability * ident * expr * expr
| ECall of ident * expr list
| EReplace of place * expr
| EDrop of expr

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_params : param list; fn_ret : ty;
                fn_body : expr }

type syntax = fn_def list

type ctx_entry = ((ident, ty) prod, bool) prod

type ctx = ctx_entry list

val usage_eqb : usage -> usage -> bool

val usage_sub_bool : usage -> usage -> bool

val ty_core_eqb : ty typeCore -> ty typeCore -> bool

val ctx_lookup_b : ident -> ctx -> (ty, bool) prod option

val ctx_consume_b : ident -> ctx -> ctx option

val ctx_add_b : ident -> ty -> ctx -> ctx

val ctx_remove_b : ident -> ctx -> ctx

val ctx_check_ok : ident -> ty -> ctx -> bool

val lookup_fn_b : ident -> fn_def list -> fn_def option

type rename_env = (ident, ident) prod list

val lookup_rename : ident -> rename_env -> ident

val max_ident_index : string -> ident list -> nat

val fresh_ident : ident -> ident list -> ident

val ctx_names : ctx -> ident list

val place_name : place -> ident

type infer_error =
| ErrUnknownVar of ident
| ErrAlreadyConsumed of ident
| ErrTypeMismatch of ty typeCore * ty typeCore
| ErrUsageMismatch of usage * usage
| ErrFunctionNotFound of ident
| ErrArityMismatch
| ErrContextCheckFailed
| ErrNotImplemented

type 'a infer_result =
| Infer_ok of 'a
| Infer_err of infer_error

val free_vars_expr : expr -> ident list

val param_names : param list -> ident list

val rename_place : rename_env -> place -> place

val alpha_rename_expr :
  rename_env -> ident list -> expr -> (expr, ident list) prod

val alpha_rename_params :
  rename_env -> ident list -> param list -> ((param list, rename_env) prod,
  ident list) prod

val alpha_rename_fn_def : ident list -> fn_def -> (fn_def, ident list) prod

val alpha_rename_syntax_go : ident list -> syntax -> (syntax, ident list) prod

val alpha_rename_for_infer :
  ctx -> fn_def list -> expr -> (fn_def list, expr) prod

val infer_core : fn_def list -> ctx -> expr -> (ty, ctx) prod infer_result

val infer : fn_def list -> ctx -> expr -> (ty, ctx) prod infer_result
