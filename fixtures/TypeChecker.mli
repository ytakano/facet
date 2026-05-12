
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
 end

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type lifetime =
| LStatic
| LVar of Big_int_Z.big_int

val lifetime_eqb : lifetime -> lifetime -> bool

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
| TBooleans
| TNamed of string
| TFn of 'a list * 'a
| TRef of lifetime * ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

val ty_usage : ty -> usage

val ty_core : ty -> ty typeCore

type ident = string * Big_int_Z.big_int

val ident_eqb : ident -> ident -> bool

type literal =
| LInt of Big_int_Z.big_int
| LFloat of string
| LBool of bool

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
| EAssign of place * expr
| EDrop of expr
| EIf of expr * expr * expr

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_params : param list; fn_ret : ty;
                fn_body : expr }

type syntax = fn_def list

type ctx_entry = ((ident * ty) * bool) * mutability

type ctx = ctx_entry list

val param_ctx_entry : param -> ctx_entry

val params_ctx : param list -> ctx

val usage_max : usage -> usage -> usage

val ctx_merge : ctx -> ctx -> ctx option

val usage_eqb : usage -> usage -> bool

val usage_sub_bool : usage -> usage -> bool

val ref_kind_eqb : ref_kind -> ref_kind -> bool

val ty_eqb : ty -> ty -> bool

val ty_core_eqb : ty typeCore -> ty typeCore -> bool

val ctx_lookup_b : ident -> ctx -> (ty * bool) option

val ctx_consume_b : ident -> ctx -> ctx option

val ctx_lookup_mut_b : ident -> ctx -> mutability option

val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx

val ctx_remove_b : ident -> ctx -> ctx

val ctx_check_ok : ident -> ty -> ctx -> bool

val lookup_fn_b : ident -> fn_def list -> fn_def option

type rename_env = (ident * ident) list

val lookup_rename : ident -> rename_env -> ident

val max_ident_index : string -> ident list -> Big_int_Z.big_int

val fresh_ident : ident -> ident list -> ident

val ctx_names : ctx -> ident list

val place_name : place -> ident

type infer_error =
| ErrUnknownVar of ident
| ErrAlreadyConsumed of ident
| ErrTypeMismatch of ty typeCore * ty typeCore
| ErrNotMutable of ident
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

val alpha_rename_expr : rename_env -> ident list -> expr -> expr * ident list

val alpha_rename_params :
  rename_env -> ident list -> param list -> (param list * rename_env) * ident
  list

val alpha_rename_fn_def : ident list -> fn_def -> fn_def * ident list

val alpha_rename_syntax_go : ident list -> syntax -> syntax * ident list

val alpha_rename_for_infer : ctx -> fn_def list -> expr -> fn_def list * expr

val infer_core : fn_def list -> ctx -> expr -> (ty * ctx) infer_result

val infer_body : fn_def list -> ctx -> expr -> (ty * ctx) infer_result

val params_ok_b : param list -> ctx -> bool

val infer : fn_def list -> fn_def -> (ty * ctx) infer_result

val check_program : fn_def list -> bool

val infer_direct : fn_def list -> fn_def -> (ty * ctx) infer_result
