
type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

val eqb : bool -> bool -> bool

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

type ident = string

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

val infer : fn_def list -> ctx -> expr -> (ty, ctx) prod option
