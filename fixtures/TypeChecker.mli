
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big_int_Z.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat : 'a1 -> Big_int_Z.big_int -> 'a1 list

val firstn : Big_int_Z.big_int -> 'a1 list -> 'a1 list

val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type lifetime =
| LStatic
| LVar of Big_int_Z.big_int

val lifetime_eqb : lifetime -> lifetime -> bool

type region_ctx = lifetime list

val outlives_b : lifetime -> lifetime -> bool

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

val apply_lt_lifetime : lifetime list -> lifetime -> lifetime

val apply_lt_ty : lifetime list -> ty -> ty

type ident = string * Big_int_Z.big_int

val ident_eqb : ident -> ident -> bool

type literal =
| LInt of Big_int_Z.big_int
| LFloat of string
| LBool of bool

type place =
| PVar of ident
| PDeref of place

type expr =
| EUnit
| ELit of literal
| EVar of ident
| ELet of mutability * ident * ty * expr * expr
| ELetInfer of mutability * ident * expr * expr
| ECall of ident * expr list
| EReplace of place * expr
| EAssign of place * expr
| EBorrow of ref_kind * place
| EDeref of expr
| EDrop of expr
| EIf of expr * expr * expr

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_lifetimes : Big_int_Z.big_int;
                fn_params : param list; fn_ret : ty; fn_body : expr }

type syntax = fn_def list

type ctx_entry = ((ident * ty) * bool) * mutability

type ctx = ctx_entry list

val param_ctx_entry : param -> ctx_entry

val params_ctx : param list -> ctx

val usage_max : usage -> usage -> usage

val ctx_merge : ctx -> ctx -> ctx option

val apply_lt_param : lifetime list -> param -> param

val apply_lt_params : lifetime list -> param list -> param list

type borrow_entry =
| BEShared of ident
| BEMut of ident

type borrow_state = borrow_entry list

val be_eqb : borrow_entry -> borrow_entry -> bool

val bs_eqb : borrow_state -> borrow_state -> bool

val bs_has_mut : ident -> borrow_state -> bool

val bs_has_any : ident -> borrow_state -> bool

val bs_remove_one : borrow_entry -> borrow_state -> borrow_state

val bs_remove_all : borrow_state -> borrow_state -> borrow_state

val bs_new_entries : borrow_state -> borrow_state -> borrow_state

val usage_eqb : usage -> usage -> bool

val usage_sub_bool : usage -> usage -> bool

val ref_kind_eqb : ref_kind -> ref_kind -> bool

val ty_eqb : ty -> ty -> bool

val ty_core_eqb : ty typeCore -> ty typeCore -> bool

val ty_compatible_b : ty -> ty -> bool

val ctx_lookup_b : ident -> ctx -> (ty * bool) option

val ctx_consume_b : ident -> ctx -> ctx option

val ctx_lookup_mut_b : ident -> ctx -> mutability option

val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx

val ctx_remove_b : ident -> ctx -> ctx

val ctx_check_ok : ident -> ty -> ctx -> bool

val lookup_fn_b : ident -> fn_def list -> fn_def option

val mk_region_ctx : Big_int_Z.big_int -> region_ctx

val wf_lifetime_b : region_ctx -> lifetime -> bool

val wf_type_b : region_ctx -> ty -> bool

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
| ErrImmutableBorrow of ident
| ErrNotAReference of ty typeCore
| ErrBorrowConflict of ident
| ErrLifetimeLeak
| ErrLifetimeConflict

val compatible_error : ty -> ty -> infer_error

val list_set_nth : Big_int_Z.big_int -> 'a1 -> 'a1 list -> 'a1 list

val lt_subst_vec_add :
  lifetime option list -> Big_int_Z.big_int -> lifetime -> lifetime option
  list option

val unify_lt :
  Big_int_Z.big_int -> lifetime option list -> ty -> ty -> lifetime option
  list option

val finalize_subst : lifetime option list -> lifetime list

val build_sigma :
  Big_int_Z.big_int -> lifetime option list -> ty list -> param list ->
  lifetime option list option

val check_args : ty list -> param list -> infer_error option

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

val infer_core :
  fn_def list -> Big_int_Z.big_int -> ctx -> expr -> (ty * ctx) infer_result

val infer_body :
  fn_def list -> Big_int_Z.big_int -> ctx -> expr -> (ty * ctx) infer_result

val params_ok_b : param list -> ctx -> bool

val wf_params_b : region_ctx -> param list -> bool

val infer : fn_def list -> fn_def -> (ty * ctx) infer_result

val check_program : fn_def list -> bool

val borrow_check :
  fn_def list -> borrow_state -> ctx -> expr -> borrow_state infer_result

val infer_full : fn_def list -> fn_def -> (ty * ctx) infer_result

val infer_direct : fn_def list -> fn_def -> (ty * ctx) infer_result
