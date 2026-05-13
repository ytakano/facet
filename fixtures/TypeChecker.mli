
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big_int_Z.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
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
| LBound of Big_int_Z.big_int

val lifetime_eqb : lifetime -> lifetime -> bool

type region_ctx = lifetime list

type outlives_ctx = (lifetime * lifetime) list

val outlives_direct_b : outlives_ctx -> lifetime -> lifetime -> bool

val outlives_b_fuel :
  Big_int_Z.big_int -> outlives_ctx -> lifetime -> lifetime -> bool

val outlives_b : outlives_ctx -> lifetime -> lifetime -> bool

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
| TParam of Big_int_Z.big_int
| TStruct of string * lifetime list * 'a list
| TFn of 'a list * 'a
| TForall of Big_int_Z.big_int * outlives_ctx * 'a
| TRef of lifetime * ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

val ty_usage : ty -> usage

val ty_core : ty -> ty typeCore

val ref_usage_ok_b : usage -> ref_kind -> bool

val apply_lt_lifetime : lifetime list -> lifetime -> lifetime

val apply_lt_outlives : lifetime list -> outlives_ctx -> outlives_ctx

val close_fn_lifetime : Big_int_Z.big_int -> lifetime -> lifetime

val apply_lt_ty : lifetime list -> ty -> ty

val map_lifetimes_ty : (lifetime -> lifetime) -> ty -> ty

val close_fn_ty : Big_int_Z.big_int -> ty -> ty

val close_fn_outlives : Big_int_Z.big_int -> outlives_ctx -> outlives_ctx

val open_bound_lifetime : lifetime option list -> lifetime -> lifetime

val open_bound_ty : lifetime option list -> ty -> ty

val open_bound_outlives : lifetime option list -> outlives_ctx -> outlives_ctx

val contains_lbound_lifetime : lifetime -> bool

val contains_lbound_outlives : outlives_ctx -> bool

val contains_lbound_ty : ty -> bool

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
| EFn of ident
| ECall of ident * expr list
| ECallExpr of expr * expr list
| EReplace of place * expr
| EAssign of place * expr
| EBorrow of ref_kind * place
| EDeref of expr
| EDrop of expr
| EIf of expr * expr * expr

val expr_as_place : expr -> place option

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_lifetimes : Big_int_Z.big_int;
                fn_outlives : outlives_ctx; fn_params : param list;
                fn_ret : ty; fn_body : expr }

type field_def = { field_name : string; field_mutability : mutability;
                   field_ty : ty }

type trait_bound = { bound_type_index : Big_int_Z.big_int;
                     bound_traits : string list }

type struct_def = { struct_name : string;
                    struct_lifetimes : Big_int_Z.big_int;
                    struct_type_params : Big_int_Z.big_int;
                    struct_bounds : trait_bound list;
                    struct_fields : field_def list }

type trait_def = { trait_name : string;
                   trait_type_params : Big_int_Z.big_int;
                   trait_bounds : trait_bound list }

type impl_def = { impl_lifetimes : Big_int_Z.big_int;
                  impl_type_params : Big_int_Z.big_int;
                  impl_trait_name : string; impl_trait_args : ty list;
                  impl_for_ty : ty }

type global_env = { env_structs : struct_def list;
                    env_traits : trait_def list; env_impls : impl_def list;
                    env_fns : fn_def list }

type ctx_entry = ((ident * ty) * bool) * mutability

type ctx = ctx_entry list

val param_ctx_entry : param -> ctx_entry

val params_ctx : param list -> ctx

val usage_max : usage -> usage -> usage

val ctx_merge : ctx -> ctx -> ctx option

val fn_value_ty : fn_def -> ty

val place_root : place -> ident

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

val expr_ref_root : expr -> ident option

val bs_remove_one : borrow_entry -> borrow_state -> borrow_state

val bs_remove_all : borrow_state -> borrow_state -> borrow_state

val bs_new_entries : borrow_state -> borrow_state -> borrow_state

val usage_eqb : usage -> usage -> bool

val usage_sub_bool : usage -> usage -> bool

val ref_kind_eqb : ref_kind -> ref_kind -> bool

val lifetime_pair_eqb : (lifetime * lifetime) -> (lifetime * lifetime) -> bool

val outlives_ctx_eqb : outlives_ctx -> outlives_ctx -> bool

val lifetime_list_eqb : lifetime list -> lifetime list -> bool

val ty_eqb : ty -> ty -> bool

val ty_core_eqb : ty typeCore -> ty typeCore -> bool

val ty_depth : ty -> Big_int_Z.big_int

val ty_compatible_args_contra_b_fuel :
  (outlives_ctx -> ty -> ty -> bool) -> outlives_ctx -> ty list -> ty list ->
  bool

val ty_compatible_b_fuel :
  Big_int_Z.big_int -> outlives_ctx -> ty -> ty -> bool

val ty_compatible_b : outlives_ctx -> ty -> ty -> bool

val ctx_lookup_b : ident -> ctx -> (ty * bool) option

val ctx_consume_b : ident -> ctx -> ctx option

val ctx_lookup_mut_b : ident -> ctx -> mutability option

val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx

val ctx_remove_b : ident -> ctx -> ctx

val ctx_check_ok : ident -> ty -> ctx -> bool

val lookup_fn_b : ident -> fn_def list -> fn_def option

val mk_region_ctx : Big_int_Z.big_int -> region_ctx

val wf_lifetime_at_b : Big_int_Z.big_int -> region_ctx -> lifetime -> bool

val wf_outlives_at_b : Big_int_Z.big_int -> region_ctx -> outlives_ctx -> bool

val wf_type_at_b : Big_int_Z.big_int -> region_ctx -> ty -> bool

val wf_lifetime_b : region_ctx -> lifetime -> bool

val wf_type_b : region_ctx -> ty -> bool

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
| ErrNotAFunction of ty typeCore
| ErrBorrowConflict of ident
| ErrLifetimeLeak
| ErrLifetimeConflict
| ErrHrtBoundUnsatisfied
| ErrHrtUnresolvedBound
| ErrHrtMonomorphicUsedBound
| ErrMalformedHrtBody of ty typeCore

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

val bound_subst_vec_add :
  lifetime option list -> Big_int_Z.big_int -> lifetime -> lifetime option
  list option

val unify_bound_lt :
  lifetime option list -> ty -> ty -> lifetime option list option

val build_bound_sigma :
  lifetime option list -> ty list -> ty list -> lifetime option list option

val check_args : outlives_ctx -> ty list -> param list -> infer_error option

val check_arg_tys : outlives_ctx -> ty list -> ty list -> infer_error option

type 'a infer_result =
| Infer_ok of 'a
| Infer_err of infer_error

val infer_place : ctx -> place -> ty infer_result

val wf_outlives_b : region_ctx -> outlives_ctx -> bool

val outlives_constraints_hold_b : outlives_ctx -> outlives_ctx -> bool

val infer_core :
  fn_def list -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
  (ty * ctx) infer_result

val infer_body :
  fn_def list -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
  (ty * ctx) infer_result

val params_ok_b : param list -> ctx -> bool

val wf_params_b : region_ctx -> param list -> bool

val infer : fn_def list -> fn_def -> (ty * ctx) infer_result

val check_program : fn_def list -> bool

val infer_env : global_env -> fn_def -> (ty * ctx) infer_result

val check_program_env : global_env -> bool

val borrow_check :
  fn_def list -> borrow_state -> ctx -> expr -> borrow_state infer_result

val infer_full : fn_def list -> fn_def -> (ty * ctx) infer_result

val infer_direct : fn_def list -> fn_def -> (ty * ctx) infer_result
