
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big_int_Z.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val tail_add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val tail_addmul :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val tail_mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val of_uint_acc : uint -> Big_int_Z.big_int -> Big_int_Z.big_int

val of_uint : uint -> Big_int_Z.big_int

val of_hex_uint_acc : uint0 -> Big_int_Z.big_int -> Big_int_Z.big_int

val of_hex_uint : uint0 -> Big_int_Z.big_int

val of_num_uint : uint1 -> Big_int_Z.big_int

val eqb0 : bool -> bool -> bool

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

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

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
| PField of place * string

type expr =
| EUnit
| ELit of literal
| EVar of ident
| ELet of mutability * ident * ty * expr * expr
| ELetInfer of mutability * ident * expr * expr
| EFn of ident
| EPlace of place
| ECall of ident * expr list
| ECallExpr of expr * expr list
| EStruct of string * lifetime list * ty list * (string * expr) list
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

type field_path = string list

val path_segment_eqb : string -> string -> bool

val path_eqb : field_path -> field_path -> bool

val path_prefix_b : field_path -> field_path -> bool

val path_conflict_b : field_path -> field_path -> bool

val path_conflicts_any_b : field_path -> field_path list -> bool

val remove_restored_paths : field_path -> field_path list -> field_path list

type binding_state = { st_consumed : bool; st_moved_paths : field_path list }

val binding_state_of_bool : bool -> binding_state

val binding_available_b : binding_state -> field_path -> bool

val state_consume_path : field_path -> binding_state -> binding_state

val state_restore_path : field_path -> binding_state -> binding_state

val place_path : place -> (ident * field_path) option

val place_suffix_path : place -> field_path

type field_def = { field_name : string; field_mutability : mutability;
                   field_ty : ty }

type trait_ref = { trait_ref_name : string; trait_ref_args : ty list }

type trait_bound = { bound_type_index : Big_int_Z.big_int;
                     bound_traits : trait_ref list }

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

val lookup_struct_in : string -> struct_def list -> struct_def option

val lookup_struct : string -> global_env -> struct_def option

val lookup_field : string -> field_def list -> field_def option

val lookup_trait_in : string -> trait_def list -> trait_def option

val lookup_trait : string -> global_env -> trait_def option

val subst_type_params_ty : ty list -> ty -> ty

val instantiate_struct_field_ty : lifetime list -> ty list -> field_def -> ty

val usage_eqb_decl : usage -> usage -> bool

val ref_kind_eqb_decl : ref_kind -> ref_kind -> bool

val lifetime_list_eqb_decl : lifetime list -> lifetime list -> bool

val outlives_ctx_eqb_decl : outlives_ctx -> outlives_ctx -> bool

val ty_eqb_decl : ty -> ty -> bool

type type_subst = ty option list

type lifetime_subst = lifetime option list

val repeat_none : Big_int_Z.big_int -> 'a1 option list

val list_set_nth : Big_int_Z.big_int -> 'a1 -> 'a1 list -> 'a1 list

val bind_type_param :
  Big_int_Z.big_int -> ty -> type_subst -> type_subst option

val bind_lifetime_param :
  Big_int_Z.big_int -> lifetime -> lifetime_subst -> lifetime_subst option

type impl_match_state = type_subst * lifetime_subst

val match_lifetime :
  Big_int_Z.big_int -> lifetime -> lifetime -> impl_match_state ->
  impl_match_state option

val match_lifetimes :
  Big_int_Z.big_int -> lifetime list -> lifetime list -> impl_match_state ->
  impl_match_state option

val match_ty :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> ty -> ty ->
  impl_match_state -> impl_match_state option

val match_tys :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> ty list ->
  ty list -> impl_match_state -> impl_match_state option

val ty_match_fuel : ty -> Big_int_Z.big_int

val impl_matches_b : string -> ty list -> ty -> impl_def -> bool

val matching_impls : string -> ty list -> ty -> impl_def list -> impl_def list

type ctx_entry = ((ident * ty) * binding_state) * mutability

type ctx = ctx_entry list

val ctx_lookup_state : ident -> ctx -> (ty * binding_state) option

val ctx_update_state :
  ident -> (binding_state -> binding_state) -> ctx -> ctx option

val ctx_lookup_mut : ident -> ctx -> mutability option

val ctx_add : ident -> ty -> mutability -> ctx -> ctx

val ctx_remove : ident -> ctx -> ctx

val param_ctx_entry : param -> ctx_entry

val params_ctx : param list -> ctx

val usage_max : usage -> usage -> usage

val ctx_merge : ctx -> ctx -> ctx option

val fn_value_ty : fn_def -> ty

val place_root : place -> ident

val apply_lt_param : lifetime list -> param -> param

val apply_lt_params : lifetime list -> param list -> param list

val expr_ref_root : expr -> ident option

val place_name : place -> ident

type root_set = ident list

type root_env = (ident * root_set) list

val root_set_union : root_set -> root_set -> root_set

val root_env_lookup : ident -> root_env -> root_set option

val root_env_add : ident -> root_set -> root_env -> root_env

val root_env_update : ident -> root_set -> root_env -> root_env

val root_env_remove : ident -> root_env -> root_env

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

val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx

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
| ErrDuplicateParam of ident
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
| ErrStructNotFound of string
| ErrFieldNotFound of string
| ErrDuplicateField of string
| ErrMissingField of string
| ErrTraitImplNotFound of string * ty
| ErrTraitImplAmbiguous of string * ty

val compatible_error : ty -> ty -> infer_error

val trait_impl_error_with_args :
  global_env -> string -> ty list -> ty -> infer_error option

val instantiate_trait_ref : ty list -> trait_ref -> trait_ref

val check_trait_ref_for_ty :
  global_env -> trait_ref -> ty -> infer_error option

val check_trait_refs_for_ty :
  global_env -> trait_ref list -> ty -> infer_error option

val check_struct_bounds :
  global_env -> trait_bound list -> ty list -> infer_error option

val list_set_nth0 : Big_int_Z.big_int -> 'a1 -> 'a1 list -> 'a1 list

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

val lookup_field_b : string -> (string * expr) list -> expr option

val has_field_b : string -> (string * expr) list -> bool

val first_duplicate_field : (string * expr) list -> string option

val first_unknown_field :
  (string * expr) list -> field_def list -> string option

val first_missing_field :
  field_def list -> (string * expr) list -> string option

val infer_place_env : global_env -> ctx -> place -> ty infer_result

val wf_outlives_b : region_ctx -> outlives_ctx -> bool

val outlives_constraints_hold_b : outlives_ctx -> outlives_ctx -> bool

type sctx = ctx

val sctx_of_ctx : ctx -> sctx

val ctx_of_sctx : sctx -> ctx

val sctx_lookup : ident -> sctx -> (ty * binding_state) option

val sctx_lookup_mut : ident -> sctx -> mutability option

val sctx_add : ident -> ty -> mutability -> sctx -> sctx

val sctx_remove : ident -> sctx -> sctx

val sctx_update_state :
  ident -> (binding_state -> binding_state) -> sctx -> sctx option

val prefix_obligation_paths : field_path -> field_path list -> field_path list

val linear_obligation_paths_fuel :
  Big_int_Z.big_int -> global_env -> ty -> field_path list

val linear_obligation_paths : global_env -> ty -> field_path list

val moved_path_satisfies_obligation_b : field_path list -> field_path -> bool

val moved_paths_satisfy_obligations_b :
  field_path list -> field_path list -> bool

val linear_scope_ok_b : global_env -> ty -> binding_state -> bool

val sctx_check_ok : global_env -> ident -> ty -> sctx -> bool

val params_ok_sctx_b : global_env -> param list -> sctx -> bool

val params_ok_env_b : global_env -> param list -> ctx -> bool

val sctx_path_available : sctx -> ident -> field_path -> unit infer_result

val sctx_consume_path : sctx -> ident -> field_path -> sctx infer_result

val sctx_restore_path : sctx -> ident -> field_path -> sctx infer_result

val infer_place_sctx : global_env -> sctx -> place -> ty infer_result

val infer_place_type_sctx : global_env -> sctx -> place -> ty infer_result

val place_under_unique_ref_b : global_env -> sctx -> place -> bool

val writable_place_b : global_env -> sctx -> place -> bool

val consume_place_value :
  global_env -> sctx -> place -> ty -> sctx infer_result

val usage_max_tys : ty list -> usage

val instantiate_struct_instance_ty :
  struct_def -> lifetime list -> ty list -> ty

val infer_core_env_state_fuel :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  sctx -> expr -> (ty * sctx) infer_result

val infer_core_env :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
  (ty * ctx) infer_result

val root_set_eqb : root_set -> root_set -> bool

val root_env_eqb : root_env -> root_env -> bool

val roots_exclude_b : ident -> root_set -> bool

val root_env_excludes_b : ident -> root_env -> bool

val infer_place_roots :
  global_env -> sctx -> root_env -> place ->
  (((ty * ident) * field_path) * root_set) infer_result

val consume_direct_place_value_roots :
  global_env -> sctx -> root_env -> place -> ((ty * sctx) * root_set)
  infer_result

val infer_core_env_state_fuel_roots :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  root_env -> sctx -> expr -> (((ty * sctx) * root_env) * root_set)
  infer_result

val infer_core_env_roots :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> (((ty * ctx) * root_env) * root_set) infer_result

val wf_params_b : region_ctx -> param list -> bool

val string_in : string -> string list -> bool

val duplicate_param_name_aux : string list -> param list -> ident option

val duplicate_param_name : param list -> ident option

val infer_env : global_env -> fn_def -> (ty * ctx) infer_result

val infer_env_roots :
  global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
  infer_result

type path_borrow_entry =
| PBShared of ident * field_path
| PBMut of ident * field_path

type path_borrow_state = path_borrow_entry list

val pbe_target_eqb : ident -> field_path -> path_borrow_entry -> bool

val pbs_has_mut : ident -> field_path -> path_borrow_state -> bool

val pbs_has_any : ident -> field_path -> path_borrow_state -> bool

val borrow_target_of_place : place -> ident * field_path

val path_borrow_entry_eqb : path_borrow_entry -> path_borrow_entry -> bool

val pbs_remove_one :
  path_borrow_entry -> path_borrow_state -> path_borrow_state

val pbs_remove_all :
  path_borrow_state -> path_borrow_state -> path_borrow_state

val pbs_new_entries :
  path_borrow_state -> path_borrow_state -> path_borrow_state

val pbs_eqb : path_borrow_state -> path_borrow_state -> bool

val pbs_access_allowed_b :
  ident -> field_path -> path_borrow_state -> ty -> bool

val borrow_check_place_access :
  global_env -> path_borrow_state -> ctx -> place -> unit infer_result

val borrow_check_env :
  global_env -> path_borrow_state -> ctx -> expr -> path_borrow_state
  infer_result

val infer_full_env : global_env -> fn_def -> (ty * ctx) infer_result

val infer_full_env_roots :
  global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
  infer_result

val check_program_env : global_env -> bool
