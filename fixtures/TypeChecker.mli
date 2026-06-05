
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

val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

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

type 'a core_trait_ref = { core_trait_ref_name : string;
                           core_trait_ref_args : 'a list }

type 'a core_trait_bound = { core_bound_type_index : Big_int_Z.big_int;
                             core_bound_traits : 'a core_trait_ref list }

type 'a typeCore =
| TUnits
| TIntegers
| TFloats
| TBooleans
| TNamed of string
| TParam of Big_int_Z.big_int
| TStruct of string * lifetime list * 'a list
| TEnum of string * lifetime list * 'a list
| TFn of 'a list * 'a
| TClosure of lifetime * 'a list * 'a
| TForall of Big_int_Z.big_int * outlives_ctx * 'a
| TTypeForall of Big_int_Z.big_int * 'a core_trait_bound list * 'a
| TRef of lifetime * ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

val ty_usage : ty -> usage

val ty_core : ty -> ty typeCore

val ref_usage_ok_b : usage -> ref_kind -> bool

val apply_lt_lifetime : lifetime list -> lifetime -> lifetime

val apply_lt_outlives : lifetime list -> outlives_ctx -> outlives_ctx

val map_core_trait_ref :
  ('a1 -> 'a2) -> 'a1 core_trait_ref -> 'a2 core_trait_ref

val map_core_trait_bound :
  ('a1 -> 'a2) -> 'a1 core_trait_bound -> 'a2 core_trait_bound

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
| EMakeClosure of ident * ident list
| EPlace of place
| ECall of ident * expr list
| ECallGeneric of ident * ty list * expr list
| ECallExpr of expr * expr list
| ECallExprGeneric of expr * ty list * expr list
| EStruct of string * lifetime list * ty list * (string * expr) list
| EEnum of string * string * lifetime list * ty list * expr list
| EMatch of expr * ((string * ident list) * expr) list
| EReplace of place * expr
| EAssign of place * expr
| EBorrow of ref_kind * place
| EDeref of expr
| EDrop of expr
| EIf of expr * expr * expr

val expr_as_place : expr -> place option

val match_branch_name : ((string * ident list) * expr) -> string

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type trait_ref = { trait_ref_name : string; trait_ref_args : ty list }

type trait_bound = { bound_type_index : Big_int_Z.big_int;
                     bound_traits : trait_ref list }

type fn_def = { fn_name : ident; fn_lifetimes : Big_int_Z.big_int;
                fn_outlives : outlives_ctx; fn_captures : param list;
                fn_params : param list; fn_ret : ty; fn_body : expr;
                fn_type_params : Big_int_Z.big_int;
                fn_bounds : trait_bound list }

type syntax = fn_def list

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

val place_resolved_write_direct_parent_b : place -> bool

val place_suffix_path : place -> field_path

type field_def = { field_name : string; field_mutability : mutability;
                   field_ty : ty }

type struct_def = { struct_name : string;
                    struct_lifetimes : Big_int_Z.big_int;
                    struct_type_params : Big_int_Z.big_int;
                    struct_bounds : trait_bound list;
                    struct_fields : field_def list }

type enum_variant_def = { enum_variant_name : string;
                          enum_variant_fields : ty list }

type enum_def = { enum_name : string; enum_lifetimes : Big_int_Z.big_int;
                  enum_type_params : Big_int_Z.big_int;
                  enum_bounds : trait_bound list;
                  enum_variants : enum_variant_def list }

type trait_def = { trait_name : string;
                   trait_type_params : Big_int_Z.big_int;
                   trait_bounds : trait_bound list }

type impl_def = { impl_lifetimes : Big_int_Z.big_int;
                  impl_type_params : Big_int_Z.big_int;
                  impl_trait_name : string; impl_trait_args : ty list;
                  impl_for_ty : ty }

type global_env = { env_structs : struct_def list; env_enums : enum_def list;
                    env_traits : trait_def list; env_impls : impl_def list;
                    env_local_bounds : trait_bound list; env_fns : fn_def list }

val global_env_with_local_bounds :
  global_env -> trait_bound list -> global_env

val core_trait_ref_of_trait_ref : trait_ref -> ty core_trait_ref

val core_trait_bound_of_trait_bound : trait_bound -> ty core_trait_bound

val trait_ref_of_core_trait_ref : ty core_trait_ref -> trait_ref

val trait_bound_of_core_trait_bound : ty core_trait_bound -> trait_bound

val trait_bounds_of_core_trait_bounds :
  ty core_trait_bound list -> trait_bound list

val lookup_struct_in : string -> struct_def list -> struct_def option

val lookup_struct : string -> global_env -> struct_def option

val lookup_enum_in : string -> enum_def list -> enum_def option

val lookup_enum : string -> global_env -> enum_def option

val lookup_enum_variant :
  string -> enum_variant_def list -> enum_variant_def option

val lookup_field : string -> field_def list -> field_def option

val lookup_trait_in : string -> trait_def list -> trait_def option

val lookup_trait : string -> global_env -> trait_def option

val usage_max_decl : usage -> usage -> usage

val subst_type_params_ty : ty list -> ty -> ty

val subst_type_params_expr : ty list -> expr -> expr

val instantiate_struct_field_ty : lifetime list -> ty list -> field_def -> ty

val instantiate_enum_variant_field_ty : lifetime list -> ty list -> ty -> ty

val usage_max_ty_list : ty list -> usage

val usage_max_enum_variants : enum_variant_def list -> usage

val instantiate_enum_ty : enum_def -> lifetime list -> ty list -> ty

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

val fn_body_params : fn_def -> param list

val fn_binding_params : fn_def -> param list

val fn_body_ctx : fn_def -> ctx

val usage_max : usage -> usage -> usage

val closure_capture_usage : ty list -> usage

val ctx_merge : ctx -> ctx -> ctx option

val lookup_expr_branch :
  string -> ((string * ident list) * expr) list -> expr option

val lookup_expr_branch_binders :
  string -> ((string * ident list) * expr) list -> ident list option

val fn_signature_ty_with_usage : usage -> fn_def -> ty

val closure_value_ty_at : lifetime -> fn_def -> ty list -> ty

val fn_value_ty : fn_def -> ty

val place_root : place -> ident

val apply_lt_param : lifetime list -> param -> param

val apply_lt_params : lifetime list -> param list -> param list

val apply_type_param : ty list -> param -> param

val apply_type_params : ty list -> param list -> param list

val subst_type_params_ctx_entry : ty list -> ctx_entry -> ctx_entry

val subst_type_params_ctx : ty list -> ctx -> ctx

val expr_ref_root : expr -> ident option

type rename_env = (ident * ident) list

val lookup_rename : ident -> rename_env -> ident

val max_ident_index : string -> ident list -> Big_int_Z.big_int

val fresh_ident : ident -> ident list -> ident

val ctx_names : ctx -> ident list

val place_name : place -> ident

val expr_names : expr -> ident list

val free_vars_expr : expr -> ident list

val param_names : param list -> ident list

val rename_place : rename_env -> place -> place

val alpha_rename_idents :
  rename_env -> ident list -> ident list -> (ident list * rename_env) * ident
  list

val alpha_rename_expr : rename_env -> ident list -> expr -> expr * ident list

val alpha_rename_params :
  rename_env -> ident list -> param list -> (param list * rename_env) * ident
  list

val alpha_rename_fn_def : ident list -> fn_def -> fn_def * ident list

val alpha_rename_syntax_go : ident list -> syntax -> syntax * ident list

val alpha_rename_syntax : syntax -> syntax

type root_atom =
| RStore of ident
| RParam of ident

type root_set = root_atom list

type root_env = (ident * root_set) list

val initial_root_env_for_params_origin : param list -> param list -> root_env

val initial_root_env_for_params : param list -> root_env

val initial_root_env_for_fn : fn_def -> root_env

val root_atom_eqb : root_atom -> root_atom -> bool

val root_set_union : root_set -> root_set -> root_set

val root_sets_union : root_set list -> root_set

val root_env_lookup : ident -> root_env -> root_set option

val root_env_add : ident -> root_set -> root_env -> root_env

val root_env_update : ident -> root_set -> root_env -> root_env

val root_env_remove : ident -> root_env -> root_env

val args_local_store_names_with :
  (expr -> ident list) -> expr list -> ident list

val fields_local_store_names_with :
  (expr -> ident list) -> (string * expr) list -> ident list

val match_branches_local_store_names_with :
  (expr -> ident list) -> ((string * ident list) * expr) list -> ident list

val expr_local_store_names : expr -> ident list

val args_local_store_names : expr list -> ident list

val root_provenance_place_name : place -> ident

val root_of_place : place -> root_set

val place_root_lookup : root_env -> place -> root_set option

val place_borrow_roots : root_env -> place -> root_set option

val same_store_root : ident -> root_set -> bool

val singleton_store_root : root_set -> ident option

val resolve_root_set_fuel :
  Big_int_Z.big_int -> root_env -> root_set -> root_set option

val resolve_root_set : root_env -> root_set -> root_set option

val place_resolved_roots : root_env -> place -> root_set option

val place_resolved_write_target : root_env -> place -> ident option

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

val capture_ref_free_ty_b_fuel : Big_int_Z.big_int -> global_env -> ty -> bool

val capture_ref_free_ty_b : global_env -> ty -> bool

val ctx_lookup_b : ident -> ctx -> (ty * bool) option

val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx

val ctx_remove_b : ident -> ctx -> ctx

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
| ErrEnumNotFound of string
| ErrVariantNotFound of string
| ErrNotAnEnum of ty typeCore
| ErrDuplicateVariant of string
| ErrMissingVariant of string
| ErrMatchPayloadUnsupported of string
| ErrFieldNotFound of string
| ErrDuplicateField of string
| ErrMissingField of string
| ErrTraitImplNotFound of string * ty
| ErrTraitImplAmbiguous of string * ty
| ErrTypeArgInferenceFailed
| ErrEndToEndSafetyGateFailed
| ErrGlobalNamesNotUnique
| ErrInFunction of ident * infer_error

val compatible_error : ty -> ty -> infer_error

val no_captures_b : fn_def -> bool

val trait_impl_error_with_args :
  global_env -> string -> ty list -> ty -> infer_error option

val instantiate_trait_ref : ty list -> trait_ref -> trait_ref

val subst_type_params_trait_ref : ty list -> trait_ref -> trait_ref

val subst_type_params_trait_bound : ty list -> trait_bound -> trait_bound

val subst_type_params_trait_bounds :
  ty list -> trait_bound list -> trait_bound list

val ty_list_eqb : ty list -> ty list -> bool

val trait_ref_eqb : trait_ref -> trait_ref -> bool

val local_bound_satisfies_trait :
  trait_bound list -> Big_int_Z.big_int -> trait_ref -> bool

val local_bounds_satisfy_trait_ref_for_ty :
  trait_bound list -> trait_ref -> ty -> bool

val check_trait_ref_for_ty :
  global_env -> trait_ref -> ty -> infer_error option

val check_trait_refs_for_ty :
  global_env -> trait_ref list -> ty -> infer_error option

val type_arg_list_set_nth :
  Big_int_Z.big_int -> ty option -> ty option list -> ty option list

val type_arg_subst_vec_add :
  ty option list -> Big_int_Z.big_int -> ty -> ty option list option

val infer_type_args_from_ty :
  Big_int_Z.big_int -> ty -> ty -> ty option list -> ty option list option

val infer_type_args_from_tys :
  Big_int_Z.big_int -> ty list -> ty list -> ty option list -> ty option list
  option

val infer_type_args_from_params :
  param list -> ty list -> ty option list -> ty option list option

val finalize_type_args : ty option list -> ty list option

val infer_call_type_args_expected :
  fn_def -> ty list -> ty option -> ty list option

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

val complete_bound_sigma_with_vars_from :
  Big_int_Z.big_int -> Big_int_Z.big_int -> lifetime option list -> lifetime
  option list

val complete_bound_sigma_with_vars :
  Big_int_Z.big_int -> lifetime option list -> lifetime option list

val check_args : outlives_ctx -> ty list -> param list -> infer_error option

val check_arg_tys : outlives_ctx -> ty list -> ty list -> infer_error option

type 'a infer_result =
| Infer_ok of 'a
| Infer_err of infer_error

val infer_if_bool :
  bool -> 'a1 infer_result -> 'a1 infer_result -> 'a1 infer_result

val tys_depth : ty list -> Big_int_Z.big_int

val infer_type_forall_args :
  Big_int_Z.big_int -> ty list -> ty list -> ty list option

val check_type_forall_bounds :
  global_env -> ty core_trait_bound list -> ty list -> infer_error option

val infer_type_forall_call_env :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound list
  -> ty -> ty list -> ty infer_result

val infer_type_forall_call_env_elab :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound list
  -> ty -> ty list -> (ty list * ty) infer_result

val shared_ref_lifetime_of_ty : ty -> lifetime option

val collect_shared_ref_lifetimes : ty list -> lifetime list

val all_outlive_b : outlives_ctx -> lifetime list -> lifetime -> bool

val find_closure_env_lifetime :
  outlives_ctx -> lifetime list -> lifetime list -> lifetime option

val infer_closure_env_lifetime :
  outlives_ctx -> ty list -> lifetime infer_result

val closure_capture_allowed_b :
  global_env -> outlives_ctx -> lifetime -> ty -> bool

val closure_captures_allowed_b :
  global_env -> outlives_ctx -> lifetime -> ty list -> bool

val lookup_field_b : string -> (string * expr) list -> expr option

val has_field_b : string -> (string * expr) list -> bool

val first_duplicate_field : (string * expr) list -> string option

val first_unknown_field :
  (string * expr) list -> field_def list -> string option

val first_missing_field :
  field_def list -> (string * expr) list -> string option

val lookup_branch_b :
  string -> ((string * ident list) * expr) list -> expr option

val has_branch_b : string -> ((string * ident list) * expr) list -> bool

val first_duplicate_branch :
  ((string * ident list) * expr) list -> string option

val first_unknown_variant_branch :
  ((string * ident list) * expr) list -> enum_variant_def list -> string
  option

val first_missing_variant_branch :
  enum_variant_def list -> ((string * ident list) * expr) list -> string
  option

val first_payload_binder_branch :
  ((string * ident list) * expr) list -> string option

val first_payload_variant : enum_variant_def list -> string option

val first_unsupported_match_payload :
  ((string * ident list) * expr) list -> enum_variant_def list -> string
  option

val usage_max_tys_nonempty : ty -> ty list -> usage

val ctx_merge_many : ctx -> ctx list -> ctx option

val match_binder_params : ident list -> ty list -> param list infer_result

val instantiate_enum_variant_field_tys :
  lifetime list -> ty list -> enum_variant_def -> ty list

val match_payload_params :
  ident list -> lifetime list -> ty list -> enum_variant_def -> param list
  infer_result

val ctx_add_params : param list -> ctx -> ctx

val ctx_remove_params : param list -> ctx -> ctx

val ident_in_b : ident -> ident list -> bool

val ident_nodup_b : ident list -> bool

val params_names_nodup_b : param list -> bool

val ctx_lookup_params_none_b : param list -> ctx -> bool

val unrestricted_unit_params_of_binders : ident list -> param list

val infer_place_env : global_env -> ctx -> place -> ty infer_result

val wf_outlives_b : region_ctx -> outlives_ctx -> bool

val outlives_constraints_hold_b : outlives_ctx -> outlives_ctx -> bool

val infer_hrt_call_env :
  outlives_ctx -> Big_int_Z.big_int -> Big_int_Z.big_int -> outlives_ctx ->
  ty -> ty list -> ty infer_result

val open_core_trait_bounds :
  lifetime option list -> ty core_trait_bound list -> ty core_trait_bound list

val infer_mixed_forall_call_env :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound list -> ty -> ty
  list -> ty infer_result

type sctx_entry = ctx_entry

type sctx = ctx

val sctx_of_ctx : ctx -> sctx

val ctx_of_sctx : sctx -> ctx

val mutability_eqb : mutability -> mutability -> bool

val field_path_eqb : field_path -> field_path -> bool

val field_paths_eqb : field_path list -> field_path list -> bool

val binding_state_eqb : binding_state -> binding_state -> bool

val sctx_entry_eqb : sctx_entry -> sctx_entry -> bool

val sctx_eqb : sctx -> sctx -> bool

val sctx_lookup : ident -> sctx -> (ty * binding_state) option

val sctx_lookup_mut : ident -> sctx -> mutability option

val check_make_closure_captures_sctx_base :
  global_env -> outlives_ctx -> sctx -> ident list -> param list -> ty list
  infer_result

val check_make_closure_captures_sctx_with_env :
  global_env -> outlives_ctx -> sctx -> ident list -> param list ->
  (lifetime * ty list) infer_result

val check_make_closure_captures_exact_sctx_with_env_base :
  global_env -> outlives_ctx -> sctx -> ident list -> param list -> ty list
  infer_result

val check_make_closure_captures_exact_sctx_with_env :
  global_env -> outlives_ctx -> sctx -> ident list -> param list ->
  (lifetime * ty list) infer_result

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

val sctx_add_params : param list -> sctx -> sctx

val sctx_remove_params : param list -> sctx -> sctx

val sctx_path_available : sctx -> ident -> field_path -> unit infer_result

val sctx_consume_path : sctx -> ident -> field_path -> sctx infer_result

val sctx_restore_path : sctx -> ident -> field_path -> sctx infer_result

val infer_place_sctx : global_env -> sctx -> place -> ty infer_result

val infer_place_type_sctx : global_env -> sctx -> place -> ty infer_result

val place_under_unique_ref_b : global_env -> sctx -> place -> bool

val writable_place_b : global_env -> sctx -> place -> bool

val place_resolved_write_writable_chain_b :
  global_env -> root_env -> sctx -> place -> bool

val consume_place_value :
  global_env -> sctx -> place -> ty -> sctx infer_result

val usage_max_tys : ty list -> usage

val instantiate_struct_instance_ty :
  struct_def -> lifetime list -> ty list -> ty

val auto_drop_paths_for_ty_fuel :
  Big_int_Z.big_int -> global_env -> ty -> field_path -> field_path list

val auto_drop_paths_for_ty : global_env -> ty -> field_path list

val filter_live_drop_paths :
  binding_state -> field_path list -> field_path list

val auto_drop_live_paths :
  global_env -> ident -> ty -> sctx -> field_path list

val infer_core_env_state_fuel :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  sctx -> expr -> (ty * sctx) infer_result

val infer_core_env :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
  (ty * ctx) infer_result

val infer_core_env_state_fuel_elab :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  sctx -> expr -> ((ty * sctx) * expr) infer_result

val infer_core_env_elab :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
  ((ty * ctx) * expr) infer_result

val root_set_eqb : root_set -> root_set -> bool

val root_env_eqb : root_env -> root_env -> bool

val roots_exclude_b : ident -> root_set -> bool

val roots_for_checked_result : global_env -> ty -> root_set -> root_set

val root_env_excludes_b : ident -> root_env -> bool

val roots_exclude_params_b : param list -> root_set -> bool

val root_env_excludes_params_b : param list -> root_env -> bool

val root_env_add_params_roots_same :
  param list -> root_set -> root_env -> root_env

val root_env_remove_match_params : param list -> root_env -> root_env

val root_env_lookup_params_none_b : param list -> root_env -> bool

val preservation_ready_expr_b : expr -> bool

val preservation_ready_args_b : expr list -> bool

val preservation_ready_fields_b : (string * expr) list -> bool

val provenance_ready_expr_b : expr -> bool

val provenance_ready_args_b : expr list -> bool

val provenance_ready_fields_b : (string * expr) list -> bool

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

val infer_core_env_state_fuel_roots_shadow_safe :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  root_env -> sctx -> expr -> (((ty * sctx) * root_env) * root_set)
  infer_result

val infer_core_env_state_fuel_roots_shadow_safe_checked :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  root_env -> sctx -> expr -> (((ty * sctx) * root_env) * root_set)
  infer_result

val infer_core_env_roots_shadow_safe :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> (((ty * ctx) * root_env) * root_set) infer_result

val infer_core_env_roots_shadow_safe_checked :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> (((ty * ctx) * root_env) * root_set) infer_result

val wf_params_b : region_ctx -> param list -> bool

val string_in : string -> string list -> bool

val duplicate_param_name_aux : string list -> param list -> ident option

val duplicate_param_name : param list -> ident option

val check_fn_binding_params : region_ctx -> fn_def -> infer_error option

val string_names_unique_b : string list -> bool

val fn_name_strings : fn_def list -> string list

val enum_variant_names : enum_def -> string list

val top_level_names : global_env -> string list

val top_level_names_unique_b : global_env -> bool

val enum_variants_unique_b : enum_def -> bool

val enum_variant_names_unique_b : global_env -> bool

val global_names_unique_b : global_env -> bool

val infer_env : global_env -> fn_def -> (ty * ctx) infer_result

val fn_with_body : fn_def -> expr -> fn_def

val infer_env_elab :
  global_env -> fn_def -> ((ty * ctx) * fn_def) infer_result

val infer_env_roots :
  global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
  infer_result

val infer_env_roots_shadow_safe :
  global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
  infer_result

val infer_env_roots_shadow_safe_checked :
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

val infer_full_env_elab :
  global_env -> fn_def -> ((ty * ctx) * fn_def) infer_result

val infer_full_env_roots :
  global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
  infer_result

val infer_full_env_roots_checked :
  global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
  infer_result

val alpha_normalize_global_env : global_env -> global_env

val infer_fns_env_elab : global_env -> fn_def list -> fn_def list infer_result

val infer_program_env_alpha_elab : global_env -> global_env infer_result

val fn_params_roots_exclude_b : param list -> root_set -> bool

val fn_params_root_env_excludes_b : param list -> root_env -> bool

val check_fn_root_shadow_summary : global_env -> fn_def -> bool

val check_env_root_shadow_summary : global_env -> bool

val check_fn_root_shadow_provenance_summary : global_env -> fn_def -> bool

val check_env_root_shadow_provenance_summary : global_env -> bool

val store_safe_function_value_call_args_b : global_env -> expr list -> bool

val direct_call_target_expr : expr -> ((ident * expr list) * expr) option

val generic_direct_call_target_expr :
  expr -> (((ident * ty list) * expr list) * expr) option

val let_bound_generic_direct_call_target_expr :
  expr -> ((((ident * ty list) * expr list) * ty) * expr) option

val if_literal_generic_direct_call_target_expr :
  expr -> (((((((bool * ident) * ty list) * expr list) * ident) * ty
  list) * expr list) * expr) option

val direct_call_ready_expr_b : expr -> bool

val check_fn_root_shadow_direct_call_provenance_summary :
  global_env -> fn_def -> bool

val local_fn_value_call_target_expr :
  expr -> ((ident * expr list) * expr) option

val local_fn_value_call_target_expr_with_binder :
  expr -> (((ident * ident) * expr list) * expr) option

val supported_non_type_generic_function_value_call_callee_ty_b : ty -> bool

val check_supported_non_type_generic_function_value_call_expr :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> bool

val check_fn_root_shadow_non_capturing_call_provenance_summary :
  global_env -> fn_def -> bool

val captured_call_target_expr :
  expr -> ((ident * ident list) * expr list) option

val args_free_vars_checker : expr list -> ident list

val local_captured_call_target_expr :
  expr -> (((((((ident * ident list) * expr
  list) * mutability) * ident) * ty) * expr) * expr) option

val check_fn_root_shadow_captured_callee_provenance_summary :
  global_env -> fn_def -> bool

val capture_root_bound :
  root_env -> ident list -> param list -> root_set option

val callee_hidden_capture_args_disjoint_b : fn_def -> expr list -> bool

val check_expr_root_shadow_captured_call_provenance_summary_fuel :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  root_env -> sctx -> expr -> bool

val check_expr_root_shadow_captured_call_provenance_summary :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> bool

val non_function_value_ty_b : ty -> bool

val check_expr_root_shadow_store_safe_narrow_summary_fuel :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  root_env -> sctx -> expr -> bool

val check_expr_root_shadow_store_safe_narrow_summary :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> bool

val check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel :
  Big_int_Z.big_int -> global_env -> fn_def -> ty list -> bool

val check_callee_body_root_shadow_store_safe_narrow_summary_instantiated :
  global_env -> fn_def -> ty list -> bool

val check_expr_root_shadow_store_safe_narrow_summary_checked_fuel :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  root_env -> sctx -> expr -> bool

val check_expr_root_shadow_store_safe_narrow_summary_checked :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx -> expr
  -> bool

val check_fn_root_shadow_generic_direct_store_safe_summary :
  global_env -> fn_def -> bool

val check_fn_root_shadow_captured_call_provenance_summary :
  global_env -> fn_def -> bool

val check_fn_root_shadow_captured_call_store_safe_summary :
  global_env -> fn_def -> bool

val check_env_root_shadow_direct_call_provenance_summary : global_env -> bool

val check_env_root_shadow_captured_call_provenance_summary :
  global_env -> bool

val check_fn_ordinary_safety_gate : global_env -> fn_def -> bool

val check_program_env : global_env -> bool

val check_program_env_alpha : global_env -> bool

val check_program_env_alpha_validated : global_env -> bool

val check_program_env_alpha_elab : global_env -> bool

val check_env_preservation_ready : global_env -> bool

val check_program_env_alpha_validated_root_shadow : global_env -> bool

val check_program_env_alpha_validated_root_shadow_provenance_summary :
  global_env -> bool

val check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary :
  global_env -> bool

val check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary :
  global_env -> bool

val check_program_env_alpha_validated_root_shadow_provenance :
  global_env -> bool

val infer_fn_env_end2end :
  global_env -> fn_def -> (((ty * ctx) * root_env) * root_set) infer_result

val infer_fns_env_end2end : global_env -> fn_def list -> unit infer_result

val infer_program_env_end2end : global_env -> global_env infer_result

val check_program_env_end2end : global_env -> bool

type raw_expr =
| RawUnit
| RawLit of literal
| RawVar of ident
| RawFn of ident
| RawPlace of place
| RawLet of mutability * ident * ty * raw_expr * raw_expr
| RawLetInfer of mutability * ident * raw_expr * raw_expr
| RawCall of ident * raw_expr list
| RawCallGeneric of ident * ty list * raw_expr list
| RawCallExpr of raw_expr * raw_expr list
| RawStruct of string * lifetime list * ty list * (string * raw_expr) list
| RawEnum of string * string * lifetime list * ty list * raw_expr list
| RawMatch of raw_expr * ((string * ident list) * raw_expr) list
| RawReplace of place * raw_expr
| RawAssign of place * raw_expr
| RawBorrow of ref_kind * place
| RawDeref of raw_expr
| RawDrop of raw_expr
| RawIf of raw_expr * raw_expr * raw_expr
| RawClosure of ident list * param list * ty * raw_expr
| RawCore of expr

type raw_fn_def = { raw_fn_name : ident;
                    raw_fn_lifetimes : Big_int_Z.big_int;
                    raw_fn_outlives : outlives_ctx;
                    raw_fn_params : param list; raw_fn_ret : ty;
                    raw_fn_body : raw_expr;
                    raw_fn_type_params : Big_int_Z.big_int;
                    raw_fn_bounds : trait_bound list }

val fn_stub_of_raw : raw_fn_def -> fn_def

val append_env_fns : global_env -> fn_def list -> global_env

val closure_elab_suffix : Big_int_Z.big_int -> string

val closure_elab_name : Big_int_Z.big_int -> ident

val generic_fn_value_wrapper_name : Big_int_Z.big_int -> ident

val wrapper_params_from_tys_from : Big_int_Z.big_int -> ty list -> param list

val wrapper_params_from_tys : ty list -> param list

val expr_vars_of_params : param list -> expr list

val infer_fn_value_type_args_expected :
  fn_def -> ty option -> ((ty list * ty list) * ty) option

val auto_drop_ret_name : Big_int_Z.big_int -> ident

val auto_drop_tmp_name : Big_int_Z.big_int -> ident

val place_of_path_from : place -> field_path -> place

val place_of_field_path : ident -> field_path -> place

val wrap_auto_drop_expr :
  ident -> field_path list -> expr -> Big_int_Z.big_int ->
  expr * Big_int_Z.big_int

val wrap_let_body_auto_drops :
  global_env -> ident -> ty -> sctx -> ty -> expr -> Big_int_Z.big_int ->
  expr * Big_int_Z.big_int

val closure_elab_capture_param :
  global_env -> outlives_ctx -> sctx -> ident -> param infer_result

val closure_elab_capture_params :
  global_env -> outlives_ctx -> sctx -> ident list -> param list infer_result

val infer_elaborated_expr_state :
  Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
  sctx -> expr -> sctx infer_result

val elaborate_raw_expr_fuel :
  Big_int_Z.big_int -> ty option -> global_env -> outlives_ctx ->
  Big_int_Z.big_int -> sctx -> Big_int_Z.big_int -> raw_expr ->
  (((expr * sctx) * fn_def list) * Big_int_Z.big_int) infer_result

val elaborate_raw_expr :
  global_env -> outlives_ctx -> Big_int_Z.big_int -> sctx -> raw_expr ->
  (expr * fn_def list) infer_result

val raw_fn_body_ctx : raw_fn_def -> ctx

val elaborate_raw_fns_fuel :
  Big_int_Z.big_int -> global_env -> fn_def list -> Big_int_Z.big_int ->
  raw_fn_def list -> (fn_def list * Big_int_Z.big_int) infer_result

val elaborate_raw_global_env :
  global_env -> raw_fn_def list -> global_env infer_result
