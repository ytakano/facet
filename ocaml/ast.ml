type name = string

type named_place =
  | NPVar of name
  | NPDeref of named_place
  | NPField of named_place * name

type named_ty =
  | NTy of TypeChecker.usage * named_ty_core
and named_ty_core =
  | NTUnits
  | NTIntegers
  | NTFloats
  | NTBooleans
  | NTNamed of string * named_type_arg list
  | NTFn of named_ty list * named_ty
  | NTForall of Big_int_Z.big_int * (TypeChecker.lifetime * TypeChecker.lifetime) list * named_ty
  | NTRef of TypeChecker.lifetime option * TypeChecker.ref_kind * named_ty
and named_type_arg =
  | NTArgLifetime of TypeChecker.lifetime
  | NTArgTy of named_ty

type named_expr =
  | NUnit
  | NLit    of TypeChecker.literal
  | NVar    of name
  | NPlace  of named_place
  | NLet    of TypeChecker.mutability * name * named_ty option * named_expr * named_expr
  | NCall   of name * named_expr list
  | NStruct of name * named_type_arg list * (name * named_expr) list
  | NReplace of named_place * named_expr
  | NAssign of named_place * named_expr
  | NBorrow of TypeChecker.ref_kind * named_place
  | NDeref  of named_expr
  | NDrop   of named_expr
  | NIf     of named_expr * named_expr * named_expr

type named_param = {
  np_mutability : TypeChecker.mutability;
  np_name       : name;
  np_ty         : named_ty;
}

type named_fn_def = {
  nf_name           : name;
  nf_lifetime_names : string list;
  nf_outlives       : (TypeChecker.lifetime * TypeChecker.lifetime) list;
  nf_params         : named_param list;
  nf_ret            : named_ty;
  nf_body           : named_expr;
}

type named_generic_param =
  | NGLifetime of string
  | NGType of string

type named_trait_bound = {
  ntb_type_name : string;
  ntb_traits    : string list;
}

type named_field_def = {
  nfield_mutability : TypeChecker.mutability;
  nfield_name       : name;
  nfield_ty         : named_ty;
}

type named_struct_def = {
  ns_name     : name;
  ns_generics : named_generic_param list;
  ns_bounds   : named_trait_bound list;
  ns_fields   : named_field_def list;
}

type named_trait_def = {
  nt_name     : name;
  nt_generics : named_generic_param list;
  nt_bounds   : named_trait_bound list;
}

type named_impl_def = {
  ni_generics   : named_generic_param list;
  ni_trait_name : name;
  ni_trait_args : named_type_arg list;
  ni_for_ty     : named_ty;
}

type named_item =
  | NIFn of named_fn_def
  | NIStruct of named_struct_def
  | NITrait of named_trait_def
  | NIImpl of named_impl_def
