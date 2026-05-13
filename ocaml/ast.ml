type name = string

type named_place =
  | NPVar of name
  | NPDeref of named_place

type named_expr =
  | NUnit
  | NLit    of TypeChecker.literal
  | NVar    of name
  | NLet    of TypeChecker.mutability * name * TypeChecker.ty option * named_expr * named_expr
  | NCall   of name * named_expr list
  | NReplace of named_place * named_expr
  | NAssign of named_place * named_expr
  | NBorrow of TypeChecker.ref_kind * named_place
  | NDeref  of named_expr
  | NDrop   of named_expr
  | NIf     of named_expr * named_expr * named_expr

type named_ty =
  | NTy of TypeChecker.usage * named_ty_core
and named_ty_core =
  | NTUnits
  | NTIntegers
  | NTFloats
  | NTBooleans
  | NTNamed of string
  | NTFn of TypeChecker.ty list * TypeChecker.ty
  | NTForall of Big_int_Z.big_int * (TypeChecker.lifetime * TypeChecker.lifetime) list * TypeChecker.ty
  | NTRef of string option * TypeChecker.ref_kind * named_ty

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
