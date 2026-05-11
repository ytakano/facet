type name = string

type named_expr =
  | NUnit
  | NLit    of TypeChecker.literal
  | NVar    of name
  | NLet    of TypeChecker.mutability * name * TypeChecker.ty option * named_expr * named_expr
  | NCall   of name * named_expr list
  | NReplace of name * named_expr
  | NDrop   of named_expr

type named_param = {
  np_mutability : TypeChecker.mutability;
  np_name       : name;
  np_ty         : TypeChecker.ty;
}

type named_fn_def = {
  nf_name   : name;
  nf_params : named_param list;
  nf_ret    : TypeChecker.ty;
  nf_body   : named_expr;
}
