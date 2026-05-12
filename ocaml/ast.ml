type name = string

type named_expr =
  | NUnit
  | NLit    of TypeChecker.literal
  | NVar    of name
  | NLet    of TypeChecker.mutability * name * TypeChecker.ty option * named_expr * named_expr
  | NCall   of name * named_expr list
  | NReplace of name * named_expr
  | NAssign of name * named_expr
  | NBorrow of TypeChecker.ref_kind * name
  | NReplaceDeref of name * named_expr       (* write through mutable ref: replace *x e *)
  | NAssignDeref  of name * named_expr       (* assign through mutable ref: ( *x = e ) *)
  | NReBorrow     of TypeChecker.ref_kind * name  (* re-borrow through ref: & *x or &mut *x *)
  | NDeref  of named_expr
  | NDrop   of named_expr
  | NIf     of named_expr * named_expr * named_expr

type named_param = {
  np_mutability : TypeChecker.mutability;
  np_name       : name;
  np_ty         : TypeChecker.ty;
}

type named_fn_def = {
  nf_name           : name;
  nf_lifetime_names : string list;
  nf_params         : named_param list;
  nf_ret            : TypeChecker.ty;
  nf_body           : named_expr;
}
