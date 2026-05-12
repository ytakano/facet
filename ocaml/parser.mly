%{
open Ast
open TypeChecker

type stmt_item =
  | LetStmt of mutability * name * ty option * named_expr
  | ExprStmt of named_expr

let desugar_stmt item cont =
  match item with
  | LetStmt (m, x, ty_opt, e) -> NLet (m, x, ty_opt, e, cont)
  | ExprStmt e                -> NLet (MImmutable, "_", None, e, cont)

(* Mutable state for lifetime name resolution within the current fn_def *)
let current_lifetimes : string list ref = ref []

let resolve_lt_name (name : string) : Big_int_Z.big_int =
  let rec aux i = function
    | [] -> failwith (Printf.sprintf "undefined lifetime '%s" name)
    | h :: _ when h = name -> Big_int_Z.big_int_of_int i
    | _ :: t -> aux (i+1) t
  in
  aux 0 !current_lifetimes
%}

%token KW_FN KW_LET KW_IN KW_MUT KW_DROP KW_REPLACE
%token KW_AFFINE KW_LINEAR KW_UNRESTRICTED KW_ISIZE KW_F64
%token KW_IF KW_ELSE KW_TRUE KW_FALSE KW_BOOL
%token LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE
%token ARROW AMP STAR
%token COMMA COLON EQUAL SEMI UNDERSCORE
%token <string> ID
%token <string> LIFETIME
%token <Big_int_Z.big_int> INT_LIT
%token <string> FLOAT_LIT
%token EOF

%start <Ast.named_fn_def list> program

%%

program:
  | defs = list(fn_def); EOF { defs }

fn_def:
  | KW_FN; name = ID; lt_names = opt_lifetime_params;
    LPAREN; ps = params; RPAREN;
    ARROW; ret = ty; LBRACE; body = block; RBRACE
    { { nf_name = name; nf_lifetime_names = lt_names;
        nf_params = ps; nf_ret = ret; nf_body = body } }

opt_lifetime_params:
  | { current_lifetimes := []; [] }
  | LANGLE; names = separated_nonempty_list(COMMA, lifetime_name); RANGLE
    { current_lifetimes := names; names }

lifetime_name:
  | lt = LIFETIME { lt }

params:
  | { [] }
  | ps = separated_nonempty_list(COMMA, param) { ps }

param:
  | m = opt_mut; name = ID; COLON; t = ty
    { { np_mutability = m; np_name = name; np_ty = t } }

opt_mut:
  | { MImmutable }
  | KW_MUT { MMutable }

(* A block is a sequence of stmts followed by an optional final expression.
   Right-recursive to avoid shift/reduce conflicts. *)
block:
  | e = expr { e }
  | s = stmt; rest = block_tail { desugar_stmt s rest }

(* After consuming at least one stmt, we may have:
   - nothing (=> NUnit, only when RBRACE follows)
   - another stmt
   - a final expr  *)
block_tail:
  | { NUnit }
  | e = expr { e }
  | s = stmt; rest = block_tail { desugar_stmt s rest }

(* A statement is a let-binding or expression followed by semicolon.
   atom_expr is used for expr-stmts to avoid S/R conflicts with inline let. *)
stmt:
  | s = let_stmt; SEMI { s }
  | e = atom_expr; SEMI { ExprStmt e }

let_stmt:
  | KW_LET; m = opt_mut; x = var_name; COLON; t = ty; EQUAL; e = expr
    { LetStmt (m, x, Some t, e) }
  | KW_LET; m = opt_mut; x = var_name; EQUAL; e = expr
    { LetStmt (m, x, None, e) }

var_name:
  | x = ID     { x }
  | UNDERSCORE { "_" }

(* Full expressions include inline let-bindings *)
expr:
  | e = atom_expr { e }
  | KW_LET; m = opt_mut; x = var_name; COLON; t = ty; EQUAL;
    e1 = expr; KW_IN; e2 = expr
    { NLet (m, x, Some t, e1, e2) }
  | KW_LET; m = opt_mut; x = var_name; EQUAL; e1 = expr; KW_IN; e2 = expr
    { NLet (m, x, None, e1, e2) }

(* Atomic expressions — no inline let; used for call args and expr-stmts *)
atom_expr:
  | LPAREN; RPAREN
    { NUnit }
  | n = INT_LIT
    { NLit (LInt n) }
  | f = FLOAT_LIT
    { NLit (LFloat f) }
  | KW_TRUE
    { NLit (LBool true) }
  | KW_FALSE
    { NLit (LBool false) }
  | x = ID
    { NVar x }
  | LPAREN; KW_DROP; e = expr; RPAREN
    { NDrop e }
  | LPAREN; KW_REPLACE; x = ID; e = atom_expr; RPAREN
    { NReplace (x, e) }
  | LPAREN; KW_REPLACE; STAR; x = ID; e = atom_expr; RPAREN
    { NReplaceDeref (x, e) }
  | LPAREN; x = ID; EQUAL; e = atom_expr; RPAREN
    { NAssign (x, e) }
  | LPAREN; AMP; x = ID; RPAREN
    { NBorrow (RShared, x) }
  | LPAREN; AMP; KW_MUT; x = ID; RPAREN
    { NBorrow (RUnique, x) }
  | LPAREN; AMP; STAR; x = ID; RPAREN
    { NReBorrow (RShared, x) }
  | LPAREN; AMP; KW_MUT; STAR; x = ID; RPAREN
    { NReBorrow (RUnique, x) }
  | LPAREN; STAR; x = ID; EQUAL; e = atom_expr; RPAREN
    { NAssignDeref (x, e) }
  | LPAREN; STAR; e = expr; RPAREN
    { NDeref e }
  | LPAREN; f = ID; args = list(atom_expr); RPAREN
    { NCall (f, args) }
  | KW_IF; cond = atom_expr; LBRACE; then_e = block; RBRACE;
    KW_ELSE; LBRACE; else_e = block; RBRACE
    { NIf (cond, then_e, else_e) }
  | KW_IF; cond = atom_expr; LBRACE; then_e = block; RBRACE
    { NIf (cond, then_e, NUnit) }

ty:
  | KW_AFFINE;       c = ty_core { MkTy (UAffine,       c) }
  | KW_LINEAR;       c = ty_core { MkTy (ULinear,       c) }
  | KW_UNRESTRICTED; c = ty_core { MkTy (UUnrestricted, c) }

ty_core:
  | KW_ISIZE { TIntegers }
  | KW_F64   { TFloats }
  | KW_BOOL  { TBooleans }
  | LPAREN; RPAREN { TUnits }
  | AMP; t = ty { TRef (LVar Big_int_Z.zero_big_int, RShared, t) }
  | AMP; KW_MUT; t = ty { TRef (LVar Big_int_Z.zero_big_int, RUnique, t) }
  | AMP; lt = LIFETIME; t = ty { TRef (LVar (resolve_lt_name lt), RShared, t) }
  | AMP; lt = LIFETIME; KW_MUT; t = ty { TRef (LVar (resolve_lt_name lt), RUnique, t) }
  | KW_FN; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty
    { TFn (ts, ret) }

ty_list:
  | { [] }
  | ts = separated_nonempty_list(COMMA, ty) { ts }
