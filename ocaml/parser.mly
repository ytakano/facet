%{
open Ast
open TypeChecker

type stmt_item =
  | LetStmt of mutability * name * named_ty option * named_expr
  | ExprStmt of named_expr

type fn_where_item =
  | FnWhereTrait of named_trait_bound
  | FnWhereOutlives of (TypeChecker.lifetime * TypeChecker.lifetime)

let desugar_stmt item cont =
  match item with
  | LetStmt (m, x, ty_opt, e) -> NLet (m, x, ty_opt, e, cont)
  | ExprStmt e                -> NLet (MImmutable, "_", None, e, cont)

let split_fn_where_items items =
  let add (bounds, outs) = function
    | FnWhereTrait b -> (bounds @ [b], outs)
    | FnWhereOutlives c -> (bounds, outs @ [c])
  in
  List.fold_left add ([], []) items

(* Mutable state for lifetime name resolution within the current fn_def *)
let current_lifetimes : string list ref = ref []
let current_hrt_lifetimes : string list ref = ref []

let check_unique_lifetimes names =
  let rec go seen = function
    | [] -> ()
    | x :: xs ->
      if List.mem x seen
      then failwith (Printf.sprintf "duplicate lifetime '%s" x)
      else go (x :: seen) xs
  in
  go [] names

let resolve_fn_lt_name (name : string) : Big_int_Z.big_int =
  let rec aux i = function
    | [] -> failwith (Printf.sprintf "undefined lifetime '%s" name)
    | h :: _ when h = name -> Big_int_Z.big_int_of_int i
    | _ :: t -> aux (i+1) t
  in
  aux 0 !current_lifetimes

let resolve_lifetime (name : string) : lifetime =
  if name = "static" then LStatic else
  let rec aux_bound i = function
    | [] -> None
    | h :: _ when h = name -> Some (LBound (Big_int_Z.big_int_of_int i))
    | _ :: t -> aux_bound (i+1) t
  in
  match aux_bound 0 !current_hrt_lifetimes with
  | Some l -> l
  | None -> LVar (resolve_fn_lt_name name)

let split_generics params =
  let rec go lts tys = function
    | [] -> (List.rev lts, List.rev tys)
    | NGLifetime lt :: rest -> go (lt :: lts) tys rest
    | NGType ty :: rest -> go lts (ty :: tys) rest
  in
  go [] [] params

let check_unique_type_params names =
  let rec go seen = function
    | [] -> ()
    | x :: xs ->
      if List.mem x seen
      then failwith (Printf.sprintf "duplicate type parameter %s" x)
      else go (x :: seen) xs
  in
  go [] names

let with_mixed_forall_params params f =
  let (lts, tys) = split_generics params in
  check_unique_lifetimes lts;
  check_unique_type_params tys;
  let prev = !current_hrt_lifetimes in
  current_hrt_lifetimes := lts;
  f lts tys prev

let install_generics params =
  let (lts, tys) = split_generics params in
  check_unique_lifetimes lts;
  check_unique_type_params tys;
  current_lifetimes := lts;
  params


let open_variant_lifetimes lts =
  check_unique_lifetimes lts;
  let prev = !current_lifetimes in
  current_lifetimes := lts @ prev;
  (lts, prev)

let close_variant_lifetimes prev =
  current_lifetimes := prev

let expr_of_place = function
  | NPVar x -> NVar x
  | p -> NPlace p

let split_constructor_path segments =
  match List.rev segments with
  | variant :: enum_rev when enum_rev <> [] -> (List.rev enum_rev, variant)
  | _ -> failwith "enum constructor path must include enum and variant"

%}

%token KW_FN KW_FOR KW_STRUCT KW_ENUM KW_TRAIT KW_IMPL KW_MATCH KW_MOD KW_PUB KW_USE KW_AS KW_LET KW_REC KW_AND KW_IN KW_MUT KW_DROP KW_REPLACE KW_CLOSURE
%token KW_AFFINE KW_LINEAR KW_UNRESTRICTED KW_ISIZE KW_F64
%token KW_IF KW_ELSE KW_TRUE KW_FALSE KW_BOOL KW_WHERE
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET LANGLE RANGLE
%token ARROW FATARROW AMP STAR
%token COMMA COLON DCOLON EQUAL SEMI UNDERSCORE DOT PLUS
%token <string> ID
%token <string> LIFETIME
%token <Big_int_Z.big_int> INT_LIT
%token <string> FLOAT_LIT
%token EOF

%start <Ast.named_item list> program

%%

program:
  | items = list(top_item); EOF { items }

top_item:
  | vis = visibility; f = fn_def { NIFn { f with nf_visibility = vis } }
  | vis = visibility; s = struct_def { NIStruct { s with ns_visibility = vis } }
  | vis = visibility; e = enum_def { NIEnum { e with ne_visibility = vis } }
  | vis = visibility; t = trait_def { NITrait { t with nt_visibility = vis } }
  | i = impl_def { NIImpl i }
  | u = use_def { let (path, alias) = u in NIUse (path, alias) }
  | vis = visibility; m = mod_file_def { NIModFile (vis, m) }
  | vis = visibility; m = mod_def { let (name, items) = m in NIMod (vis, name, items) }

visibility:
  | { VPrivate }
  | KW_PUB { VPublic }

mod_def:
  | KW_MOD; name = ID; LBRACE; items = list(top_item); RBRACE
    { (name, items) }

mod_file_def:
  | KW_MOD; name = ID; SEMI
    { name }

use_def:
  | KW_USE; target = path_name; alias = opt_use_alias; SEMI
    { (target, alias) }

opt_use_alias:
  | { None }
  | KW_AS; name = ID { Some name }

fn_def:
  | KW_FN; name = ID; generics = opt_generic_params;
    LPAREN; ps = params; RPAREN;
    ARROW; ret = signature_ty; where_clause = opt_fn_where_clause; LBRACE; body = block; RBRACE
    { let (bounds, outs) = where_clause in
      { nf_visibility = VPrivate; nf_name = name; nf_generics = generics; nf_bounds = bounds;
        nf_outlives = outs; nf_params = ps; nf_ret = ret; nf_body = body } }

struct_def:
  | KW_STRUCT; name = ID; generics = opt_generic_params;
    bounds = opt_trait_bounds; LBRACE; fields = separated_list(COMMA, struct_field); RBRACE
    { { ns_visibility = VPrivate; ns_name = name; ns_generics = generics; ns_bounds = bounds; ns_fields = fields } }

enum_def:
  | KW_ENUM; name = ID; generics = opt_generic_params;
    where_clause = opt_fn_where_clause; LBRACE; variants = separated_list(COMMA, enum_variant); RBRACE
    { let (bounds, outs) = where_clause in
      { ne_visibility = VPrivate; ne_name = name; ne_generics = generics; ne_bounds = bounds;
        ne_outlives = outs; ne_variants = variants } }

enum_variant:
  | name = ID
    { { nev_name = name; nev_lifetimes = []; nev_fields = [] } }
  | name = ID; LPAREN; fields = separated_list(COMMA, ty); RPAREN
    { { nev_name = name; nev_lifetimes = []; nev_fields = fields } }
  | name = ID; h = variant_lifetime_open; LPAREN; fields = separated_list(COMMA, ty); RPAREN
    { let (lts, prev) = h in
      close_variant_lifetimes prev;
      { nev_name = name; nev_lifetimes = lts; nev_fields = fields } }

variant_lifetime_open:
  | LANGLE; lts = separated_nonempty_list(COMMA, LIFETIME); RANGLE
    { open_variant_lifetimes lts }

trait_def:
  | KW_TRAIT; name = ID; generics = opt_generic_params; bounds = opt_trait_bounds; SEMI
    { { nt_visibility = VPrivate; nt_name = name; nt_generics = generics; nt_bounds = bounds;
        nt_items = [] } }
  | KW_TRAIT; name = ID; generics = opt_generic_params; bounds = opt_trait_bounds;
    LBRACE; items = list(trait_item); RBRACE
    { { nt_visibility = VPrivate; nt_name = name; nt_generics = generics; nt_bounds = bounds;
        nt_items = items } }

trait_item:
  | kw_type; name = ID; SEMI
    { NTIAssocTypeDecl name }
  | sig_ = method_sig; SEMI
    { NTIMethodSig sig_ }

method_sig:
  | KW_FN; name = ID; LPAREN; ps = surface_params; RPAREN; ARROW; ret = surface_ty
    { { nms_name = name; nms_params = ps; nms_ret = ret } }

impl_def:
  | KW_IMPL; generics = opt_generic_params; trait_name = path_name; trait_args = opt_type_args;
    KW_FOR; for_ty = ty; SEMI
    { { ni_generics = generics; ni_trait_name = trait_name;
        ni_trait_args = trait_args; ni_for_ty = for_ty; ni_items = [] } }
  | KW_IMPL; generics = opt_generic_params; trait_name = path_name; trait_args = opt_type_args;
    KW_FOR; for_ty = ty; LBRACE; items = list(impl_item); RBRACE
    { { ni_generics = generics; ni_trait_name = trait_name;
        ni_trait_args = trait_args; ni_for_ty = for_ty; ni_items = items } }

impl_item:
  | kw_type; name = ID; EQUAL; t = surface_ty; SEMI
    { NIIAssocTypeDef (name, t) }
  | KW_FN; name = ID; LPAREN; ps = surface_params; RPAREN; ARROW; ret = surface_ty;
    LBRACE; body = block; RBRACE
    { NIIMethodDef { nmd_name = name; nmd_params = ps; nmd_ret = ret; nmd_body = body } }

kw_type:
  | kw = ID
    { if kw = "type" then () else failwith (Printf.sprintf "expected type item, got %s" kw) }

opt_generic_params:
  | { current_lifetimes := []; [] }
  | LANGLE; params = separated_nonempty_list(COMMA, generic_param); RANGLE
    { install_generics params }

generic_param:
  | lt = LIFETIME { NGLifetime lt }
  | name = ID { NGType name }

opt_trait_bounds:
  | { [] }
  | KW_WHERE; bounds = separated_nonempty_list(COMMA, trait_bound) { bounds }

opt_fn_where_clause:
  | { ([], []) }
  | KW_WHERE; items = separated_nonempty_list(COMMA, fn_where_item)
    { split_fn_where_items items }

fn_where_item:
  | b = trait_bound { FnWhereTrait b }
  | c = outlives_constraint { FnWhereOutlives c }

trait_bound:
  | type_name = ID; COLON; traits = separated_nonempty_list(PLUS, trait_ref)
    { { ntb_type_name = type_name; ntb_traits = traits } }

trait_ref:
  | name = path_name; args = opt_type_args
    { { ntr_name = name; ntr_args = args } }

surface_trait_ref:
  | name = path_name; args = opt_surface_type_args
    { { nstr_name = name; nstr_args = args } }

struct_field:
  | m = opt_mut; name = ID; COLON; t = ty
    { { nfield_mutability = m; nfield_name = name; nfield_ty = t } }

outlives_constraint:
  | a = LIFETIME; COLON; b = LIFETIME
    { (resolve_lifetime a, resolve_lifetime b) }

params:
  | { [] }
  | ps = separated_nonempty_list(COMMA, param) { ps }

param:
  | m = opt_mut; name = ID; COLON; t = signature_ty
    { { np_mutability = m; np_name = name; np_ty = t } }

surface_params:
  | { [] }
  | ps = separated_nonempty_list(COMMA, surface_param) { ps }

surface_param:
  | m = opt_mut; name = ID; COLON; t = surface_ty
    { { nsp_mutability = m; nsp_name = name; nsp_ty = t } }

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
  | KW_LET; KW_REC; captures = opt_rec_captures; f = rec_fn_def; rest = list(rec_and_fn_def);
    KW_IN; body = expr
    { NLetRec (captures, f :: rest, body) }

rec_fn_def:
  | name = ID; LPAREN; ps = params; RPAREN; ARROW; ret = signature_ty;
    LBRACE; body = block; RBRACE
    { { nrf_name = name; nrf_params = ps; nrf_ret = ret; nrf_body = body } }

rec_and_fn_def:
  | KW_AND; f = rec_fn_def { f }

opt_rec_captures:
  | { [] }
  | LBRACKET; captures = separated_list(COMMA, ID); RBRACKET { captures }

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
  | name = ID; LBRACE; fields = separated_list(COMMA, struct_literal_field); RBRACE
    { NStruct ([name], [], fields) }
  | name = qualified_path; LBRACE; fields = separated_list(COMMA, struct_literal_field); RBRACE
    { NStruct (name, [], fields) }
  | ctor = qualified_path; LPAREN; payloads = separated_list(COMMA, atom_expr); RPAREN
    { let (enum_name, variant_name) = split_constructor_path ctor in
      NEnum (enum_name, [], variant_name, [], payloads) }
  | enum_name = ID; DCOLON; variant_name = ID;
    LANGLE; variant_args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    LPAREN; payloads = separated_list(COMMA, atom_expr); RPAREN
    { NEnum ([enum_name], [], variant_name, variant_args, payloads) }
  | enum_name = ID; LANGLE; args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    DCOLON; variant_name = ID; LPAREN; payloads = separated_list(COMMA, atom_expr); RPAREN
    { NEnum ([enum_name], args, variant_name, [], payloads) }
  | enum_name = qualified_path; LANGLE; args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    DCOLON; variant_name = ID; LPAREN; payloads = separated_list(COMMA, atom_expr); RPAREN
    { NEnum (enum_name, args, variant_name, [], payloads) }
  | enum_name = ID; LANGLE; args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    DCOLON; variant_name = ID; LANGLE; variant_args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    LPAREN; payloads = separated_list(COMMA, atom_expr); RPAREN
    { NEnum ([enum_name], args, variant_name, variant_args, payloads) }
  | enum_name = qualified_path; LANGLE; args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    DCOLON; variant_name = ID; LANGLE; variant_args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    LPAREN; payloads = separated_list(COMMA, atom_expr); RPAREN
    { NEnum (enum_name, args, variant_name, variant_args, payloads) }
  | name = ID; LANGLE; args = separated_nonempty_list(COMMA, type_arg); RANGLE;
    LBRACE; fields = separated_list(COMMA, struct_literal_field); RBRACE
    { NStruct ([name], args, fields) }
  | KW_MATCH; scrut = match_scrut; LBRACE; branches = match_branches; RBRACE
    { NMatch (scrut, branches) }
  | p = place
    { expr_of_place p }
  | LPAREN; KW_DROP; e = expr; RPAREN
    { NDrop e }
  | LPAREN; KW_REPLACE; p = place; e = atom_expr; RPAREN
    { NReplace (p, e) }
  | LPAREN; p = place; EQUAL; e = atom_expr; RPAREN
    { NAssign (p, e) }
  | LPAREN; AMP; p = place; RPAREN
    { NBorrow (RShared, p) }
  | LPAREN; AMP; KW_MUT; p = place; RPAREN
    { NBorrow (RUnique, p) }
  | LPAREN; STAR; e = expr; RPAREN
    { NDeref e }
  | LPAREN; LANGLE; self_ty = ty; KW_AS; trait = trait_ref; RANGLE;
    DCOLON; method_name = ID; args = list(atom_expr); RPAREN
    { NMethodCall (self_ty, trait, method_name, args) }
  | LPAREN; f = path_name; type_args = opt_type_args; args = list(atom_expr); RPAREN
    { NCall (f, type_args, args) }
  | KW_IF; cond = atom_expr; LBRACE; then_e = block; RBRACE;
    KW_ELSE; LBRACE; else_e = block; RBRACE
    { NIf (cond, then_e, else_e) }
  | KW_IF; cond = atom_expr; LBRACE; then_e = block; RBRACE
    { NIf (cond, then_e, NUnit) }
  | KW_CLOSURE; LBRACKET; captures = separated_list(COMMA, ID); RBRACKET;
    LPAREN; ps = params; RPAREN; ARROW; ret = signature_ty;
    LBRACE; body = block; RBRACE
    { NClosure (captures, ps, ret, body) }

place:
  | p = place_base; fields = list(field_suffix)
    { List.fold_left (fun acc f -> NPField (acc, f)) p fields }

place_base:
  | x = ID
    { NPVar x }
  | STAR; p = place
    { NPDeref p }

field_suffix:
  | DOT; f = ID { f }

path_name:
  | name = ID { [name] }
  | p = qualified_path { p }

qualified_path:
  | head = ID; DCOLON; second = ID; tail = list(path_suffix) { head :: second :: tail }

path_suffix:
  | DCOLON; name = ID { name }

struct_literal_field:
  | name = ID; EQUAL; e = expr { (name, e) }

match_branches:
  | { [] }
  | first = match_branch; rest = match_branch_tail { first :: rest }

match_branch_tail:
  | { [] }
  | COMMA { [] }
  | COMMA; branch = match_branch; rest = match_branch_tail { branch :: rest }

match_branch:
  | variant = ID; FATARROW; e = expr { (variant, [], e) }
  | variant = ID; LPAREN; binders = separated_list(COMMA, ID); RPAREN;
    FATARROW; e = expr
    { (variant, binders, e) }

match_scrut:
  | p = place { expr_of_place p }
  | LPAREN; e = expr; RPAREN { e }

ty:
  | KW_AFFINE;       c = ty_core { NTy (UAffine,       c) }
  | KW_LINEAR;       c = ty_core { NTy (ULinear,       c) }
  | KW_UNRESTRICTED; c = ty_core { NTy (UUnrestricted, c) }

ty_core:
  | KW_ISIZE { NTIntegers }
  | KW_F64   { NTFloats }
  | KW_BOOL  { NTBooleans }
  | LPAREN; RPAREN { NTUnits }
  | name = path_name; args = opt_type_args { NTNamed (name, args) }
  | LANGLE; self_ty = ty; KW_AS; trait = trait_ref; RANGLE; DCOLON; assoc = ID
    { NTAssoc (self_ty, trait, assoc) }
  | AMP; t = ty { NTRef (None, RShared, t) }
  | AMP; KW_MUT; t = ty { NTRef (None, RUnique, t) }
  | AMP; lt = LIFETIME; t = ty { NTRef (Some (resolve_lifetime lt), RShared, t) }
  | AMP; lt = LIFETIME; KW_MUT; t = ty { NTRef (Some (resolve_lifetime lt), RUnique, t) }
  | KW_FN; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty
    { NTFn (ts, ret) }
  | KW_CLOSURE; LANGLE; env_lt = LIFETIME; RANGLE; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty
    { NTClosure (resolve_lifetime env_lt, ts, ret) }
  | h = mixed_forall_params; KW_FN; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty; where_clause = opt_fn_where_clause
    { let (params, prev) = h in
      let (bounds, outs) = where_clause in
      let (lts, tys) = split_generics params in
      current_hrt_lifetimes := prev;
      let body = NTy (UUnrestricted, NTFn (ts, ret)) in
      match lts, tys with
      | [], _ -> NTTypeForall (tys, bounds, body)
      | _, [] -> NTForall (Big_int_Z.big_int_of_int (List.length lts), outs, body)
      | _, _ ->
          NTForall
            (Big_int_Z.big_int_of_int (List.length lts), outs,
             NTy (UUnrestricted, NTTypeForall (tys, bounds, body))) }

surface_ty:
  | u = opt_usage; c = surface_ty_core { NSTy (u, c) }

opt_usage:
  | { None }
  | KW_AFFINE { Some UAffine }
  | KW_LINEAR { Some ULinear }
  | KW_UNRESTRICTED { Some UUnrestricted }

surface_ty_core:
  | KW_ISIZE { NSTIntegers }
  | KW_F64   { NSTFloats }
  | KW_BOOL  { NSTBooleans }
  | LPAREN; RPAREN { NSTUnits }
  | name = path_name; args = opt_surface_type_args { NSTNamed (name, args) }
  | LANGLE; self_ty = surface_ty; KW_AS; trait = surface_trait_ref; RANGLE; DCOLON; assoc = ID
    { NSTAssoc (self_ty, trait, assoc) }
  | AMP; t = surface_ty { NSTRef (None, RShared, t) }
  | AMP; KW_MUT; t = surface_ty { NSTRef (None, RUnique, t) }
  | AMP; lt = LIFETIME; t = surface_ty { NSTRef (Some (resolve_lifetime lt), RShared, t) }
  | AMP; lt = LIFETIME; KW_MUT; t = surface_ty { NSTRef (Some (resolve_lifetime lt), RUnique, t) }
  | KW_FN; LPAREN; ts = surface_ty_list; RPAREN; ARROW; ret = surface_ty
    { NSTFn (ts, ret) }
  | KW_CLOSURE; LANGLE; env_lt = LIFETIME; RANGLE; LPAREN; ts = surface_ty_list; RPAREN; ARROW; ret = surface_ty
    { NSTClosure (resolve_lifetime env_lt, ts, ret) }

opt_surface_type_args:
  | { [] }
  | LANGLE; args = separated_nonempty_list(COMMA, surface_type_arg); RANGLE { args }

surface_type_arg:
  | lt = LIFETIME { NSTArgLifetime (resolve_lifetime lt) }
  | t = surface_ty { NSTArgTy t }

surface_ty_list:
  | { [] }
  | ts = separated_nonempty_list(COMMA, surface_ty) { ts }

signature_ty:
  | KW_AFFINE;       c = signature_ty_core { NTy (UAffine,       c) }
  | KW_LINEAR;       c = signature_ty_core { NTy (ULinear,       c) }
  | KW_UNRESTRICTED; c = signature_ty_core { NTy (UUnrestricted, c) }

signature_ty_core:
  | KW_ISIZE { NTIntegers }
  | KW_F64   { NTFloats }
  | KW_BOOL  { NTBooleans }
  | LPAREN; RPAREN { NTUnits }
  | name = path_name; args = opt_type_args { NTNamed (name, args) }
  | LANGLE; self_ty = signature_ty; KW_AS; trait = trait_ref; RANGLE; DCOLON; assoc = ID
    { NTAssoc (self_ty, trait, assoc) }
  | AMP; t = signature_ty { NTRef (None, RShared, t) }
  | AMP; KW_MUT; t = signature_ty { NTRef (None, RUnique, t) }
  | AMP; lt = LIFETIME; t = signature_ty { NTRef (Some (resolve_lifetime lt), RShared, t) }
  | AMP; lt = LIFETIME; KW_MUT; t = signature_ty { NTRef (Some (resolve_lifetime lt), RUnique, t) }
  | KW_FN; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty
    { NTFn (ts, ret) }
  | KW_CLOSURE; LANGLE; env_lt = LIFETIME; RANGLE; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty
    { NTClosure (resolve_lifetime env_lt, ts, ret) }
  | h = mixed_forall_params; KW_FN; LPAREN; ts = ty_list; RPAREN; ARROW; ret = ty; where_clause = opt_fn_where_clause
    { let (params, prev) = h in
      let (bounds, outs) = where_clause in
      let (lts, tys) = split_generics params in
      current_hrt_lifetimes := prev;
      let body = NTy (UUnrestricted, NTFn (ts, ret)) in
      match lts, tys with
      | [], _ -> NTTypeForall (tys, bounds, body)
      | _, [] -> NTForall (Big_int_Z.big_int_of_int (List.length lts), outs, body)
      | _, _ ->
          NTForall
            (Big_int_Z.big_int_of_int (List.length lts), outs,
             NTy (UUnrestricted, NTTypeForall (tys, bounds, body))) }

opt_type_args:
  | { [] }
  | LANGLE; args = separated_nonempty_list(COMMA, type_arg); RANGLE { args }

type_arg:
  | lt = LIFETIME { NTArgLifetime (resolve_lifetime lt) }
  | t = ty { NTArgTy t }

mixed_forall_params:
  | KW_FOR; LANGLE; params = separated_nonempty_list(COMMA, generic_param); RANGLE
    { with_mixed_forall_params params (fun _ _ prev -> (params, prev)) }

ty_list:
  | { [] }
  | ts = separated_nonempty_list(COMMA, ty) { ts }
