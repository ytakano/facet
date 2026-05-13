open Ast
open TypeChecker

(* scope maps name -> current de Bruijn index (shadow-counting) *)
type scope = (string * int) list

let current_depth scope name =
  match List.assoc_opt name scope with
  | Some d -> d
  | None   -> -1

let add_binding scope name =
  let d = current_depth scope name + 1 in
  ((name, d) :: scope, d)

let lookup scope name =
  max 0 (current_depth scope name)

let make_ident name d : ident =
  (name, Big_int_Z.big_int_of_int d)

let rec convert_place scope = function
  | NPVar name -> PVar (make_ident name (lookup scope name))
  | NPDeref p -> PDeref (convert_place scope p)

let in_scope scope name = current_depth scope name >= 0

let rec convert (fn_names : string list) (scope : scope) (e : named_expr) : expr =
  match e with
  | NUnit           -> EUnit
  | NLit l          -> ELit l
  | NVar name       ->
    if in_scope scope name then EVar (make_ident name (lookup scope name))
    else if List.mem name fn_names then EFn (make_ident name 0)
    else EVar (make_ident name (lookup scope name))
  | NDrop e1        -> EDrop (convert fn_names scope e1)
  | NReplace (p, e1) ->
    EReplace (convert_place scope p, convert fn_names scope e1)
  | NAssign (p, e1) ->
    EAssign (convert_place scope p, convert fn_names scope e1)
  | NBorrow (rk, p) ->
    EBorrow (rk, convert_place scope p)
  | NDeref e1 ->
    EDeref (convert fn_names scope e1)
  | NCall (f, args) ->
    let args' = List.map (convert fn_names scope) args in
    if in_scope scope f then ECallExpr (EVar (make_ident f (lookup scope f)), args')
    else ECall (make_ident f 0, args')
  | NLet (m, name, Some ty, e1, e2) ->
    let e1' = convert fn_names scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert fn_names scope' e2 in
    ELet (m, make_ident name d, ty, e1', e2')
  | NLet (m, name, None, e1, e2) ->
    let e1' = convert fn_names scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert fn_names scope' e2 in
    ELetInfer (m, make_ident name d, e1', e2')
  | NIf (cond, then_e, else_e) ->
    EIf (convert fn_names scope cond, convert fn_names scope then_e, convert fn_names scope else_e)

let convert_fn_def_with_names fn_names (f : named_fn_def) : fn_def =
  let (scope, params) = List.fold_left
    (fun (sc, acc) np ->
      let (sc', d) = add_binding sc np.np_name in
      let p = { param_mutability = np.np_mutability;
                param_name       = make_ident np.np_name d;
                param_ty         = np.np_ty } in
      (sc', acc @ [p]))
    ([], []) f.nf_params
  in
  { fn_name      = make_ident f.nf_name 0;
    fn_lifetimes = Big_int_Z.big_int_of_int (List.length f.nf_lifetime_names);
    fn_outlives = f.nf_outlives;
    fn_params    = params;
    fn_ret       = f.nf_ret;
    fn_body      = convert fn_names scope f.nf_body }

let convert_program (fs : named_fn_def list) : fn_def list =
  let fn_names = List.map (fun f -> f.nf_name) fs in
  List.map (convert_fn_def_with_names fn_names) fs

let convert_fn_def f = convert_fn_def_with_names [] f
