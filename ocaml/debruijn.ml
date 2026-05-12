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

let rec convert (scope : scope) (e : named_expr) : expr =
  match e with
  | NUnit           -> EUnit
  | NLit l          -> ELit l
  | NVar name       -> EVar (make_ident name (lookup scope name))
  | NDrop e1        -> EDrop (convert scope e1)
  | NReplace (id, e1) ->
    EReplace (PVar (make_ident id (lookup scope id)), convert scope e1)
  | NAssign (id, e1) ->
    EAssign (PVar (make_ident id (lookup scope id)), convert scope e1)
  | NBorrow (rk, id) ->
    EBorrow (rk, PVar (make_ident id (lookup scope id)))
  | NReplaceDeref (id, e1) ->
    EReplace (PDeref (PVar (make_ident id (lookup scope id))), convert scope e1)
  | NAssignDeref (id, e1) ->
    EAssign (PDeref (PVar (make_ident id (lookup scope id))), convert scope e1)
  | NReBorrow (rk, id) ->
    EBorrow (rk, PDeref (PVar (make_ident id (lookup scope id))))
  | NDeref e1 ->
    EDeref (convert scope e1)
  | NCall (f, args) ->
    ECall (make_ident f 0, List.map (convert scope) args)
  | NLet (m, name, Some ty, e1, e2) ->
    let e1' = convert scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert scope' e2 in
    ELet (m, make_ident name d, ty, e1', e2')
  | NLet (m, name, None, e1, e2) ->
    let e1' = convert scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert scope' e2 in
    ELetInfer (m, make_ident name d, e1', e2')
  | NIf (cond, then_e, else_e) ->
    EIf (convert scope cond, convert scope then_e, convert scope else_e)

let convert_fn_def (f : named_fn_def) : fn_def =
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
    fn_params    = params;
    fn_ret       = f.nf_ret;
    fn_body      = convert scope f.nf_body }
