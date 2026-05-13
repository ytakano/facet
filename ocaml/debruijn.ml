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

let resolve_lifetime_name names name =
  let rec aux i = function
    | [] -> failwith ("undefined lifetime '" ^ name)
    | h :: _ when h = name -> i
    | _ :: rest -> aux (i + 1) rest
  in
  aux 0 names

let lifetime_mem l lifetimes =
  List.exists (fun l' -> l' = l) lifetimes

let lifetime_add l lifetimes =
  if lifetime_mem l lifetimes then lifetimes else l :: lifetimes

let lower_named_ty_core c =
  match c with
  | NTUnits -> TUnits
  | NTIntegers -> TIntegers
  | NTFloats -> TFloats
  | NTBooleans -> TBooleans
  | NTNamed s -> TNamed s
  | NTFn (ts, ret) -> TFn (ts, ret)
  | NTForall (n, outs, body) -> TForall (n, outs, body)
  | NTRef _ -> failwith "internal error: NTRef must be lowered with context"

let rec lower_input_ty lifetime_names next input_lts (NTy (u, c)) =
  match c with
  | NTRef (lt_opt, rk, inner) ->
    let (inner_ty, next', input_lts') = lower_input_ty lifetime_names next input_lts inner in
    let (lt, next'') =
      match lt_opt with
      | Some name -> (LVar (Big_int_Z.big_int_of_int (resolve_lifetime_name lifetime_names name)), next')
      | None -> (LVar (Big_int_Z.big_int_of_int next'), next' + 1)
    in
    (MkTy (u, TRef (lt, rk, inner_ty)), next'', lifetime_add lt input_lts')
  | _ ->
    (MkTy (u, lower_named_ty_core c), next, input_lts)

let rec lower_output_ty lifetime_names input_lts (NTy (u, c)) =
  match c with
  | NTRef (lt_opt, rk, inner) ->
    let inner_ty = lower_output_ty lifetime_names input_lts inner in
    let lt =
      match lt_opt with
      | Some name -> LVar (Big_int_Z.big_int_of_int (resolve_lifetime_name lifetime_names name))
      | None ->
        match input_lts with
        | [only] -> only
        | [] -> failwith "cannot elide output lifetime without an input lifetime"
        | _ -> failwith "cannot elide output lifetime with multiple input lifetimes"
    in
    MkTy (u, TRef (lt, rk, inner_ty))
  | _ ->
    MkTy (u, lower_named_ty_core c)

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
  let (scope, params, next_lifetime, input_lts) = List.fold_left
    (fun (sc, acc, next_lt, input_lts) np ->
      let (sc', d) = add_binding sc np.np_name in
      let (param_ty, next_lt', input_lts') =
        lower_input_ty f.nf_lifetime_names next_lt input_lts np.np_ty
      in
      let p = { param_mutability = np.np_mutability;
                param_name       = make_ident np.np_name d;
                param_ty         = param_ty } in
      (sc', acc @ [p], next_lt', input_lts'))
    ([], [], List.length f.nf_lifetime_names, []) f.nf_params
  in
  let ret_ty = lower_output_ty f.nf_lifetime_names input_lts f.nf_ret in
  { fn_name      = make_ident f.nf_name 0;
    fn_lifetimes = Big_int_Z.big_int_of_int next_lifetime;
    fn_outlives = f.nf_outlives;
    fn_params    = params;
    fn_ret       = ret_ty;
    fn_body      = convert fn_names scope f.nf_body }

let convert_program (fs : named_fn_def list) : fn_def list =
  let fn_names = List.map (fun f -> f.nf_name) fs in
  List.map (convert_fn_def_with_names fn_names) fs

let convert_fn_def f = convert_fn_def_with_names [] f
