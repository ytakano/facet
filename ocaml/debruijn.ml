open Ast
open TypeChecker

(* scope maps name -> current de Bruijn index (shadow-counting) *)
type scope = (string * int) list

type ty_scope = {
  type_params  : string list;
  struct_names : string list;
}

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
  | NPField (p, field) -> PField (convert_place scope p, field)

let in_scope scope name = current_depth scope name >= 0

let lifetime_mem l lifetimes =
  List.exists (fun l' -> l' = l) lifetimes

let lifetime_add l lifetimes =
  if lifetime_mem l lifetimes then lifetimes else l :: lifetimes

let index_of name names =
  let rec aux i = function
    | [] -> None
    | h :: _ when h = name -> Some i
    | _ :: rest -> aux (i + 1) rest
  in
  aux 0 names

let rec lower_named_ty ty_scope (NTy (u, c)) =
  MkTy (u, lower_named_ty_core ty_scope c)

and lower_named_ty_core ty_scope c =
  match c with
  | NTUnits -> TUnits
  | NTIntegers -> TIntegers
  | NTFloats -> TFloats
  | NTBooleans -> TBooleans
  | NTNamed (s, args) ->
    begin match index_of s ty_scope.type_params with
    | Some i ->
      if args <> [] then failwith ("type parameter cannot take arguments: " ^ s);
      TParam (Big_int_Z.big_int_of_int i)
    | None ->
      let (lts, tys) = split_type_args ty_scope args in
      if List.mem s ty_scope.struct_names || args <> []
      then TStruct (s, lts, tys)
      else TNamed s
    end
  | NTFn (ts, ret) ->
    TFn (List.map (lower_named_ty ty_scope) ts, lower_named_ty ty_scope ret)
  | NTForall (n, outs, body) ->
    TForall (n, outs, lower_named_ty ty_scope body)
  | NTRef (lt_opt, rk, inner) ->
    let lt =
      match lt_opt with
      | Some lt -> lt
      | None -> LVar Big_int_Z.zero_big_int
    in
    TRef (lt, rk, lower_named_ty ty_scope inner)

and split_type_args ty_scope args =
  let rec go lts tys = function
    | [] -> (List.rev lts, List.rev tys)
    | NTArgLifetime lt :: rest -> go (lt :: lts) tys rest
    | NTArgTy ty :: rest -> go lts (lower_named_ty ty_scope ty :: tys) rest
  in
  go [] [] args

let rec named_ty_has_elided_ref_lifetime (NTy (_, c)) =
  named_ty_core_has_elided_ref_lifetime c

and named_ty_core_has_elided_ref_lifetime c =
  match c with
  | NTUnits | NTIntegers | NTFloats | NTBooleans -> false
  | NTNamed (_, args) ->
    List.exists named_type_arg_has_elided_ref_lifetime args
  | NTFn (ts, ret) ->
    List.exists named_ty_has_elided_ref_lifetime ts ||
    named_ty_has_elided_ref_lifetime ret
  | NTForall (_, _, body) ->
    named_ty_has_elided_ref_lifetime body
  | NTRef (None, _, _) -> true
  | NTRef (Some _, _, inner) ->
    named_ty_has_elided_ref_lifetime inner

and named_type_arg_has_elided_ref_lifetime = function
  | NTArgLifetime _ -> false
  | NTArgTy ty -> named_ty_has_elided_ref_lifetime ty

let rec lower_input_ty ty_scope next input_lts (NTy (u, c)) =
  match c with
  | NTRef (lt_opt, rk, inner) ->
    let (inner_ty, next', input_lts') = lower_input_ty ty_scope next input_lts inner in
    let (lt, next'') =
      match lt_opt with
      | Some lt -> (lt, next')
      | None -> (LVar (Big_int_Z.big_int_of_int next'), next' + 1)
    in
    (MkTy (u, TRef (lt, rk, inner_ty)), next'', lifetime_add lt input_lts')
  | _ ->
    (MkTy (u, lower_named_ty_core ty_scope c), next, input_lts)

let rec lower_output_ty ty_scope input_lts (NTy (u, c)) =
  match c with
  | NTRef (lt_opt, rk, inner) ->
    let inner_ty = lower_output_ty ty_scope input_lts inner in
    let lt =
      match lt_opt with
      | Some lt -> lt
      | None ->
        match input_lts with
        | [only] -> only
        | [] -> failwith "cannot elide output lifetime without an input lifetime"
        | _ -> failwith "cannot elide output lifetime with multiple input lifetimes"
    in
    MkTy (u, TRef (lt, rk, inner_ty))
  | _ ->
    MkTy (u, lower_named_ty_core ty_scope c)

let split_generics generics =
  let rec go lts tys = function
    | [] -> (List.rev lts, List.rev tys)
    | NGLifetime lt :: rest -> go (lt :: lts) tys rest
    | NGType ty :: rest -> go lts (ty :: tys) rest
  in
  go [] [] generics

let trait_bound_of_named type_params b =
  match index_of b.ntb_type_name type_params with
  | None -> failwith ("unknown type parameter in trait bound: " ^ b.ntb_type_name)
  | Some i ->
    { bound_type_index = Big_int_Z.big_int_of_int i;
      bound_traits = b.ntb_traits }

let split_expr_type_args ty_scope args =
  let rec go lts tys = function
    | [] -> (List.rev lts, List.rev tys)
    | NTArgLifetime lt :: rest -> go (lt :: lts) tys rest
    | NTArgTy ty :: rest -> go lts (lower_named_ty ty_scope ty :: tys) rest
  in
  go [] [] args

let rec convert (fn_names : string list) (ty_scope : ty_scope) (scope : scope) (e : named_expr) : expr =
  match e with
  | NUnit           -> EUnit
  | NLit l          -> ELit l
  | NVar name       ->
    if in_scope scope name then EVar (make_ident name (lookup scope name))
    else if List.mem name fn_names then EFn (make_ident name 0)
    else EVar (make_ident name (lookup scope name))
  | NPlace p        -> EPlace (convert_place scope p)
  | NDrop e1        -> EDrop (convert fn_names ty_scope scope e1)
  | NReplace (p, e1) ->
    EReplace (convert_place scope p, convert fn_names ty_scope scope e1)
  | NAssign (p, e1) ->
    EAssign (convert_place scope p, convert fn_names ty_scope scope e1)
  | NBorrow (rk, p) ->
    EBorrow (rk, convert_place scope p)
  | NDeref e1 ->
    EDeref (convert fn_names ty_scope scope e1)
  | NCall (f, args) ->
    let args' = List.map (convert fn_names ty_scope scope) args in
    if in_scope scope f then ECallExpr (EVar (make_ident f (lookup scope f)), args')
    else ECall (make_ident f 0, args')
  | NStruct (name, args, fields) ->
    let (lts, tys) = split_expr_type_args ty_scope args in
    EStruct (name, lts, tys,
      List.map (fun (field, e1) -> (field, convert fn_names ty_scope scope e1)) fields)
  | NLet (m, name, Some ty, e1, e2) ->
    if named_ty_has_elided_ref_lifetime ty
    then failwith "cannot elide lifetime in local type annotation";
    let e1' = convert fn_names ty_scope scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert fn_names ty_scope scope' e2 in
    ELet (m, make_ident name d, lower_named_ty ty_scope ty, e1', e2')
  | NLet (m, name, None, e1, e2) ->
    let e1' = convert fn_names ty_scope scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert fn_names ty_scope scope' e2 in
    ELetInfer (m, make_ident name d, e1', e2')
  | NIf (cond, then_e, else_e) ->
    EIf (convert fn_names ty_scope scope cond,
         convert fn_names ty_scope scope then_e,
         convert fn_names ty_scope scope else_e)

let convert_fn_def_with_names struct_names fn_names (f : named_fn_def) : fn_def =
  let ty_scope = {
    type_params = [];
    struct_names;
  } in
  let (scope, params, next_lifetime, input_lts) = List.fold_left
    (fun (sc, acc, next_lt, input_lts) np ->
      let (sc', d) = add_binding sc np.np_name in
      let (param_ty, next_lt', input_lts') =
        lower_input_ty ty_scope next_lt input_lts np.np_ty
      in
      let p = { param_mutability = np.np_mutability;
                param_name       = make_ident np.np_name d;
                param_ty         = param_ty } in
      (sc', acc @ [p], next_lt', input_lts'))
    ([], [], List.length f.nf_lifetime_names, []) f.nf_params
  in
  let ret_ty = lower_output_ty ty_scope input_lts f.nf_ret in
  { fn_name      = make_ident f.nf_name 0;
    fn_lifetimes = Big_int_Z.big_int_of_int next_lifetime;
    fn_outlives = f.nf_outlives;
    fn_params    = params;
    fn_ret       = ret_ty;
    fn_body      = convert fn_names ty_scope scope f.nf_body }

let convert_struct struct_names s =
  let (lts, tys) = split_generics s.ns_generics in
  let ty_scope = { type_params = tys; struct_names } in
  { struct_name = s.ns_name;
    struct_lifetimes = Big_int_Z.big_int_of_int (List.length lts);
    struct_type_params = Big_int_Z.big_int_of_int (List.length tys);
    struct_bounds = List.map (trait_bound_of_named tys) s.ns_bounds;
    struct_fields =
      List.map
        (fun f ->
          { field_name = f.nfield_name;
            field_mutability = f.nfield_mutability;
            field_ty = lower_named_ty ty_scope f.nfield_ty })
        s.ns_fields }

let convert_trait t =
  let (_lts, tys) = split_generics t.nt_generics in
  { trait_name = t.nt_name;
    trait_type_params = Big_int_Z.big_int_of_int (List.length tys);
    trait_bounds = List.map (trait_bound_of_named tys) t.nt_bounds }

let convert_impl struct_names i =
  let (lts, tys) = split_generics i.ni_generics in
  let ty_scope = { type_params = tys; struct_names } in
  let (trait_lts, trait_args) = split_expr_type_args ty_scope i.ni_trait_args in
  if trait_lts <> []
  then failwith ("trait impl target cannot take lifetime arguments: " ^ i.ni_trait_name);
  { impl_lifetimes = Big_int_Z.big_int_of_int (List.length lts);
    impl_type_params = Big_int_Z.big_int_of_int (List.length tys);
    impl_trait_name = i.ni_trait_name;
    impl_trait_args = trait_args;
    impl_for_ty = lower_named_ty ty_scope i.ni_for_ty }

let duplicate_name names =
  let rec go seen = function
    | [] -> None
    | x :: xs -> if List.mem x seen then Some x else go (x :: seen) xs
  in
  go [] names

let validate_env env =
  let top_names =
    List.map (fun s -> s.struct_name) env.env_structs @
    List.map (fun t -> t.trait_name) env.env_traits @
    List.map (fun f -> fst f.fn_name) env.env_fns
  in
  match duplicate_name top_names with
  | Some name -> Some ("duplicate top-level name: " ^ name)
  | None ->
    let trait_names = List.map (fun t -> t.trait_name) env.env_traits in
    let zero = Big_int_Z.zero_big_int in
    let big_len xs = Big_int_Z.big_int_of_int (List.length xs) in
    let find_struct name =
      List.find_opt (fun s -> s.struct_name = name) env.env_structs
    in
    let find_trait name =
      List.find_opt (fun t -> t.trait_name = name) env.env_traits
    in
    let validate_bound max_ty_params b =
      if Big_int_Z.ge_big_int b.bound_type_index max_ty_params
      then Some "trait bound refers to an out-of-range type parameter"
      else
        match List.find_opt (fun tr -> not (List.mem tr trait_names)) b.bound_traits with
        | Some tr -> Some ("unknown trait in bound: " ^ tr)
        | None -> None
    in
    let rec first_some = function
      | [] -> None
      | x :: xs -> begin match x with Some _ -> x | None -> first_some xs end
    in
    let lifetime_error lt_params bound_depth = function
      | LStatic -> None
      | LVar i ->
        if Big_int_Z.lt_big_int i lt_params then None
        else Some "lifetime parameter index out of range"
      | LBound i ->
        if Big_int_Z.lt_big_int i bound_depth then None
        else Some "bound lifetime index out of range"
    in
    let outlives_error lt_params bound_depth outs =
      first_some
        (List.map
           (fun (a, b) ->
             match lifetime_error lt_params bound_depth a with
             | Some _ as err -> err
             | None -> lifetime_error lt_params bound_depth b)
           outs)
    in
    let rec type_error ty_params lt_params bound_depth (MkTy (_, core)) =
      match core with
      | TUnits | TIntegers | TFloats | TBooleans -> None
      | TNamed name -> Some ("unknown type: " ^ name)
      | TParam i ->
        if Big_int_Z.lt_big_int i ty_params then None
        else Some "type parameter index out of range"
      | TStruct (name, lts, args) ->
        begin match find_struct name with
        | None -> Some ("unknown struct type: " ^ name)
        | Some s ->
          if not (Big_int_Z.eq_big_int (big_len lts) s.struct_lifetimes)
          then Some ("struct lifetime arity mismatch: " ^ name)
          else if not (Big_int_Z.eq_big_int (big_len args) s.struct_type_params)
          then Some ("struct type arity mismatch: " ^ name)
          else
            first_some
              (List.map (lifetime_error lt_params bound_depth) lts @
               List.map (type_error ty_params lt_params bound_depth) args)
        end
      | TFn (args, ret) ->
        first_some
          (List.map (type_error ty_params lt_params bound_depth) args @
           [type_error ty_params lt_params bound_depth ret])
      | TForall (n, outs, body) ->
        let bound_depth' = Big_int_Z.add_big_int n bound_depth in
        begin match outlives_error lt_params bound_depth' outs with
        | Some _ as err -> err
        | None -> type_error ty_params lt_params bound_depth' body
        end
      | TRef (lt, _, inner) ->
        begin match lifetime_error lt_params bound_depth lt with
        | Some _ as err -> err
        | None -> type_error ty_params lt_params bound_depth inner
        end
    in
    let rec type_struct_refs (MkTy (_, core)) =
      match core with
      | TStruct (name, _, args) ->
        name :: List.concat_map type_struct_refs args
      | TFn (args, ret) ->
        List.concat_map type_struct_refs args @ type_struct_refs ret
      | TForall (_, _, body) -> type_struct_refs body
      | TRef (_, _, inner) -> type_struct_refs inner
      | TUnits | TIntegers | TFloats | TBooleans | TNamed _ | TParam _ -> []
    in
    let struct_deps s =
      List.concat_map (fun f -> type_struct_refs f.field_ty) s.struct_fields
    in
    let rec reaches_struct seen target current =
      if List.mem current seen then false
      else
        match find_struct current with
        | None -> false
        | Some s ->
          let deps = struct_deps s in
          List.mem target deps ||
          List.exists (reaches_struct (current :: seen) target) deps
    in
    let validate_acyclic_struct s =
      if reaches_struct [] s.struct_name s.struct_name
      then Some ("recursive struct: " ^ s.struct_name)
      else None
    in
    let validate_struct s =
      match duplicate_name (List.map (fun f -> f.field_name) s.struct_fields) with
      | Some field -> Some ("duplicate field in struct " ^ s.struct_name ^ ": " ^ field)
      | None ->
        first_some
          (List.map
             (fun f -> type_error s.struct_type_params s.struct_lifetimes zero f.field_ty)
             s.struct_fields @
           List.map (validate_bound s.struct_type_params) s.struct_bounds)
    in
    let validate_trait t =
      first_some (List.map (validate_bound t.trait_type_params) t.trait_bounds)
    in
    let validate_impl i =
      match find_trait i.impl_trait_name with
      | None -> Some ("unknown trait in impl: " ^ i.impl_trait_name)
      | Some trait_def ->
        if not (Big_int_Z.eq_big_int (big_len i.impl_trait_args) trait_def.trait_type_params)
        then Some ("trait type arity mismatch: " ^ i.impl_trait_name)
        else
        first_some
          (List.map
             (type_error i.impl_type_params i.impl_lifetimes zero)
             i.impl_trait_args @
           [type_error i.impl_type_params i.impl_lifetimes zero i.impl_for_ty])
    in
    let validate_fn f =
      first_some
        (List.map
           (fun p -> type_error zero f.fn_lifetimes zero p.param_ty)
           f.fn_params @
         [type_error zero f.fn_lifetimes zero f.fn_ret;
          outlives_error f.fn_lifetimes zero f.fn_outlives])
    in
    match first_some (List.map validate_acyclic_struct env.env_structs @
                      List.map validate_struct env.env_structs @
                      List.map validate_trait env.env_traits @
                      List.map validate_impl env.env_impls @
                      List.map validate_fn env.env_fns) with
    | Some _ as err -> err
    | None ->
      let impl_key_eq a b =
        a.impl_trait_name = b.impl_trait_name &&
        List.length a.impl_trait_args = List.length b.impl_trait_args &&
        List.for_all2 ty_eqb a.impl_trait_args b.impl_trait_args &&
        ty_eqb a.impl_for_ty b.impl_for_ty
      in
      let rec dup_impl = function
        | [] -> false
        | x :: xs -> List.exists (impl_key_eq x) xs || dup_impl xs
      in
      if dup_impl env.env_impls then Some "duplicate impl" else None

let convert_program_items (items : named_item list) : global_env =
  let structs = List.filter_map (function NIStruct s -> Some s | _ -> None) items in
  let traits = List.filter_map (function NITrait t -> Some t | _ -> None) items in
  let impls = List.filter_map (function NIImpl i -> Some i | _ -> None) items in
  let fns = List.filter_map (function NIFn f -> Some f | _ -> None) items in
  let struct_names = List.map (fun s -> s.ns_name) structs in
  let fn_names = List.map (fun f -> f.nf_name) fns in
  let env = {
    env_structs = List.map (convert_struct struct_names) structs;
    env_traits = List.map convert_trait traits;
    env_impls = List.map (convert_impl struct_names) impls;
    env_fns = List.map (convert_fn_def_with_names struct_names fn_names) fns;
  } in
  match validate_env env with
  | None -> env
  | Some msg -> failwith msg

let convert_program (items : named_item list) : fn_def list =
  (convert_program_items items).env_fns

let convert_fn_def f = convert_fn_def_with_names [] [] f
