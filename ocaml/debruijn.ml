open Ast
open TypeChecker

(* scope maps name -> current de Bruijn index (shadow-counting) *)
type scope = (string * int) list

type ty_scope = {
  type_params  : string list;
  struct_names : string list;
  enum_names   : string list;
}

let string_of_path path = String.concat "::" path

let split_generics params =
  let rec go lts tys = function
    | [] -> (List.rev lts, List.rev tys)
    | NGLifetime lt :: rest -> go (lt :: lts) tys rest
    | NGType ty :: rest -> go lts (ty :: tys) rest
  in
  go [] [] params


let parent_prefixes prefix =
  let rec aux acc p =
    match p with
    | [] -> List.rev ([] :: acc)
    | _ -> aux (p :: acc) (List.rev (List.tl (List.rev p)))
  in
  aux [] prefix

type item_info = {
  info_name : string;
  info_visibility : named_visibility;
  info_owner : string list;
  info_ancestors : (string list * named_visibility) list;
}

type import_info = {
  import_name : string;
  import_target : string;
}

let rec path_starts_with prefix path =
  match prefix, path with
  | [], _ -> true
  | p :: ps, x :: xs when p = x -> path_starts_with ps xs
  | _ -> false

let item_visible_from prefix info =
  let visible_from_owner owner visibility =
    match visibility with
    | VPublic -> true
    | VPrivate -> path_starts_with owner prefix
  in
  visible_from_owner info.info_owner info.info_visibility
  && List.for_all
    (fun (owner, visibility) -> visible_from_owner owner visibility)
    info.info_ancestors

let resolve_info_from known prefix name =
  match List.find_opt (fun info -> info.info_name = name) known with
  | None -> None
  | Some info ->
    if item_visible_from prefix info then Some info
    else failwith ("private path: " ^ name)

let resolve_path_from known imports prefix path =
  match path with
  | [] -> failwith "empty path"
  | [name] ->
    begin match List.find_opt (fun info -> info.import_name = name) imports with
    | Some info -> info.import_target
    | None ->
      let candidates = List.map (fun p -> string_of_path (p @ [name])) (parent_prefixes prefix) in
      begin match List.find_map (resolve_info_from known prefix) candidates with
      | Some info -> info.info_name
      | None -> name
      end
    end
  | head :: rest ->
    begin match List.find_opt (fun info -> info.import_name = head) imports with
    | Some info -> info.import_target ^ "::" ^ string_of_path rest
    | None ->
      let name = string_of_path path in
      begin match resolve_info_from known prefix name with
      | Some info -> info.info_name
      | None -> name
      end
    end

let rec map_named_ty f ty_params (NTy (u, c)) =
  NTy (u, map_named_ty_core f ty_params c)

and map_named_ty_core f ty_params = function
  | NTUnits -> NTUnits
  | NTIntegers -> NTIntegers
  | NTFloats -> NTFloats
  | NTBooleans -> NTBooleans
  | NTNamed ([name], args) when List.mem name ty_params ->
    NTNamed ([name], List.map (map_named_type_arg f ty_params) args)
  | NTNamed (path, args) ->
    NTNamed ([f path], List.map (map_named_type_arg f ty_params) args)
  | NTFn (ts, ret) ->
    NTFn (List.map (map_named_ty f ty_params) ts, map_named_ty f ty_params ret)
  | NTClosure (lt, ts, ret) ->
    NTClosure (lt, List.map (map_named_ty f ty_params) ts, map_named_ty f ty_params ret)
  | NTForall (n, outs, body) ->
    NTForall (n, outs, map_named_ty f ty_params body)
  | NTTypeForall (params, bounds, body) ->
    NTTypeForall (params, List.map (map_named_trait_bound f ty_params) bounds,
      map_named_ty f (params @ ty_params) body)
  | NTRef (lt, rk, inner) ->
    NTRef (lt, rk, map_named_ty f ty_params inner)

and map_named_type_arg f ty_params = function
  | NTArgLifetime lt -> NTArgLifetime lt
  | NTArgTy ty -> NTArgTy (map_named_ty f ty_params ty)

and map_named_trait_ref f ty_params r =
  { ntr_name = [f r.ntr_name];
    ntr_args = List.map (map_named_type_arg f ty_params) r.ntr_args }

and map_named_trait_bound f ty_params b =
  { b with ntb_traits = List.map (map_named_trait_ref f ty_params) b.ntb_traits }

let map_named_param f ty_params p =
  { p with np_ty = map_named_ty f ty_params p.np_ty }

let rec map_named_expr f fn_names ty_params value_scope = function
  | NUnit -> NUnit
  | NLit l -> NLit l
  | NVar name ->
    if List.mem name value_scope then NVar name
    else
      let resolved = f [name] in
      if List.mem resolved fn_names then NVar resolved else NVar name
  | NPlace p -> NPlace p
  | NLet (m, name, ty_opt, e1, e2) ->
    let ty_opt' = Option.map (map_named_ty f ty_params) ty_opt in
    NLet (m, name, ty_opt',
      map_named_expr f fn_names ty_params value_scope e1,
      map_named_expr f fn_names ty_params (name :: value_scope) e2)
  | NCall (path, args, exprs) ->
    let path' =
      match path with
      | [name] when List.mem name value_scope -> [name]
      | _ -> [f path]
    in
    NCall (path', List.map (map_named_type_arg f ty_params) args,
      List.map (map_named_expr f fn_names ty_params value_scope) exprs)
  | NStruct (path, args, fields) ->
    NStruct ([f path], List.map (map_named_type_arg f ty_params) args,
      List.map (fun (field, e) ->
        (field, map_named_expr f fn_names ty_params value_scope e)) fields)
  | NEnum (path, args, variant, variant_args, payloads) ->
    NEnum ([f path], List.map (map_named_type_arg f ty_params) args, variant,
      List.map (map_named_type_arg f ty_params) variant_args,
      List.map (map_named_expr f fn_names ty_params value_scope) payloads)
  | NMatch (scrut, branches) ->
    NMatch (map_named_expr f fn_names ty_params value_scope scrut,
      List.map (fun (variant, binders, body) ->
        (variant, binders, map_named_expr f fn_names ty_params (binders @ value_scope) body)) branches)
  | NReplace (place, e) ->
    NReplace (place, map_named_expr f fn_names ty_params value_scope e)
  | NAssign (place, e) ->
    NAssign (place, map_named_expr f fn_names ty_params value_scope e)
  | NBorrow (rk, place) -> NBorrow (rk, place)
  | NDeref e -> NDeref (map_named_expr f fn_names ty_params value_scope e)
  | NDrop e -> NDrop (map_named_expr f fn_names ty_params value_scope e)
  | NIf (a, b, c) ->
    NIf (map_named_expr f fn_names ty_params value_scope a,
         map_named_expr f fn_names ty_params value_scope b,
         map_named_expr f fn_names ty_params value_scope c)
  | NClosure (captures, params, ret, body) ->
    let params' = List.map (map_named_param f ty_params) params in
    let value_scope' = List.map (fun p -> p.np_name) params @ captures @ value_scope in
    NClosure (captures, params', map_named_ty f ty_params ret,
      map_named_expr f fn_names ty_params value_scope' body)
  | NLetRec (captures, rec_fns, body) ->
    let rec_names = List.map (fun rf -> rf.nrf_name) rec_fns in
    let map_rec_fn rf =
      let params' = List.map (map_named_param f ty_params) rf.nrf_params in
      let body_scope =
        List.map (fun p -> p.np_name) rf.nrf_params @ captures @ rec_names @ value_scope in
      { rf with nrf_params = params'; nrf_ret = map_named_ty f ty_params rf.nrf_ret;
                nrf_body = map_named_expr f fn_names ty_params body_scope rf.nrf_body }
    in
    NLetRec (captures, List.map map_rec_fn rec_fns,
      map_named_expr f fn_names ty_params (rec_names @ value_scope) body)

let item_local_name = function
  | NIFn f -> f.nf_name
  | NIStruct s -> s.ns_name
  | NIEnum e -> e.ne_name
  | NITrait t -> t.nt_name
  | NIImpl _ -> "<impl>"
  | NIUse _ -> "<use>"
  | NIModFile (_, name) -> name
  | NIMod (_, name, _) -> name

let duplicate_module_name names =
  let names = List.filter (fun name -> name <> "<impl>" && name <> "<use>") names in
  let rec go seen = function
    | [] -> None
    | x :: xs -> if List.mem x seen then Some x else go (x :: seen) xs
  in
  go [] names

let rec reject_user_core_module = function
  | [] -> ()
  | NIMod (_, "core", _) :: _ -> failwith "user-defined module core is reserved"
  | NIModFile (_, "core") :: _ -> failwith "user-defined module core is reserved"
  | NIMod (_, _, items) :: rest -> reject_user_core_module items; reject_user_core_module rest
  | _ :: rest -> reject_user_core_module rest

let rec collect_item_paths prefix items =
  begin match duplicate_module_name (List.map item_local_name items) with
  | Some name -> failwith ("duplicate item in module " ^ string_of_path prefix ^ ": " ^ name)
  | None -> ()
  end;
  List.concat_map
    (function
      | NIMod (_, name, children) -> collect_item_paths (prefix @ [name]) children
      | NIModFile (_, name) -> failwith ("unexpanded file module: " ^ string_of_path (prefix @ [name]))
      | NIFn f -> [prefix @ [f.nf_name]]
      | NIStruct st -> [prefix @ [st.ns_name]]
      | NIEnum e -> [prefix @ [e.ne_name]]
      | NITrait t -> [prefix @ [t.nt_name]]
      | NIImpl _ -> []
      | NIUse _ -> [])
    items

let rec collect_item_infos ancestors prefix items =
  List.concat_map
    (function
      | NIMod (visibility, name, children) ->
        let module_path = prefix @ [name] in
        collect_item_infos ((prefix, visibility) :: ancestors) module_path children
      | NIModFile (_, name) -> failwith ("unexpanded file module: " ^ string_of_path (prefix @ [name]))
      | NIFn f ->
        [{ info_name = string_of_path (prefix @ [f.nf_name]);
           info_visibility = f.nf_visibility;
           info_owner = prefix;
           info_ancestors = ancestors }]
      | NIStruct st ->
        [{ info_name = string_of_path (prefix @ [st.ns_name]);
           info_visibility = st.ns_visibility;
           info_owner = prefix;
           info_ancestors = ancestors }]
      | NIEnum e ->
        [{ info_name = string_of_path (prefix @ [e.ne_name]);
           info_visibility = e.ne_visibility;
           info_owner = prefix;
           info_ancestors = ancestors }]
      | NITrait t ->
        [{ info_name = string_of_path (prefix @ [t.nt_name]);
           info_visibility = t.nt_visibility;
           info_owner = prefix;
           info_ancestors = ancestors }]
      | NIImpl _ -> []
      | NIUse _ -> [])
    items

let last_path_segment path =
  match List.rev path with
  | [] -> failwith "empty import path"
  | name :: _ -> name

let known_info_exists known name =
  List.exists (fun info -> info.info_name = name) known

let resolve_import_target known prefix path =
  let target = resolve_path_from known [] prefix path in
  if known_info_exists known target then target
  else failwith ("unknown import path: " ^ string_of_path path)

let collect_module_imports known prefix items =
  let local_names =
    List.filter
      (fun name -> name <> "<impl>" && name <> "<use>")
      (List.map item_local_name items)
  in
  let add_import imports path alias =
    let name = match alias with Some name -> name | None -> last_path_segment path in
    if List.mem name local_names
    then failwith ("ambiguous import: " ^ name)
    else if List.exists (fun info -> info.import_name = name) imports
    then failwith ("ambiguous import: " ^ name)
    else { import_name = name; import_target = resolve_import_target known prefix path } :: imports
  in
  List.rev
    (List.fold_left
       (fun imports item ->
          match item with
          | NIUse (path, alias) -> add_import imports path alias
          | _ -> imports)
       []
       items)

let rec flatten_modules known prefix items =
  let known_names = List.map (fun info -> info.info_name) known in
  let fn_names = known_names in
  let imports = collect_module_imports known prefix items in
  let resolve = resolve_path_from known imports prefix in
  List.concat_map
    (function
      | NIMod (_, name, children) -> flatten_modules known (prefix @ [name]) children
      | NIModFile (_, name) -> failwith ("unexpanded file module: " ^ string_of_path (prefix @ [name]))
      | NIFn f ->
        let (_lts, tys) = split_generics f.nf_generics in
        [NIFn { f with nf_name = string_of_path (prefix @ [f.nf_name]);
                      nf_bounds = List.map (map_named_trait_bound resolve tys) f.nf_bounds;
                      nf_params = List.map (map_named_param resolve tys) f.nf_params;
                      nf_ret = map_named_ty resolve tys f.nf_ret;
                      nf_body = map_named_expr resolve fn_names tys
                        (List.map (fun p -> p.np_name) f.nf_params) f.nf_body }]
      | NIStruct st ->
        let (_lts, tys) = split_generics st.ns_generics in
        [NIStruct { st with ns_name = string_of_path (prefix @ [st.ns_name]);
                           ns_bounds = List.map (map_named_trait_bound resolve tys) st.ns_bounds;
                           ns_fields = List.map
                             (fun field -> { field with nfield_ty = map_named_ty resolve tys field.nfield_ty })
                             st.ns_fields }]
      | NIEnum e ->
        let (_lts, tys) = split_generics e.ne_generics in
        [NIEnum { e with ne_name = string_of_path (prefix @ [e.ne_name]);
                         ne_bounds = List.map (map_named_trait_bound resolve tys) e.ne_bounds;
                         ne_variants = List.map
                           (fun v -> { v with nev_fields = List.map (map_named_ty resolve tys) v.nev_fields })
                           e.ne_variants }]
      | NITrait t ->
        let (_lts, tys) = split_generics t.nt_generics in
        [NITrait { t with nt_name = string_of_path (prefix @ [t.nt_name]);
                          nt_bounds = List.map (map_named_trait_bound resolve tys) t.nt_bounds }]
      | NIImpl i ->
        let (_lts, tys) = split_generics i.ni_generics in
        [NIImpl { i with ni_trait_name = [resolve i.ni_trait_name];
                         ni_trait_args = List.map (map_named_type_arg resolve tys) i.ni_trait_args;
                         ni_for_ty = map_named_ty resolve tys i.ni_for_ty }]
      | NIUse _ -> [])
    items

let flatten_program_items items =
  ignore (collect_item_paths [] items);
  let known = collect_item_infos [] [] items in
  flatten_modules known [] items

let flatten_program_items_with_core core_items user_items =
  reject_user_core_module user_items;
  flatten_program_items (core_items @ user_items)

type known_paths = {
  known_struct_names : string list;
  known_enum_names : string list;
  known_trait_names : string list;
  known_fn_names : string list;
}

let is_qualified_name name = String.contains name ':'

let require_known kind known name =
  if List.mem name known then ()
  else if is_qualified_name name then failwith ("unknown " ^ kind ^ " path: " ^ name)
  else ()

let rec validate_ty_paths known ty_params (NTy (_, core)) =
  match core with
  | NTUnits | NTIntegers | NTFloats | NTBooleans -> ()
  | NTNamed (path, args) ->
    let name = string_of_path path in
    if not (List.mem name ty_params) then
      require_known "type" (known.known_struct_names @ known.known_enum_names) name;
    List.iter (validate_type_arg_paths known ty_params) args
  | NTFn (args, ret) ->
    List.iter (validate_ty_paths known ty_params) args;
    validate_ty_paths known ty_params ret
  | NTClosure (_, args, ret) ->
    List.iter (validate_ty_paths known ty_params) args;
    validate_ty_paths known ty_params ret
  | NTForall (_, _, body) -> validate_ty_paths known ty_params body
  | NTTypeForall (params, bounds, body) ->
    let ty_params' = params @ ty_params in
    List.iter (validate_trait_bound_paths known ty_params') bounds;
    validate_ty_paths known ty_params' body
  | NTRef (_, _, inner) -> validate_ty_paths known ty_params inner

and validate_type_arg_paths known ty_params = function
  | NTArgLifetime _ -> ()
  | NTArgTy ty -> validate_ty_paths known ty_params ty

and validate_trait_ref_paths known ty_params r =
  let name = string_of_path r.ntr_name in
  require_known "trait" known.known_trait_names name;
  List.iter (validate_type_arg_paths known ty_params) r.ntr_args

and validate_trait_bound_paths known ty_params b =
  List.iter (validate_trait_ref_paths known ty_params) b.ntb_traits

let validate_param_paths known ty_params p =
  validate_ty_paths known ty_params p.np_ty

let rec validate_expr_paths known ty_params value_scope = function
  | NUnit | NLit _ | NPlace _ | NBorrow _ -> ()
  | NVar _ -> ()
  | NLet (_, name, ty_opt, e1, e2) ->
    Option.iter (validate_ty_paths known ty_params) ty_opt;
    validate_expr_paths known ty_params value_scope e1;
    validate_expr_paths known ty_params (name :: value_scope) e2
  | NCall (path, type_args, args) ->
    let name = string_of_path path in
    begin match path with
    | [local] when List.mem local value_scope -> ()
    | _ -> require_known "function" known.known_fn_names name
    end;
    List.iter (validate_type_arg_paths known ty_params) type_args;
    List.iter (validate_expr_paths known ty_params value_scope) args
  | NStruct (path, type_args, fields) ->
    let name = string_of_path path in
    require_known "struct" known.known_struct_names name;
    List.iter (validate_type_arg_paths known ty_params) type_args;
    List.iter (fun (_, e) -> validate_expr_paths known ty_params value_scope e) fields
  | NEnum (path, type_args, _, variant_args, payloads) ->
    let name = string_of_path path in
    require_known "enum" known.known_enum_names name;
    List.iter (validate_type_arg_paths known ty_params) type_args;
    List.iter (validate_type_arg_paths known ty_params) variant_args;
    List.iter (validate_expr_paths known ty_params value_scope) payloads
  | NMatch (scrut, branches) ->
    validate_expr_paths known ty_params value_scope scrut;
    List.iter
      (fun (_, binders, body) ->
        validate_expr_paths known ty_params (binders @ value_scope) body)
      branches
  | NReplace (_, e) | NAssign (_, e) | NDeref e | NDrop e ->
    validate_expr_paths known ty_params value_scope e
  | NIf (cond, then_e, else_e) ->
    validate_expr_paths known ty_params value_scope cond;
    validate_expr_paths known ty_params value_scope then_e;
    validate_expr_paths known ty_params value_scope else_e
  | NClosure (captures, params, ret, body) ->
    List.iter (validate_param_paths known ty_params) params;
    validate_ty_paths known ty_params ret;
    let value_scope' = List.map (fun p -> p.np_name) params @ captures @ value_scope in
    validate_expr_paths known ty_params value_scope' body
  | NLetRec (captures, rec_fns, body) ->
    let rec_names = List.map (fun rf -> rf.nrf_name) rec_fns in
    let rec first_duplicate seen = function
      | [] -> None
      | x :: xs -> if List.mem x seen then Some x else first_duplicate (x :: seen) xs
    in
    begin match first_duplicate [] rec_names with
    | Some name -> failwith ("duplicate let rec function name: " ^ name)
    | None -> ()
    end;
    begin match first_duplicate [] captures with
    | Some name -> failwith ("duplicate let rec capture name: " ^ name)
    | None -> ()
    end;
    List.iter
      (fun name ->
        if not (List.mem name value_scope)
        then failwith ("unknown let rec capture name: " ^ name))
      captures;
    List.iter
      (fun rf ->
        List.iter (validate_param_paths known ty_params) rf.nrf_params;
        validate_ty_paths known ty_params rf.nrf_ret;
        let body_scope =
          List.map (fun p -> p.np_name) rf.nrf_params @ captures @ rec_names @ value_scope in
        validate_expr_paths known ty_params body_scope rf.nrf_body)
      rec_fns;
    validate_expr_paths known ty_params (rec_names @ value_scope) body

let validate_item_paths known = function
  | NIFn f ->
    let (_lts, tys) = split_generics f.nf_generics in
    List.iter (validate_trait_bound_paths known tys) f.nf_bounds;
    List.iter (validate_param_paths known tys) f.nf_params;
    validate_ty_paths known tys f.nf_ret;
    validate_expr_paths known tys (List.map (fun p -> p.np_name) f.nf_params) f.nf_body
  | NIStruct st ->
    let (_lts, tys) = split_generics st.ns_generics in
    List.iter (validate_trait_bound_paths known tys) st.ns_bounds;
    List.iter (fun field -> validate_ty_paths known tys field.nfield_ty) st.ns_fields
  | NIEnum e ->
    let (_lts, tys) = split_generics e.ne_generics in
    List.iter (validate_trait_bound_paths known tys) e.ne_bounds;
    List.iter
      (fun variant -> List.iter (validate_ty_paths known tys) variant.nev_fields)
      e.ne_variants
  | NITrait t ->
    let (_lts, tys) = split_generics t.nt_generics in
    List.iter (validate_trait_bound_paths known tys) t.nt_bounds
  | NIImpl i ->
    let (_lts, tys) = split_generics i.ni_generics in
    let trait_name = string_of_path i.ni_trait_name in
    require_known "trait" known.known_trait_names trait_name;
    List.iter (validate_type_arg_paths known tys) i.ni_trait_args;
    validate_ty_paths known tys i.ni_for_ty
  | NIUse _ -> ()
  | NIModFile (_, name) -> failwith ("unexpanded file module: " ^ name)
  | NIMod _ -> ()

let validate_flattened_paths struct_names enum_names trait_names fn_names items =
  let known = { known_struct_names = struct_names; known_enum_names = enum_names; known_trait_names = trait_names; known_fn_names = fn_names } in
  List.iter (validate_item_paths known) items

let current_depth scope name =
  match List.assoc_opt name scope with
  | Some d -> d
  | None   -> -1

let add_binding scope name =
  let d = current_depth scope name + 1 in
  ((name, d) :: scope, d)

let add_bindings scope names =
  List.fold_left (fun scope name -> fst (add_binding scope name)) scope names

let lookup scope name =
  Stdlib.max 0 (current_depth scope name)

let make_ident name d : ident =
  (name, Big_int_Z.big_int_of_int d)

let add_bindings_with_idents scope names =
  let scope', rev_idents =
    List.fold_left
      (fun (scope_acc, idents_acc) name ->
         let (scope_next, d) = add_binding scope_acc name in
         (scope_next, make_ident name d :: idents_acc))
      (scope, [])
      names
  in
  (scope', List.rev rev_idents)

let ident_of_name scope name =
  make_ident name (lookup scope name)

let rec convert_place scope = function
  | NPVar name -> PVar (ident_of_name scope name)
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
  | NTNamed (path, args) ->
    let s = string_of_path path in
    begin match index_of s ty_scope.type_params with
    | Some i ->
      if args <> [] then failwith ("type parameter cannot take arguments: " ^ s);
      TParam (Big_int_Z.big_int_of_int i)
    | None ->
      let (lts, tys) = split_type_args ty_scope args in
      if List.mem s ty_scope.struct_names then TStruct (s, lts, tys)
      else if List.mem s ty_scope.enum_names then TEnum (s, lts, tys)
      else if args <> [] then TStruct (s, lts, tys)
      else TNamed s
    end
  | NTFn (ts, ret) ->
    TFn (List.map (lower_named_ty ty_scope) ts, lower_named_ty ty_scope ret)
  | NTClosure (env_lt, ts, ret) ->
    TClosure (env_lt, List.map (lower_named_ty ty_scope) ts, lower_named_ty ty_scope ret)
  | NTForall (n, outs, body) ->
    TForall (n, outs, lower_named_ty ty_scope body)
  | NTTypeForall (type_params, bounds, body) ->
    let ty_scope' =
      { ty_scope with type_params = type_params @ ty_scope.type_params }
    in
    TTypeForall
      (Big_int_Z.big_int_of_int (List.length type_params),
       List.map (core_trait_bound_of_named ty_scope' type_params) bounds,
       lower_named_ty ty_scope' body)
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

and core_trait_bound_of_named ty_scope type_params b =
  match index_of b.ntb_type_name type_params with
  | None -> failwith ("unknown type parameter in type-forall trait bound: " ^ b.ntb_type_name)
  | Some i ->
    { core_bound_type_index = Big_int_Z.big_int_of_int i;
      core_bound_traits = List.map (core_trait_ref_of_named ty_scope) b.ntb_traits }

and core_trait_ref_of_named ty_scope r =
  let (lts, args) = split_type_args ty_scope r.ntr_args in
  if lts <> []
  then failwith ("trait bound cannot take lifetime arguments: " ^ string_of_path r.ntr_name);
  { core_trait_ref_name = string_of_path r.ntr_name;
    core_trait_ref_args = args }

let trait_ref_of_named ty_scope r =
  let (lts, args) = split_type_args ty_scope r.ntr_args in
  if lts <> []
  then failwith ("trait bound cannot take lifetime arguments: " ^ string_of_path r.ntr_name);
  { trait_ref_name = string_of_path r.ntr_name;
    trait_ref_args = args }

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
  | NTClosure (_, ts, ret) ->
    List.exists named_ty_has_elided_ref_lifetime ts ||
    named_ty_has_elided_ref_lifetime ret
  | NTForall (_, _, body) ->
    named_ty_has_elided_ref_lifetime body
  | NTTypeForall (_, _, body) ->
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

let trait_bound_of_named ty_scope type_params b =
  match index_of b.ntb_type_name type_params with
  | None -> failwith ("unknown type parameter in trait bound: " ^ b.ntb_type_name)
  | Some i ->
    { bound_type_index = Big_int_Z.big_int_of_int i;
      bound_traits = List.map (trait_ref_of_named ty_scope) b.ntb_traits }

let split_expr_type_args ty_scope args =
  let rec go lts tys = function
    | [] -> (List.rev lts, List.rev tys)
    | NTArgLifetime lt :: rest -> go (lt :: lts) tys rest
    | NTArgTy ty :: rest -> go lts (lower_named_ty ty_scope ty :: tys) rest
  in
  go [] [] args

let lower_call_type_args ty_scope args =
  let (lts, tys) = split_expr_type_args ty_scope args in
  if lts <> []
  then failwith "explicit generic direct calls do not accept lifetime arguments"
  else tys

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
  | NCall (f_path, type_args, args) ->
    let f = string_of_path f_path in
    let args' = List.map (convert fn_names ty_scope scope) args in
    if type_args = [] then
      if in_scope scope f then ECallExpr (EVar (make_ident f (lookup scope f)), args')
      else ECall (make_ident f 0, args')
    else if in_scope scope f then
      failwith "explicit type arguments are only supported for direct function calls"
    else
      ECallGeneric (make_ident f 0, lower_call_type_args ty_scope type_args, args')
  | NStruct (name_path, args, fields) ->
    let name = string_of_path name_path in
    let (lts, tys) = split_expr_type_args ty_scope args in
    EStruct (name, lts, tys,
      List.map (fun (field, e1) -> (field, convert fn_names ty_scope scope e1)) fields)
  | NEnum (enum_name_path, args, variant_name, variant_args, payloads) ->
    let enum_name = string_of_path enum_name_path in
    let (lts, tys) = split_expr_type_args ty_scope args in
    let (variant_lts, variant_tys) = split_expr_type_args ty_scope variant_args in
    if variant_tys <> [] then failwith "variant-local type arguments are not supported";
    EEnum (enum_name, variant_name, lts, variant_lts, tys,
      List.map (convert fn_names ty_scope scope) payloads)
  | NMatch (scrut, branches) ->
    EMatch
      (convert fn_names ty_scope scope scrut,
       List.map
         (fun (variant, binders, body) ->
            let (branch_scope, binder_ids) = add_bindings_with_idents scope binders in
            ((variant, binder_ids), convert fn_names ty_scope branch_scope body))
         branches)
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
  | NClosure _ ->
    failwith "closure literals must be lowered through raw elaboration"
  | NLetRec _ ->
    failwith "let rec is not implemented yet"

let add_capture_binding outer_scope closure_scope name =
  (name, lookup outer_scope name) :: closure_scope

type rec_scope = (string * ident) list

let rec_ident rec_scope name =
  List.assoc_opt name rec_scope

let local_rec_counter = ref 0

let fresh_local_rec_ident name =
  let id = !local_rec_counter in
  incr local_rec_counter;
  make_ident ("__facet_local_rec_" ^ string_of_int id ^ "_" ^ name) 0

let lower_param ty_scope scope np =
  let (scope', d) = add_binding scope np.np_name in
  let p = { param_mutability = np.np_mutability;
            param_name       = make_ident np.np_name d;
            param_ty         = lower_named_ty ty_scope np.np_ty } in
  (scope', p)

let rec convert_raw (fn_names : string list) (ty_scope : ty_scope) (scope : scope) (rec_scope : rec_scope) (e : named_expr) : raw_expr =
  match e with
  | NUnit           -> RawUnit
  | NLit l          -> RawLit l
  | NVar name       ->
    if in_scope scope name then RawVar (ident_of_name scope name)
    else begin match rec_ident rec_scope name with
    | Some id -> RawFn id
    | None ->
      if List.mem name fn_names then RawFn (make_ident name 0)
      else RawVar (ident_of_name scope name)
    end
  | NPlace p        -> RawPlace (convert_place scope p)
  | NDrop e1        -> RawDrop (convert_raw fn_names ty_scope scope rec_scope e1)
  | NReplace (p, e1) ->
    RawReplace (convert_place scope p, convert_raw fn_names ty_scope scope rec_scope e1)
  | NAssign (p, e1) ->
    RawAssign (convert_place scope p, convert_raw fn_names ty_scope scope rec_scope e1)
  | NBorrow (rk, p) ->
    RawBorrow (rk, convert_place scope p)
  | NDeref e1 ->
    RawDeref (convert_raw fn_names ty_scope scope rec_scope e1)
  | NCall (f_path, type_args, args) ->
    let f = string_of_path f_path in
    let args' = List.map (convert_raw fn_names ty_scope scope rec_scope) args in
    if type_args = [] then
      if in_scope scope f then RawCallExpr (RawVar (ident_of_name scope f), args')
      else begin match rec_ident rec_scope f with
      | Some id -> RawCall (id, args')
      | None -> RawCall (make_ident f 0, args')
      end
    else if in_scope scope f || Option.is_some (rec_ident rec_scope f) then
      failwith "explicit type arguments are only supported for direct function calls"
    else
      RawCallGeneric (make_ident f 0, lower_call_type_args ty_scope type_args, args')
  | NStruct (name_path, args, fields) ->
    let name = string_of_path name_path in
    let (lts, tys) = split_expr_type_args ty_scope args in
    RawStruct (name, lts, tys,
      List.map (fun (field, e1) -> (field, convert_raw fn_names ty_scope scope rec_scope e1)) fields)
  | NEnum (enum_name_path, args, variant_name, variant_args, payloads) ->
    let enum_name = string_of_path enum_name_path in
    let (lts, tys) = split_expr_type_args ty_scope args in
    let (variant_lts, variant_tys) = split_expr_type_args ty_scope variant_args in
    if variant_tys <> [] then failwith "variant-local type arguments are not supported";
    RawEnum (enum_name, variant_name, lts, variant_lts, tys,
      List.map (convert_raw fn_names ty_scope scope rec_scope) payloads)
  | NMatch (scrut, branches) ->
    RawMatch
      (convert_raw fn_names ty_scope scope rec_scope scrut,
       List.map
         (fun (variant, binders, body) ->
            let (branch_scope, binder_ids) = add_bindings_with_idents scope binders in
            ((variant, binder_ids), convert_raw fn_names ty_scope branch_scope rec_scope body))
         branches)
  | NLet (m, name, Some ty, e1, e2) ->
    if named_ty_has_elided_ref_lifetime ty
    then failwith "cannot elide lifetime in local type annotation";
    let e1' = convert_raw fn_names ty_scope scope rec_scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert_raw fn_names ty_scope scope' rec_scope e2 in
    RawLet (m, make_ident name d, lower_named_ty ty_scope ty, e1', e2')
  | NLet (m, name, None, e1, e2) ->
    let e1' = convert_raw fn_names ty_scope scope rec_scope e1 in
    let (scope', d) = add_binding scope name in
    let e2' = convert_raw fn_names ty_scope scope' rec_scope e2 in
    RawLetInfer (m, make_ident name d, e1', e2')
  | NIf (cond, then_e, else_e) ->
    RawIf (convert_raw fn_names ty_scope scope rec_scope cond,
           convert_raw fn_names ty_scope scope rec_scope then_e,
           convert_raw fn_names ty_scope scope rec_scope else_e)
  | NClosure (captures, params, ret, body) ->
    let capture_ids = List.map (ident_of_name scope) captures in
    let closure_scope = List.fold_left (add_capture_binding scope) [] captures in
    let (body_scope, raw_params) =
      List.fold_left
        (fun (sc, acc) np ->
          let (sc', p) = lower_param ty_scope sc np in
          (sc', acc @ [p]))
        (closure_scope, []) params
    in
    RawClosure (capture_ids, raw_params, lower_named_ty ty_scope ret,
      convert_raw fn_names ty_scope body_scope rec_scope body)
  | NLetRec (captures, rec_fns, body) ->
    let capture_ids = List.map (ident_of_name scope) captures in
    let rec_names = List.map (fun rf -> rf.nrf_name) rec_fns in
    let rec_ids = List.map fresh_local_rec_ident rec_names in
    let rec_scope' = List.combine rec_names rec_ids @ rec_scope in
    let lower_rec_fn rf rec_id =
      let closure_scope = List.fold_left (add_capture_binding scope) [] captures in
      let (body_scope, raw_params) =
        List.fold_left
          (fun (sc, acc) np ->
            let (sc', p) = lower_param ty_scope sc np in
            (sc', acc @ [p]))
          (closure_scope, []) rf.nrf_params
      in
      MkRawRecFn (rec_id, raw_params, lower_named_ty ty_scope rf.nrf_ret,
        convert_raw fn_names ty_scope body_scope rec_scope' rf.nrf_body)
    in
    RawLetRec (capture_ids, List.map2 lower_rec_fn rec_fns rec_ids,
      convert_raw fn_names ty_scope scope rec_scope' body)

let convert_fn_def_with_names struct_names enum_names fn_names (f : named_fn_def) : fn_def =
  let (lts, tys) = split_generics f.nf_generics in
  let ty_scope = {
    type_params = tys;
    struct_names;
    enum_names;
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
    ([], [], List.length lts, []) f.nf_params
  in
  let ret_ty = lower_output_ty ty_scope input_lts f.nf_ret in
  { fn_name      = make_ident f.nf_name 0;
    fn_lifetimes = Big_int_Z.big_int_of_int next_lifetime;
    fn_outlives = f.nf_outlives;
    fn_captures  = [];
    fn_params    = params;
    fn_ret       = ret_ty;
    fn_body      = convert fn_names ty_scope scope f.nf_body;
    fn_type_params = Big_int_Z.big_int_of_int (List.length tys);
    fn_bounds = List.map (trait_bound_of_named ty_scope tys) f.nf_bounds }

let convert_raw_fn_def_with_names struct_names enum_names fn_names (f : named_fn_def) : raw_fn_def =
  let (lts, tys) = split_generics f.nf_generics in
  let ty_scope = {
    type_params = tys;
    struct_names;
    enum_names;
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
    ([], [], List.length lts, []) f.nf_params
  in
  let ret_ty = lower_output_ty ty_scope input_lts f.nf_ret in
  { raw_fn_name      = make_ident f.nf_name 0;
    raw_fn_lifetimes = Big_int_Z.big_int_of_int next_lifetime;
    raw_fn_outlives = f.nf_outlives;
    raw_fn_params    = params;
    raw_fn_ret       = ret_ty;
    raw_fn_body      = convert_raw fn_names ty_scope scope [] f.nf_body;
    raw_fn_type_params = Big_int_Z.big_int_of_int (List.length tys);
    raw_fn_bounds = List.map (trait_bound_of_named ty_scope tys) f.nf_bounds }

let convert_struct struct_names enum_names s =
  let (lts, tys) = split_generics s.ns_generics in
  let ty_scope = { type_params = tys; struct_names; enum_names } in
  { struct_name = s.ns_name;
    struct_lifetimes = Big_int_Z.big_int_of_int (List.length lts);
    struct_type_params = Big_int_Z.big_int_of_int (List.length tys);
    struct_bounds = List.map (trait_bound_of_named ty_scope tys) s.ns_bounds;
    struct_fields =
      List.map
        (fun f ->
          { field_name = f.nfield_name;
            field_mutability = f.nfield_mutability;
            field_ty = lower_named_ty ty_scope f.nfield_ty })
        s.ns_fields }

let convert_enum struct_names enum_names e =
  let (lts, tys) = split_generics e.ne_generics in
  let ty_scope = { type_params = tys; struct_names; enum_names } in
  { enum_name = e.ne_name;
    enum_lifetimes = Big_int_Z.big_int_of_int (List.length lts);
    enum_type_params = Big_int_Z.big_int_of_int (List.length tys);
    enum_bounds = List.map (trait_bound_of_named ty_scope tys) e.ne_bounds;
    enum_outlives = e.ne_outlives;
    enum_variants =
      List.map
        (fun v ->
          { enum_variant_name = v.nev_name;
            enum_variant_lifetimes = Big_int_Z.big_int_of_int (List.length v.nev_lifetimes);
            enum_variant_fields = List.map (lower_named_ty ty_scope) v.nev_fields })
        e.ne_variants }

let convert_trait struct_names enum_names t =
  let (_lts, tys) = split_generics t.nt_generics in
  let ty_scope = { type_params = tys; struct_names; enum_names } in
  { trait_name = t.nt_name;
    trait_type_params = Big_int_Z.big_int_of_int (List.length tys);
    trait_bounds = List.map (trait_bound_of_named ty_scope tys) t.nt_bounds }

let convert_impl struct_names enum_names i =
  let (lts, tys) = split_generics i.ni_generics in
  let ty_scope = { type_params = tys; struct_names; enum_names } in
  let (trait_lts, trait_args) = split_expr_type_args ty_scope i.ni_trait_args in
  if trait_lts <> []
  then failwith ("trait impl target cannot take lifetime arguments: " ^ string_of_path i.ni_trait_name);
  { impl_lifetimes = Big_int_Z.big_int_of_int (List.length lts);
    impl_type_params = Big_int_Z.big_int_of_int (List.length tys);
    impl_trait_name = string_of_path i.ni_trait_name;
    impl_trait_args = trait_args;
    impl_for_ty = lower_named_ty ty_scope i.ni_for_ty }

let duplicate_name names =
  let rec go seen = function
    | [] -> None
    | x :: xs -> if List.mem x seen then Some x else go (x :: seen) xs
  in
  go [] names

let synthetic_name_prefix = "__facet_"

let has_prefix prefix s =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix

let reject_reserved_synthetic_names names =
  match List.find_opt (has_prefix synthetic_name_prefix) names with
  | Some name -> failwith ("reserved top-level name: " ^ name)
  | None -> ()

let validate_env env =
  let top_names =
    List.map (fun s -> s.struct_name) env.env_structs @
    List.map (fun e -> e.enum_name) env.env_enums @
    List.map (fun t -> t.trait_name) env.env_traits @
    List.map (fun f -> fst f.fn_name) env.env_fns
  in
  match duplicate_name top_names with
  | Some name -> Some ("duplicate top-level name: " ^ name)
  | None ->
    let zero = Big_int_Z.zero_big_int in
    let big_len xs = Big_int_Z.big_int_of_int (List.length xs) in
    let find_struct name =
      List.find_opt (fun s -> s.struct_name = name) env.env_structs
    in
    let find_enum name =
      List.find_opt (fun e -> e.enum_name = name) env.env_enums
    in
    let find_trait name =
      List.find_opt (fun t -> t.trait_name = name) env.env_traits
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
      | TEnum (name, lts, args) ->
        begin match find_enum name with
        | None -> Some ("unknown enum type: " ^ name)
        | Some e ->
          if not (Big_int_Z.eq_big_int (big_len lts) e.enum_lifetimes)
          then Some ("enum lifetime arity mismatch: " ^ name)
          else if not (Big_int_Z.eq_big_int (big_len args) e.enum_type_params)
          then Some ("enum type arity mismatch: " ^ name)
          else
            first_some
              (List.map (lifetime_error lt_params bound_depth) lts @
               List.map (type_error ty_params lt_params bound_depth) args)
        end
      | TFn (args, ret) ->
        first_some
          (List.map (type_error ty_params lt_params bound_depth) args @
           [type_error ty_params lt_params bound_depth ret])
      | TClosure (env_lt, args, ret) ->
        begin match lifetime_error lt_params bound_depth env_lt with
        | Some _ as err -> err
        | None ->
          first_some
            (List.map (type_error ty_params lt_params bound_depth) args @
             [type_error ty_params lt_params bound_depth ret])
        end
      | TForall (n, outs, body) ->
        let bound_depth' = Big_int_Z.add_big_int n bound_depth in
        begin match outlives_error lt_params bound_depth' outs with
        | Some _ as err -> err
        | None -> type_error ty_params lt_params bound_depth' body
        end
      | TTypeForall (n, bounds, body) ->
        let ty_params' = Big_int_Z.add_big_int n ty_params in
        let validate_core_bound b =
          if Big_int_Z.ge_big_int b.core_bound_type_index n
          then Some "type-forall trait bound refers to an out-of-range bound type parameter"
          else
            let validate_trait_ref tr =
              match find_trait tr.core_trait_ref_name with
              | None -> Some ("unknown trait in type-forall bound: " ^ tr.core_trait_ref_name)
              | Some trait_def ->
                if not (Big_int_Z.eq_big_int (big_len tr.core_trait_ref_args) trait_def.trait_type_params)
                then Some ("type-forall trait bound arity mismatch: " ^ tr.core_trait_ref_name)
                else
                  first_some
                    (List.map (type_error ty_params' lt_params bound_depth) tr.core_trait_ref_args)
            in
            first_some (List.map validate_trait_ref b.core_bound_traits)
        in
        first_some
          (List.map validate_core_bound bounds @
           [type_error ty_params' lt_params bound_depth body])
      | TRef (lt, _, inner) ->
        begin match lifetime_error lt_params bound_depth lt with
        | Some _ as err -> err
        | None -> type_error ty_params lt_params bound_depth inner
        end
    in
    let validate_bound ty_params lt_params b =
      if Big_int_Z.ge_big_int b.bound_type_index ty_params
      then Some "trait bound refers to an out-of-range type parameter"
      else
        let validate_trait_ref tr =
          match find_trait tr.trait_ref_name with
          | None -> Some ("unknown trait in bound: " ^ tr.trait_ref_name)
          | Some trait_def ->
            if not (Big_int_Z.eq_big_int (big_len tr.trait_ref_args) trait_def.trait_type_params)
            then Some ("trait bound arity mismatch: " ^ tr.trait_ref_name)
            else
              first_some
                (List.map (type_error ty_params lt_params zero) tr.trait_ref_args)
        in
        first_some (List.map validate_trait_ref b.bound_traits)
    in
    let rec type_struct_refs (MkTy (_, core)) =
      match core with
      | TStruct (name, _, args) ->
        name :: List.concat_map type_struct_refs args
      | TEnum (_, _, args) ->
        List.concat_map type_struct_refs args
      | TFn (args, ret) ->
        List.concat_map type_struct_refs args @ type_struct_refs ret
      | TClosure (_, args, ret) ->
        List.concat_map type_struct_refs args @ type_struct_refs ret
      | TForall (_, _, body) -> type_struct_refs body
      | TTypeForall (_, bounds, body) ->
        List.concat_map
          (fun b ->
            List.concat_map
              (fun tr -> List.concat_map type_struct_refs tr.core_trait_ref_args)
              b.core_bound_traits)
          bounds @
        type_struct_refs body
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
           List.map (validate_bound s.struct_type_params s.struct_lifetimes) s.struct_bounds)
    in
    let validate_enum e =
      match duplicate_name (List.map (fun v -> v.enum_variant_name) e.enum_variants) with
      | Some variant -> Some ("duplicate variant in enum " ^ e.enum_name ^ ": " ^ variant)
      | None ->
        first_some
          (List.concat_map
             (fun v ->
                List.map (type_error e.enum_type_params
                  (Big_int_Z.add_big_int e.enum_lifetimes v.enum_variant_lifetimes) zero)
                  v.enum_variant_fields)
             e.enum_variants @
           List.map (validate_bound e.enum_type_params e.enum_lifetimes) e.enum_bounds @
           [outlives_error e.enum_lifetimes zero e.enum_outlives])
    in
    let validate_trait t =
      first_some (List.map (validate_bound t.trait_type_params zero) t.trait_bounds)
    in
    let validate_impl i =
      match find_trait i.impl_trait_name with
      | None -> Some ("unknown trait in impl: " ^ i.impl_trait_name)
      | Some trait_def ->
        if not (Big_int_Z.eq_big_int (big_len i.impl_trait_args) trait_def.trait_type_params)
        then Some ("trait type arity mismatch: " ^ i.impl_trait_name)
        else
          let own_bound_error =
            match check_struct_bounds env trait_def.trait_bounds i.impl_trait_args with
            | None -> None
            | Some _ -> Some ("trait own bound not satisfied: " ^ i.impl_trait_name)
          in
          first_some
            (List.map
               (type_error i.impl_type_params i.impl_lifetimes zero)
               i.impl_trait_args @
             [type_error i.impl_type_params i.impl_lifetimes zero i.impl_for_ty;
              own_bound_error])
    in
    let validate_fn f =
      first_some
        (List.map
           (fun p -> type_error f.fn_type_params f.fn_lifetimes zero p.param_ty)
           f.fn_params @
         [type_error f.fn_type_params f.fn_lifetimes zero f.fn_ret;
          outlives_error f.fn_lifetimes zero f.fn_outlives] @
         List.map (validate_bound f.fn_type_params f.fn_lifetimes) f.fn_bounds)
    in
    match first_some (List.map validate_acyclic_struct env.env_structs @
                      List.map validate_struct env.env_structs @
                      List.map validate_enum env.env_enums @
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

let convert_program_items_from_flattened items : global_env =
  let structs = List.filter_map (function NIStruct s -> Some s | _ -> None) items in
  let enums = List.filter_map (function NIEnum e -> Some e | _ -> None) items in
  let traits = List.filter_map (function NITrait t -> Some t | _ -> None) items in
  let impls = List.filter_map (function NIImpl i -> Some i | _ -> None) items in
  let fns = List.filter_map (function NIFn f -> Some f | _ -> None) items in
  let struct_names = List.map (fun s -> s.ns_name) structs in
  let enum_names = List.map (fun e -> e.ne_name) enums in
  let fn_names = List.map (fun f -> f.nf_name) fns in
  validate_flattened_paths struct_names enum_names (List.map (fun t -> t.nt_name) traits) fn_names items;
  let top_names =
    List.map (fun s -> s.ns_name) structs @
    enum_names @
    List.map (fun t -> t.nt_name) traits @
    fn_names
  in
  reject_reserved_synthetic_names top_names;
  begin match duplicate_name top_names with
  | Some name -> failwith ("duplicate top-level name: " ^ name)
  | None -> ()
  end;
  let base_env = {
    env_structs = List.map (convert_struct struct_names enum_names) structs;
    env_enums = List.map (convert_enum struct_names enum_names) enums;
    env_traits = List.map (convert_trait struct_names enum_names) traits;
    env_impls = List.map (convert_impl struct_names enum_names) impls;
    env_local_bounds = [];
    env_fns = [];
  } in
  begin match validate_env base_env with
  | None -> ()
  | Some msg -> failwith msg
  end;
  let raw_fns =
    List.map (convert_raw_fn_def_with_names struct_names enum_names fn_names) fns in
  let env =
    match elaborate_raw_global_env base_env raw_fns with
    | Infer_ok env -> env
    | Infer_err _ -> failwith "raw elaboration failed"
  in
  match validate_env env with
  | None -> env
  | Some msg -> failwith msg

let convert_program_items items =
  convert_program_items_from_flattened (flatten_program_items items)

let convert_program_items_with_core core_items user_items =
  convert_program_items_from_flattened (flatten_program_items_with_core core_items user_items)

let convert_program (items : named_item list) : fn_def list =
  (convert_program_items items).env_fns

let convert_fn_def f = convert_fn_def_with_names [] [] [] f
