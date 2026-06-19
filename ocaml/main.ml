open TypeChecker

let string_of_usage = function
  | ULinear       -> "linear"
  | UAffine       -> "affine"
  | UUnrestricted -> "unrestricted"

let rec string_of_ty_core : ty typeCore -> string = function
  | TUnits      -> "()"
  | TIntegers   -> "isize"
  | TFloats     -> "f64"
  | TBooleans   -> "bool"
  | TNamed s    -> s
  | TParam i    -> Printf.sprintf "T%s" (Big_int_Z.string_of_big_int i)
  | TStruct (name, lts, args) ->
    let lt_s =
      List.map (fun _ -> "'_") lts
    in
    let arg_s = List.map string_of_ty args in
    let all = lt_s @ arg_s in
    if all = [] then name
    else Printf.sprintf "%s<%s>" name (String.concat ", " all)
  | TEnum (name, lts, args) ->
    let lt_s =
      List.map (fun _ -> "'_") lts
    in
    let arg_s = List.map string_of_ty args in
    let all = lt_s @ arg_s in
    if all = [] then name
    else Printf.sprintf "%s<%s>" name (String.concat ", " all)
  | TFn (ts, r) ->
    Printf.sprintf "fn(%s) -> %s"
      (String.concat ", " (List.map string_of_ty ts))
      (string_of_ty r)
  | TClosure (_, ts, r) ->
    Printf.sprintf "closure(%s) -> %s"
      (String.concat ", " (List.map string_of_ty ts))
      (string_of_ty r)
  | TForall (n, _, body) ->
    Printf.sprintf "for<%s> %s"
      (String.concat ", "
         (List.init (Big_int_Z.int_of_big_int n)
            (fun i -> Printf.sprintf "'_%d" i)))
      (string_of_ty body)
  | TTypeForall (n, _, body) ->
    Printf.sprintf "for<%s> %s"
      (String.concat ", "
         (List.init (Big_int_Z.int_of_big_int n)
            (fun i -> Printf.sprintf "T%d" i)))
      (string_of_ty body)
  | TAssoc (for_ty, trait_name, trait_args, assoc_name) ->
    let trait =
      if trait_args = [] then trait_name
      else Printf.sprintf "%s<%s>" trait_name
        (String.concat ", " (List.map string_of_ty trait_args))
    in
    Printf.sprintf "<%s as %s>::%s" (string_of_ty for_ty) trait assoc_name
  | TRef (_, RShared, t) -> "&" ^ string_of_ty t
  | TRef (_, RUnique, t) -> "&mut " ^ string_of_ty t

and string_of_ty (MkTy (u, c)) =
  string_of_usage u ^ " " ^ string_of_ty_core c

let string_of_ident (name, idx) =
  Printf.sprintf "%s#%s" name (Big_int_Z.string_of_big_int idx)

type diagnostic_span = unit

type diagnostic_entry = {
  original_name : string;
  span          : diagnostic_span option;
}

type diagnostic_map = (ident * diagnostic_entry) list

let diagnostic_entry name =
  { original_name = name; span = None }

let diagnostic_add alpha_id original_id map =
  (alpha_id, diagnostic_entry (fst original_id)) :: map

let rec diagnostic_add_place map original alpha =
  match original, alpha with
  | PVar original_id, PVar alpha_id ->
    diagnostic_add alpha_id original_id map
  | PDeref original_p, PDeref alpha_p ->
    diagnostic_add_place map original_p alpha_p
  | PField (original_p, _), PField (alpha_p, _) ->
    diagnostic_add_place map original_p alpha_p
  | _ -> map

let rec diagnostic_add_expr map original alpha =
  match original, alpha with
  | EUnit, EUnit
  | ELit _, ELit _ ->
    map
  | EVar original_id, EVar alpha_id
  | EFn original_id, EFn alpha_id ->
    let map = diagnostic_add alpha_id original_id map in
    map
  | ECall (original_id, original_args), ECall (alpha_id, alpha_args) ->
    let map = diagnostic_add alpha_id original_id map in
    diagnostic_add_exprs map original_args alpha_args
  | ECallGeneric (original_id, _, original_args),
    ECallGeneric (alpha_id, _, alpha_args) ->
    let map = diagnostic_add alpha_id original_id map in
    diagnostic_add_exprs map original_args alpha_args
  | EPlace original_p, EPlace alpha_p ->
    diagnostic_add_place map original_p alpha_p
  | ELet (_, original_id, _, original_e1, original_e2),
    ELet (_, alpha_id, _, alpha_e1, alpha_e2) ->
    let map = diagnostic_add_expr map original_e1 alpha_e1 in
    let map = diagnostic_add alpha_id original_id map in
    diagnostic_add_expr map original_e2 alpha_e2
  | ELetInfer (_, original_id, original_e1, original_e2),
    ELetInfer (_, alpha_id, alpha_e1, alpha_e2) ->
    let map = diagnostic_add_expr map original_e1 alpha_e1 in
    let map = diagnostic_add alpha_id original_id map in
    diagnostic_add_expr map original_e2 alpha_e2
  | ECallExpr (original_callee, original_args),
    ECallExpr (alpha_callee, alpha_args) ->
    let map = diagnostic_add_expr map original_callee alpha_callee in
    diagnostic_add_exprs map original_args alpha_args
  | ECallExprGeneric (original_callee, _, original_args),
    ECallExprGeneric (alpha_callee, _, alpha_args) ->
    let map = diagnostic_add_expr map original_callee alpha_callee in
    diagnostic_add_exprs map original_args alpha_args
  | EStruct (_, _, _, original_fields), EStruct (_, _, _, alpha_fields) ->
    diagnostic_add_fields map original_fields alpha_fields
  | EEnum (_, _, _, _, _, original_payloads), EEnum (_, _, _, _, _, alpha_payloads) ->
    diagnostic_add_exprs map original_payloads alpha_payloads
  | EReplace (original_p, original_e), EReplace (alpha_p, alpha_e)
  | EAssign (original_p, original_e), EAssign (alpha_p, alpha_e) ->
    let map = diagnostic_add_place map original_p alpha_p in
    diagnostic_add_expr map original_e alpha_e
  | EBorrow (_, original_p), EBorrow (_, alpha_p) ->
    diagnostic_add_place map original_p alpha_p
  | EDeref original_e, EDeref alpha_e
  | EDrop original_e, EDrop alpha_e ->
    diagnostic_add_expr map original_e alpha_e
  | EIf (original_e1, original_e2, original_e3),
    EIf (alpha_e1, alpha_e2, alpha_e3) ->
    let map = diagnostic_add_expr map original_e1 alpha_e1 in
    let map = diagnostic_add_expr map original_e2 alpha_e2 in
    diagnostic_add_expr map original_e3 alpha_e3
  | _ -> map

and diagnostic_add_exprs map originals alphas =
  match originals, alphas with
  | original :: originals, alpha :: alphas ->
    diagnostic_add_exprs (diagnostic_add_expr map original alpha) originals alphas
  | _ -> map

and diagnostic_add_fields map originals alphas =
  match originals, alphas with
  | (_, original_e) :: originals, (_, alpha_e) :: alphas ->
    diagnostic_add_fields (diagnostic_add_expr map original_e alpha_e) originals alphas
  | _ -> map

let diagnostic_add_param map original alpha =
  diagnostic_add alpha.param_name original.param_name map

let diagnostic_add_fn map original alpha =
  let map = diagnostic_add alpha.fn_name original.fn_name map in
  let map =
    List.fold_left2 diagnostic_add_param map original.fn_params alpha.fn_params
  in
  diagnostic_add_expr map original.fn_body alpha.fn_body

let diagnostic_map_of_envs original_env alpha_env =
  try
    List.fold_left2 diagnostic_add_fn [] original_env.env_fns alpha_env.env_fns
  with Invalid_argument _ ->
    []

let diagnostic_lookup (map : diagnostic_map) id =
  match List.find_opt (fun (id', _) -> ident_eqb id id') map with
  | Some (_, entry) -> Some entry.original_name
  | None -> None

let string_of_diagnostic_ident diagnostics id =
  match diagnostic_lookup diagnostics id with
  | Some name -> name
  | None -> string_of_ident id

let rec string_of_infer_error ?(diagnostics = []) = function
  | ErrUnknownVar id      ->
    Printf.sprintf "unknown variable: %s" (string_of_diagnostic_ident diagnostics id)
  | ErrAlreadyConsumed id ->
    Printf.sprintf "variable already consumed: %s" (string_of_diagnostic_ident diagnostics id)
  | ErrTypeMismatch (c1, c2) ->
    Printf.sprintf "type mismatch: expected %s, got %s"
      (string_of_ty_core c1) (string_of_ty_core c2)
  | ErrNotMutable id ->
    Printf.sprintf "assignment target is not mutable: %s" (string_of_diagnostic_ident diagnostics id)
  | ErrUsageMismatch (u1, u2) ->
    Printf.sprintf "usage mismatch: expected %s, got %s"
      (string_of_usage u1) (string_of_usage u2)
  | ErrFunctionNotFound id ->
    Printf.sprintf "function not found: %s" (string_of_diagnostic_ident diagnostics id)
  | ErrArityMismatch      -> "arity mismatch"
  | ErrContextCheckFailed -> "context check failed (linear variable not consumed)"
  | ErrNotImplemented     -> "not implemented (type inference for let without annotation)"
  | ErrImmutableBorrow id ->
    Printf.sprintf "cannot borrow immutable variable as mutable: %s" (string_of_diagnostic_ident diagnostics id)
  | ErrNotAReference c    ->
    Printf.sprintf "type is not a reference: %s" (string_of_ty_core c)
  | ErrNotAFunction c    ->
    Printf.sprintf "type is not a function: %s" (string_of_ty_core c)
  | ErrBorrowConflict id  ->
    Printf.sprintf "borrow conflict: %s is already borrowed incompatibly"
      (string_of_diagnostic_ident diagnostics id)
  | ErrLifetimeLeak ->
    "lifetime leak: function returns a reference to a local (dangling reference)"
  | ErrLifetimeConflict ->
    "lifetime conflict: conflicting lifetime constraints in function call"
  | ErrHrtBoundUnsatisfied ->
    "higher-rank lifetime bound is not satisfied at this call site"
  | ErrHrtUnresolvedBound ->
    "higher-rank lifetime could not be resolved from the call arguments"
  | ErrHrtMonomorphicUsedBound ->
    "monomorphic function cannot be used where a higher-rank function with used bound lifetimes is required"
  | ErrMalformedHrtBody c ->
    Printf.sprintf "higher-rank type body is not a function: %s" (string_of_ty_core c)
  | ErrStructNotFound name ->
    Printf.sprintf "struct not found: %s" name
  | ErrEnumNotFound name ->
    Printf.sprintf "enum not found: %s" name
  | ErrVariantNotFound name ->
    Printf.sprintf "enum variant not found: %s" name
  | ErrNotAnEnum c ->
    Printf.sprintf "type is not an enum: %s" (string_of_ty_core c)
  | ErrDuplicateVariant name ->
    Printf.sprintf "duplicate match branch: %s" name
  | ErrMissingVariant name ->
    Printf.sprintf "missing match branch: %s" name
  | ErrMatchPayloadUnsupported name ->
    Printf.sprintf "match branch payloads are not supported for variant: %s" name
  | ErrFieldNotFound name ->
    Printf.sprintf "field not found: %s" name
  | ErrDuplicateField name ->
    Printf.sprintf "duplicate field: %s" name
  | ErrDuplicateParam id ->
    Printf.sprintf "duplicate parameter: %s" (string_of_diagnostic_ident diagnostics id)
  | ErrMissingField name ->
    Printf.sprintf "missing field: %s" name
  | ErrTraitImplNotFound (name, ty) ->
    Printf.sprintf "trait impl not found: %s for %s" name (string_of_ty ty)
  | ErrTraitImplAmbiguous (name, ty) ->
    Printf.sprintf "trait impl is ambiguous: %s for %s" name (string_of_ty ty)
  | ErrTypeArgInferenceFailed ->
    "could not infer generic type arguments"
  | ErrEndToEndSafetyGateFailed ->
    "end-to-end safety gate failed"
  | ErrGlobalNamesNotUnique ->
    "global names are not unique"
  | ErrInFunction (id, err) ->
    Printf.sprintf "in function %s: %s"
      (string_of_diagnostic_ident diagnostics id)
      (string_of_infer_error ~diagnostics err)


let parse_file_raw filename =
  let ic = try open_in filename
    with Sys_error msg ->
      Printf.eprintf "Error: cannot open file: %s\n" msg;
      exit 1
  in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let buf = Sedlexing.Utf8.from_string content in
  Sedlexing.set_filename buf filename;
  let state = Lexer.make_state filename buf in
  let lexer_fn = Lexer.provider state in
  try MenhirLib.Convert.Simplified.traditional2revised Parser.program lexer_fn
  with
  | Lexer.LexError (pos, msg) ->
    Printf.eprintf "Lex error at %s:%d:%d: %s\n"
      pos.Lexer.pos_fname
      pos.Lexer.pos_lnum
      (pos.Lexer.pos_cnum - pos.Lexer.pos_bol)
      msg;
    exit 1
  | Parser.Error ->
    let (start, _) = Sedlexing.lexing_positions buf in
    Printf.eprintf "Parse error at %s:%d:%d\n"
      filename
      start.Lexing.pos_lnum
      (start.Lexing.pos_cnum - start.Lexing.pos_bol);
    exit 1


let normalize_path path =
  let path =
    if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path
  in
  let is_abs = String.length path > 0 && path.[0] = '/' in
  let parts = String.split_on_char '/' path in
  let parts =
    List.fold_left
      (fun acc part ->
         match part, acc with
         | "", _ | ".", _ -> acc
         | "..", _ :: rest -> rest
         | "..", [] -> acc
         | _, _ -> part :: acc)
      []
      parts
    |> List.rev
  in
  let joined = String.concat "/" parts in
  if is_abs then "/" ^ joined else joined

let is_regular_file path =
  Sys.file_exists path && not (Sys.is_directory path)

let path_within root path =
  let root = normalize_path root in
  let path = normalize_path path in
  path = root || String.starts_with ~prefix:(root ^ "/") path

let ensure_within_package package_root name path =
  match package_root with
  | None -> path
  | Some root ->
    if path_within root path then path
    else failwith ("file module escapes package root: " ^ name)

let module_file_path ?package_root declaring_file name =
  let dir = Filename.dirname declaring_file in
  let flat = normalize_path (Filename.concat dir (name ^ ".facet")) in
  let nested = normalize_path (Filename.concat (Filename.concat dir name) "mod.facet") in
  let path =
    match is_regular_file flat, is_regular_file nested with
    | true, false -> flat
    | false, true -> nested
    | true, true -> failwith ("duplicate file module candidates: " ^ name)
    | false, false -> failwith ("missing file module: " ^ name)
  in
  ensure_within_package package_root name path

let module_decl_name = function
  | Ast.NIMod (_, name, _) -> Some name
  | Ast.NIModFile (_, name) -> Some name
  | _ -> None

let reject_duplicate_module_decls items =
  let rec go seen = function
    | [] -> ()
    | item :: rest ->
      match module_decl_name item with
      | None -> go seen rest
      | Some name ->
        if List.mem name seen then failwith ("duplicate module declaration: " ^ name)
        else go (name :: seen) rest
  in
  go [] items

let cycle_message path stack =
  let chain = List.rev (path :: stack) in
  "file module cycle: " ^ String.concat " -> " chain

let rec load_source_file ?package_root stack filename =
  let filename = normalize_path filename in
  begin match package_root with
  | None -> ()
  | Some root ->
    if not (path_within root filename)
    then failwith ("source file escapes package root: " ^ filename)
  end;
  if List.mem filename stack then failwith (cycle_message filename stack)
  else
    let items = parse_file_raw filename in
    expand_file_modules ?package_root (filename :: stack) filename items

and expand_file_modules ?package_root stack declaring_file items =
  reject_duplicate_module_decls items;
  List.map
    (function
      | Ast.NIMod (visibility, name, children) ->
        Ast.NIMod (visibility, name, expand_file_modules ?package_root stack declaring_file children)
      | Ast.NIModFile (visibility, name) ->
        let module_file = module_file_path ?package_root declaring_file name in
        let children = load_source_file ?package_root stack module_file in
        Ast.NIMod (visibility, name, children)
      | item -> item)
    items

let parse_file ?package_root filename =
  let filename =
    match package_root with
    | Some root when Filename.is_relative filename -> Filename.concat root filename
    | _ -> filename
  in
  let filename = normalize_path filename in
  let package_root =
    match package_root with
    | Some root -> Some (normalize_path root)
    | None -> Some (Filename.dirname filename)
  in
  load_source_file ?package_root [] filename

let core_dir override =
  match override with
  | Some dir -> dir
  | None ->
    match Sys.getenv_opt "FACET_CORE_DIR" with
    | Some dir -> dir
    | None -> "core"

let load_core_items core_dir_override =
  let dir = core_dir core_dir_override in
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun name -> Filename.check_suffix name ".facet")
    |> List.sort String.compare
    |> List.concat_map (fun name -> parse_file (Filename.concat dir name))
  else []

let () =
  let args = Sys.argv in
  if Array.length args >= 2 && args.(1) = "--generate-grammar" then begin
    Grammar.print_grammar ();
    exit 0
  end;
  (* Parse optional flags before the source file argument *)
  let emit_fir_file = ref None in
  let core_dir_override = ref None in
  let package_root = ref None in
  let diagnose_trait_gates = ref false in
  let i = ref 1 in
  while !i < Array.length args && String.length args.(!i) > 0
        && args.(!i).[0] = '-' do
    if args.(!i) = "--emit-fir" then begin
      if !i + 1 >= Array.length args then begin
        Printf.eprintf "Error: --emit-fir requires a filename argument\n";
        exit 1
      end;
      emit_fir_file := Some args.(!i + 1);
      i := !i + 2
    end else if args.(!i) = "--core-dir" then begin
      if !i + 1 >= Array.length args then begin
        Printf.eprintf "Error: --core-dir requires a directory argument\n";
        exit 1
      end;
      core_dir_override := Some args.(!i + 1);
      i := !i + 2
    end else if args.(!i) = "--package-root" then begin
      if !i + 1 >= Array.length args then begin
        Printf.eprintf "Error: --package-root requires a directory argument\n";
        exit 1
      end;
      package_root := Some (normalize_path args.(!i + 1));
      i := !i + 2
    end else if args.(!i) = "--diagnose-trait-gates" then begin
      diagnose_trait_gates := true;
      i := !i + 1
    end else begin
      Printf.eprintf "Error: unknown option: %s\n" args.(!i);
      exit 1
    end
  done;
  if !i >= Array.length args then begin
    Printf.eprintf "Usage: %s [--emit-fir <outfile>] [--core-dir DIR] [--package-root DIR] [--diagnose-trait-gates] [--generate-grammar] FILE\n" args.(0);
    exit 1
  end;
  let filename = args.(!i) in
  let env =
    try
      let core_items = load_core_items !core_dir_override in
      let named_items = parse_file ?package_root:!package_root filename in
      Debruijn.convert_program_items_with_core core_items named_items
    with Failure msg ->
      Printf.eprintf "Validation error: %s\n" msg;
      exit 1
  in
  let env_for_checker = alpha_normalize_global_env env in
  let diagnostics = diagnostic_map_of_envs env env_for_checker in
  let checked_env =
    match infer_program_env_end2end_assoc_direct_receiver_mixed env_for_checker with
    | Infer_ok env' ->
      List.iter (fun f ->
        let (fname, _) = f.fn_name in
        Printf.printf "OK: %s\n" fname
      ) env'.env_fns;
      env'
    | Infer_err e ->
      Printf.eprintf "Type error: %s\n" (string_of_infer_error ~diagnostics e);
      exit 1
  in
  if !diagnose_trait_gates then begin
    let print_gate name ok =
      Printf.printf "%s: %s\n" name (if ok then "ok" else "fail")
    in
    let component_body_summary_failures =
      List.filter
        (fun f ->
          not
            (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
               checked_env f))
        checked_env.env_fns
    in
    let component_ready_body_summary_failures =
      List.filter
        (fun f ->
          not
            (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
               checked_env f))
        checked_env.env_fns
    in
    let component_store_safe_summary_functions =
      List.filter
        (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
           checked_env)
        checked_env.env_fns
    in
    print_gate "trait-direct-receiver-method-present"
      (check_env_root_shadow_direct_receiver_method_present checked_env);
    print_gate "trait-component-body-summary"
      (check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
         checked_env);
    print_gate "trait-component-ready-body-summary"
      (check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_summary
         checked_env);
    Printf.printf "trait-component-store-safe-summary-functions: %d\n"
      (List.length component_store_safe_summary_functions);
    Printf.printf "trait-component-body-summary-failures: %d\n"
      (List.length component_body_summary_failures);
    Printf.printf "trait-component-ready-body-summary-failures: %d\n"
      (List.length component_ready_body_summary_failures);
    List.iter
      (fun f ->
        let (fname, _) = f.fn_name in
        Printf.printf "trait-component-ready-body-summary-failure: %s\n" fname)
      component_ready_body_summary_failures;
    List.iter
      (fun f ->
        let (fname, _) = f.fn_name in
        Printf.printf "trait-component-body-summary-failure: %s\n" fname;
        let reason =
          if check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
               checked_env f
          then "local-bounds-synthetic-direct-call-ready-summary"
          else "component-store-safe-summary"
        in
        Printf.printf "trait-component-body-summary-failure-reason: %s: %s\n"
          fname reason;
        if reason = "local-bounds-synthetic-direct-call-ready-summary" then begin
          let local_env = global_env_with_local_bounds checked_env f.fn_bounds in
          let local_summary_failures =
            List.filter
              (fun local_fn ->
                not
                  (check_fn_root_shadow_synthetic_direct_call_ready_summary
                     local_env local_fn))
              local_env.env_fns
          in
          Printf.printf
            "trait-local-bounds-synthetic-summary-failures: %s: %d\n"
            fname (List.length local_summary_failures);
          List.iter
            (fun local_fn ->
              let (local_fname, _) = local_fn.fn_name in
              let reason =
                match direct_call_target_expr local_fn.fn_body with
                | None -> "no-direct-call-target"
                | Some _ -> "direct-call-ready-summary-check"
              in
              Printf.printf
                "trait-local-bounds-synthetic-summary-failure: %s: %s\n"
                fname local_fname;
              Printf.printf
                "trait-local-bounds-synthetic-summary-failure-reason: %s: %s: %s\n"
                fname local_fname reason)
            local_summary_failures
        end)
      component_body_summary_failures;
    print_gate "trait-no-receiver-body-summary"
      (check_env_root_shadow_no_receiver_component_body_summary_provider_check checked_env);
    print_gate "trait-no-receiver-ready-body-summary"
      (check_env_root_shadow_no_receiver_component_ready_body_summary_provider_check checked_env)
  end;
  Option.iter (fun fname ->
    try Fir.emit_fir fname checked_env
    with Failure msg ->
      Printf.eprintf "FIR error: %s\n" msg;
      exit 1
  ) !emit_fir_file
