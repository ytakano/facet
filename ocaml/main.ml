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

type checked_program = {
  env_for_checker : global_env;
  diagnostic_map  : diagnostic_map;
  result          : (ty * ctx, infer_error) result;
}

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
  | EFn original_id, EFn alpha_id
  | ECall (original_id, _), ECall (alpha_id, _) ->
    let map = diagnostic_add alpha_id original_id map in
    diagnostic_add_exprs map
      (match original with ECall (_, args) -> args | _ -> [])
      (match alpha with ECall (_, args) -> args | _ -> [])
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
  | EStruct (_, _, _, original_fields), EStruct (_, _, _, alpha_fields) ->
    diagnostic_add_fields map original_fields alpha_fields
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

let diagnostic_lookup map id =
  match List.find_opt (fun (id', _) -> ident_eqb id id') map with
  | Some (_, entry) -> Some entry.original_name
  | None -> None

let string_of_diagnostic_ident diagnostics id =
  match diagnostic_lookup diagnostics id with
  | Some name -> name
  | None -> string_of_ident id

let result_of_infer_result = function
  | Infer_ok value -> Ok value
  | Infer_err err -> Error err

let check_alpha_normalized_fn env_for_checker diagnostics f =
  { env_for_checker;
    diagnostic_map = diagnostics;
    result = result_of_infer_result (infer_full_env env_for_checker f) }

let string_of_infer_error ?(diagnostics = []) = function
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

let () =
  let args = Sys.argv in
  if Array.length args >= 2 && args.(1) = "--generate-grammar" then begin
    Grammar.print_grammar ();
    exit 0
  end;
  (* Parse optional flags before the source file argument *)
  let emit_fir_file = ref None in
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
    end else begin
      Printf.eprintf "Error: unknown option: %s\n" args.(!i);
      exit 1
    end
  done;
  if !i >= Array.length args then begin
    Printf.eprintf "Usage: %s [--emit-fir <outfile>] [--generate-grammar] FILE\n" args.(0);
    exit 1
  end;
  let filename = args.(!i) in
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
  let named_items =
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
  in
  let env =
    try Debruijn.convert_program_items named_items
    with Failure msg ->
      Printf.eprintf "Validation error: %s\n" msg;
      exit 1
  in
  let env_for_checker = alpha_normalize_global_env env in
  let diagnostics = diagnostic_map_of_envs env env_for_checker in
  let fn_defs = env_for_checker.env_fns in
  let ok = ref true in
  List.iter (fun f ->
    let (fname, _) = f.fn_name in
    let checked = check_alpha_normalized_fn env_for_checker diagnostics f in
    match checked.result with
    | Error e ->
      Printf.eprintf "Type error in function '%s': %s\n"
        fname (string_of_infer_error ~diagnostics:checked.diagnostic_map e);
      ok := false
    | Ok _ ->
      Printf.printf "OK: %s\n" fname
  ) fn_defs;
  if not !ok then exit 1;
  Option.iter (fun fname -> Fir.emit_fir fname env_for_checker) !emit_fir_file
