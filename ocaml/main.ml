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
  | TFn (ts, r) ->
    Printf.sprintf "fn(%s) -> %s"
      (String.concat ", " (List.map string_of_ty ts))
      (string_of_ty r)
  | TRef (RShared, t) -> "&" ^ string_of_ty t
  | TRef (RUnique, t) -> "&mut " ^ string_of_ty t

and string_of_ty (MkTy (u, c)) =
  string_of_usage u ^ " " ^ string_of_ty_core c

let string_of_ident (name, idx) =
  Printf.sprintf "%s#%s" name (Big_int_Z.string_of_big_int idx)

let string_of_infer_error = function
  | ErrUnknownVar id      ->
    Printf.sprintf "unknown variable: %s" (string_of_ident id)
  | ErrAlreadyConsumed id ->
    Printf.sprintf "variable already consumed: %s" (string_of_ident id)
  | ErrTypeMismatch (c1, c2) ->
    Printf.sprintf "type mismatch: expected %s, got %s"
      (string_of_ty_core c1) (string_of_ty_core c2)
  | ErrUsageMismatch (u1, u2) ->
    Printf.sprintf "usage mismatch: expected %s, got %s"
      (string_of_usage u1) (string_of_usage u2)
  | ErrFunctionNotFound id ->
    Printf.sprintf "function not found: %s" (string_of_ident id)
  | ErrArityMismatch      -> "arity mismatch"
  | ErrContextCheckFailed -> "context check failed (linear variable not consumed)"
  | ErrNotImplemented     -> "not implemented (type inference for let without annotation)"

let check_alpha_consistency fname fenv f =
  let r1 = infer fenv f in
  let r2 = infer_direct fenv f in
  match r1, r2 with
  | Infer_ok _, Infer_ok _ -> ()
  | Infer_err _, Infer_err _ -> ()
  | Infer_ok _, Infer_err e ->
    Printf.eprintf "ALPHA-DIFF in '%s': infer=OK, infer_direct=Err(%s)\n"
      fname (string_of_infer_error e)
  | Infer_err e, Infer_ok _ ->
    Printf.eprintf "ALPHA-DIFF in '%s': infer=Err(%s), infer_direct=OK\n"
      fname (string_of_infer_error e)

let () =
  let args = Sys.argv in
  if Array.length args >= 2 && args.(1) = "--generate-grammar" then begin
    Grammar.print_grammar ();
    exit 0
  end;
  (* Parse optional flags before the source file argument *)
  let emit_fir_file = ref None in
  let debug_alpha = ref false in
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
    end else if args.(!i) = "--debug-alpha" then begin
      debug_alpha := true;
      i := !i + 1
    end else begin
      Printf.eprintf "Error: unknown option: %s\n" args.(!i);
      exit 1
    end
  done;
  if !i >= Array.length args then begin
    Printf.eprintf "Usage: %s [--emit-fir <outfile>] [--debug-alpha] [--generate-grammar] FILE\n" args.(0);
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
  let named_defs =
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
  let fn_defs = List.map Debruijn.convert_fn_def named_defs in
  let ok = ref true in
  List.iter (fun f ->
    let (fname, _) = f.fn_name in
    if !debug_alpha then
      check_alpha_consistency fname fn_defs f;
    match infer fn_defs f with
    | Infer_err e ->
      Printf.eprintf "Type error in function '%s': %s\n"
        fname (string_of_infer_error e);
      ok := false
    | Infer_ok _ ->
      Printf.printf "OK: %s\n" fname
  ) fn_defs;
  if not !ok then exit 1;
  Option.iter (fun fname -> Fir.emit_fir fname fn_defs) !emit_fir_file
