type position = {
  pos_fname : string;
  pos_lnum  : int;
  pos_bol   : int;
  pos_cnum  : int;
}

type lexer_state = {
  buf  : Sedlexing.lexbuf;
  mutable lnum : int;
  mutable bol  : int;
  fname : string;
}

let make_state fname buf = { buf; lnum = 1; bol = 0; fname }

let current_pos st =
  let (start, _) = Sedlexing.lexing_positions st.buf in
  { pos_fname = st.fname;
    pos_lnum  = st.lnum;
    pos_bol   = st.bol;
    pos_cnum  = start.Lexing.pos_cnum;
  }

let keywords = [
  "fn",           Parser.KW_FN;
  "let",          Parser.KW_LET;
  "in",           Parser.KW_IN;
  "mut",          Parser.KW_MUT;
  "drop",         Parser.KW_DROP;
  "replace",      Parser.KW_REPLACE;
  "affine",       Parser.KW_AFFINE;
  "linear",       Parser.KW_LINEAR;
  "unrestricted", Parser.KW_UNRESTRICTED;
  "isize",        Parser.KW_ISIZE;
  "f64",          Parser.KW_F64;
  "if",           Parser.KW_IF;
  "else",         Parser.KW_ELSE;
  "true",         Parser.KW_TRUE;
  "false",        Parser.KW_FALSE;
  "bool",         Parser.KW_BOOL;
]

let id_or_kw s =
  match List.assoc_opt s keywords with
  | Some kw -> kw
  | None    -> Parser.ID s

exception LexError of position * string

let digit  = [%sedlex.regexp? '0'..'9']
let alpha  = [%sedlex.regexp? 'a'..'z' | 'A'..'Z']
let alnum  = [%sedlex.regexp? alpha | digit | '_']
let ident  = [%sedlex.regexp? alpha, Star alnum | '_', Plus alnum]

let rec tokenize st =
  let buf = st.buf in
  match%sedlex buf with
  | '/', '/', Star (Compl '\n') -> tokenize st
  | '\n' ->
    st.lnum <- st.lnum + 1;
    st.bol  <- Sedlexing.lexeme_end buf;
    tokenize st
  | Plus (Chars " \t\r") -> tokenize st
  | '-', '>' -> Parser.ARROW
  | '-', Plus digit, '.', Plus digit ->
    Parser.FLOAT_LIT (Sedlexing.Utf8.lexeme buf)
  | '-', Plus digit ->
    Parser.INT_LIT (Big_int_Z.big_int_of_string (Sedlexing.Utf8.lexeme buf))
  | Plus digit, '.', Plus digit ->
    Parser.FLOAT_LIT (Sedlexing.Utf8.lexeme buf)
  | Plus digit ->
    Parser.INT_LIT (Big_int_Z.big_int_of_string (Sedlexing.Utf8.lexeme buf))
  | ident ->
    id_or_kw (Sedlexing.Utf8.lexeme buf)
  | '_' -> Parser.UNDERSCORE
  | '(' -> Parser.LPAREN
  | ')' -> Parser.RPAREN
  | '{' -> Parser.LBRACE
  | '}' -> Parser.RBRACE
  | '&' -> Parser.AMP
  | ',' -> Parser.COMMA
  | ':' -> Parser.COLON
  | '=' -> Parser.EQUAL
  | ';' -> Parser.SEMI
  | eof -> Parser.EOF
  | _ ->
    let pos = current_pos st in
    raise (LexError (pos, Printf.sprintf "unexpected character: %s"
      (Sedlexing.Utf8.lexeme buf)))

let provider st () =
  let tok = tokenize st in
  let (start, stop) = Sedlexing.lexing_positions st.buf in
  (tok, start, stop)
