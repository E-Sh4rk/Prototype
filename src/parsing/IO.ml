open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_expr_file source_filename =
  let cin = open_in source_filename in
  let buf = Lexing.from_channel cin in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = source_filename };
  Parser.unique_term Lexer.token buf

let parse_expr_string str =
  let buf = Lexing.from_string str in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = "_" };
  Parser.unique_term Lexer.token buf

let parse_program_file source_filename =
  let cin = open_in source_filename in
  let buf = Lexing.from_channel cin in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = source_filename };
  try Parser.program Lexer.token buf with
  | Lexer.LexerError msg ->
    raise (Ast.LexicalError (Format.asprintf "%a" print_position buf, msg))
  | Parser.Error ->
    raise (Ast.SyntaxError (Format.asprintf "%a" print_position buf, "Syntax error"))

let parse_program_string str =
  let buf = Lexing.from_string str in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = "_" };
  try Parser.program Lexer.token buf with
  | Lexer.LexerError msg ->
    raise (Ast.LexicalError (Format.asprintf "%a" print_position buf, msg))
  | Parser.Error ->
    raise (Ast.SyntaxError (Format.asprintf "%a" print_position buf, "Syntax error"))
