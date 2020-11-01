
let parse_expr_file source_filename = Lexing.(
  let cin = open_in source_filename in
  let buf = Lexing.from_channel cin in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = source_filename };
  Parser.unique_term Lexer.token buf
)

let parse_expr_string str =
  let buf = Lexing.from_string str in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = "_" };
  Parser.unique_term Lexer.token buf

let parse_defs_file source_filename = Lexing.(
  let cin = open_in source_filename in
  let buf = Lexing.from_channel cin in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = source_filename };
  Parser.definitions Lexer.token buf
)

let parse_defs_string str =
  let buf = Lexing.from_string str in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = "_" };
  Parser.definitions Lexer.token buf

let parse_program_file source_filename = Lexing.(
  let cin = open_in source_filename in
  let buf = Lexing.from_channel cin in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = source_filename };
  Parser.program Lexer.token buf
)

let parse_program_string str =
  let buf = Lexing.from_string str in
  buf.lex_curr_p <- { buf.lex_curr_p with  pos_fname = "_" };
  Parser.program Lexer.token buf
