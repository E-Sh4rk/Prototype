
open Ast

val parse_expr_file : string -> parser_expr
val parse_expr_string : string -> parser_expr

val parse_defs_file : string -> (string * parser_expr) list
val parse_defs_string : string -> (string * parser_expr) list

val parse_program_file : string -> parser_program
val parse_program_string : string -> parser_program
