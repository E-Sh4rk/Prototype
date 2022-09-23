
open Ast

val parse_expr_file : string -> parser_expr
val parse_expr_string : string -> parser_expr

val parse_program_file : string -> parser_program
val parse_program_string : string -> parser_program
