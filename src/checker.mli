open Nf_ast
open Types_additions
open Cduce
open Variable

type env
val empty_env : env
val is_bottom : env -> bool
val add_to_env : Variable.t -> typ -> env -> env

exception Ill_typed of Position.t * string

val typeof : type_env -> env -> e -> typ
