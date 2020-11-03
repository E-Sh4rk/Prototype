open Nf_ast
open Types_additions
open Cduce
open Variable

type env
val empty_env : env
val is_bottom : env -> bool
val add_to_env : Variable.t -> typ -> env -> env

exception Ill_typed of Position.t list * string

val typeof : type_env -> env -> e -> typ
val candidates : type_env -> env -> e -> Variable.t -> typ list
val refine : forward:bool -> type_env -> env -> e -> typ -> type_env list
