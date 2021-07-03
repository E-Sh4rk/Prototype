open Nf_ast
open Types_additions
open Cduce

exception Ill_typed of Position.t list * string

val typeof : type_env -> Env.t -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> a -> typ
val refine_a : Env.t -> a -> typ -> Env.t list
val infer : type_env -> Env.t -> e -> e

val typeof_simple : type_env -> Env.t -> e -> typ
