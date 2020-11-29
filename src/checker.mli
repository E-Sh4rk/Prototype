open Nf_ast
open Types_additions
open Cduce

exception Ill_typed of Position.t list * string

val typeof : type_env -> Env.t -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> a -> typ
val refine : backward:bool -> type_env -> Env.t -> e -> typ -> (typ * Env.t) list
val refine_a : Position.t list -> backward:bool -> type_env -> Env.t -> a -> typ -> (typ * Env.t) list
