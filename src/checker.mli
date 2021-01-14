open Nf_ast
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof : type_env -> Env.t -> Annotations.t -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> Annotations.t -> a -> typ
(*val refine : backward:bool -> Env.t -> e -> typ -> Env.t list*)
val refine_a : backward:bool -> Env.t -> a -> typ -> Env.t list
val infer : type_env -> Env.t -> Annotations.t -> e -> e * Annotations.t

val typeof_simple : type_env -> Env.t -> e -> typ
