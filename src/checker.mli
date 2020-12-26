open Nf_ast
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof : type_env -> Env.t -> annotations -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> annotations -> a -> typ
val refine : backward:bool -> type_env -> Env.t -> e -> typ -> Env.t list
val refine_a : Position.t list -> backward:bool -> type_env -> Env.t -> a -> typ -> Env.t list
val infer : type_env -> Env.t -> annotations -> e -> annotations
val infer_a : Position.t list -> type_env -> Env.t -> annotations -> a -> annotations

val typeof_simple : type_env -> Env.t -> e -> typ
