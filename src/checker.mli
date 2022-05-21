open Msc
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof :  type_env -> Env.t -> Annot.e -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> Annot.a -> a -> typ

val refine_a : sufficient:bool -> type_env ->
    Env_refinement.t -> a -> typ -> typ -> Env_refinement.t list

val infer : type_env -> Env.t -> e -> e * Annot.e
val typeof_simple : type_env -> Env.t -> e -> typ
