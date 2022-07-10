open Msc
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof :  type_env -> Env.t -> varset -> AnnotPoly.e -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> varset -> AnnotPoly.a -> a -> typ

val refine_a : type_env ->
    Ref_env.t -> varset -> a -> typ -> typ -> Ref_env.t list

val infer : type_env -> Env.t -> varset -> e -> e * AnnotMono.e
val typeof_simple : type_env -> Env.t -> varset -> e -> typ
