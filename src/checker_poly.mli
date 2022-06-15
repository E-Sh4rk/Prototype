open Msc
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof :  type_env -> Env.t -> varset -> AnnotPoly.e -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> varset -> AnnotPoly.a -> a -> typ
