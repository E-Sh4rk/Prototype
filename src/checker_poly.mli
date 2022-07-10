open Msc
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof :  type_env -> Env.t -> varset -> AnnotPoly.e -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> varset -> AnnotPoly.a -> a -> typ

val propagate_a : Ref_env.t -> varset -> a -> typ -> typ
    -> Ref_env.t list (* Necessary *) * Ref_env.t list (* Sufficient *)

val infer : type_env -> Env.t -> varset -> e -> e * AnnotMono.e
val typeof_simple : type_env -> Env.t -> varset -> e -> typ
