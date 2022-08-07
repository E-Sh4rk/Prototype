open Msc
open Types.Base
open Types.Additions
open Annotations
open Common

exception Ill_typed of Position.t list * string

val typeof :  type_env -> Env.t -> AnnotMono.e -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> AnnotMono.a -> a -> typ

val refine_a : sufficient:bool -> type_env ->
    Ref_env.t -> a -> typ -> typ -> Ref_env.t list

val infer : type_env -> Env.t -> e -> e * AnnotMono.e
val typeof_simple : type_env -> Env.t -> e -> typ