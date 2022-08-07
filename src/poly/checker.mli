open Msc
open Types.Base
open Types.Additions
open Annotations
open Common

exception Ill_typed of Position.t list * string

val typeof : type_env -> Env.t -> Annot.t -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> Annot.a -> a -> typ
