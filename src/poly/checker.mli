open Msc
open Types.Base
open Types.Additions
open Annotations
open Common

exception Untypeable of Position.t list * string

val typeof : type_env -> Env.t -> TVarSet.t -> Annot.t -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> TVarSet.t -> Annot.a -> a -> typ
