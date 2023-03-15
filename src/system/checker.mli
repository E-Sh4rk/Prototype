open Types.Base
open Types.Additions
open Annotations
open Common

exception Untypeable of Position.t list * string

val typeof : type_env -> Env.t -> FullAnnot.t -> Msc.e -> typ

val infer : type_env -> Env.t -> Msc.e -> FullAnnot.t

val typeof_simple : type_env -> Env.t -> Msc.e -> typ
