open Msc
open Types.Base
open Types.Tvar
open Types.Additions
open Annotations
open Common

exception Untypeable of Position.t list * string

val typeof : type_env -> Env.t -> TVarSet.t -> Annot.t -> e -> typ

val infer : type_env -> Env.t -> TVarSet.t -> e -> e * Annot.t

val typeof_simple : type_env -> Env.t -> TVarSet.t -> e -> typ
