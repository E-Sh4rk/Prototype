open Nf_ast
open Types_additions
open Cduce
open Variable

module Env : sig
  type t
  val empty : t
  val is_bottom : t -> bool
  val add : Variable.t -> typ -> t -> t
  val find : Variable.t -> t -> typ
end

exception Ill_typed of Position.t list * string

val typeof : type_env -> Env.t -> e -> typ
val candidates : type_env -> Env.t -> e -> Variable.t -> typ list
val refine : backward:bool -> type_env -> Env.t -> e -> typ -> (typ * Env.t) list
