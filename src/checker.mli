open Nf_ast
open Types_additions
open Cduce
open Variable

module Env : sig
  type t
  val empty : t
  val bottom : t
  val is_bottom : t -> bool
  val add : Variable.t -> typ -> t -> t
  val find : Variable.t -> t -> typ
  val rm : Variable.t -> t -> t
  val conj : t list -> t
end

exception Ill_typed of Position.t list * string

(* TODO: change normal form: e should be let | x *)
val typeof : type_env -> Env.t -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> a -> typ
val candidates : type_env -> Env.t -> e -> Variable.t -> typ list
val candidates_a : Position.t list -> type_env -> Env.t -> a -> Variable.t -> typ list
val refine : backward:bool -> type_env -> Env.t -> e -> typ -> (typ * Env.t) list
val refine_a : Position.t list -> backward:bool -> type_env -> Env.t -> a -> typ -> (typ * Env.t) list
