open Nf_ast
open Types_additions
open Cduce

exception Ill_typed of Position.t list * string

type typ_tree =
  | TNode of Env.t * (Env.t list * typ_tree) list
  | TLeaf of Env.t * typ

val leaves : typ_tree -> (Env.t * typ) list

type context = e

val empty_context : context
val fill_context : context -> context -> context

val bound_vars : e -> Variable.VarSet.t

val typeof : type_env -> Env.t -> Env.t -> context -> e -> typ_tree
val typeof_a : Position.t list -> type_env -> Env.t -> Env.t -> context -> a -> typ_tree
val refine : backward:bool -> type_env -> Env.t -> e -> typ -> Env.t list
val refine_a : Position.t list -> backward:bool -> type_env -> Env.t -> a -> typ -> Env.t list

val typeof_simple : type_env -> Env.t -> e -> typ
