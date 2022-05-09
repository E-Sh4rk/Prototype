open Variable
open Msc
open Types_additions
open Cduce
open Annotations

exception Ill_typed of Position.t list * string

val typeof :  type_env -> Env.t -> annot -> e -> typ
val typeof_a : Position.t list -> type_env -> Env.t -> annot_a -> a -> typ

val refine_a : sufficient:bool -> type_env ->
    Env_refinement.t -> a -> typ -> Env_refinement.t list

val regroup : Variable.t -> (Env_refinement.t * 'a) list ->
    (Env_refinement.t * (Cduce.typ * 'a) list) list
