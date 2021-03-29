
open Cduce

module StrMap : Map.S with type key = String.t

(* Construction of types *)

type type_base =
    | TInt of int option * int option | TSChar of char
    | TBool | TTrue | TFalse | TUnit | TChar | TAny | TEmpty

type type_expr =
| TBase of type_base
| TCustom of string
| TPair of type_expr * type_expr
| TRecord of bool * (string * type_expr * bool) list
| TArrow of type_expr * type_expr
| TCup of type_expr * type_expr
| TCap of type_expr * type_expr
| TDiff of type_expr * type_expr
| TNeg of type_expr

type type_env

val empty_tenv : type_env

val type_base_to_typ : type_base -> typ

val type_expr_to_typ : type_env -> type_expr -> typ

val define_atom : type_env -> string -> type_env

val define_types : type_env -> (string * type_expr) list -> type_env

val get_type_or_atom : type_env -> string -> typ

val has_type_or_atom : type_env -> string -> bool

(* Operations on types *)

val conj : typ list -> typ
val disj : typ list -> typ

val simplify_dnf : (typ * typ) list list -> (typ * typ) list list
val simplify_typ : typ -> typ

val split_arrow : typ -> typ list

val is_test_type : typ -> bool

val square_split : typ -> typ -> (typ * typ) list
val square_approx : typ -> typ -> typ
val square_exact : typ -> typ -> typ

val triangle_split : typ -> typ -> (typ * typ) list
val triangle_exact : typ -> typ -> typ

(* Record manipulation *)

val record_any_with : string -> typ
(** [record_any_with l] creates the record type {l = Any ..} *)

val split_record : typ -> typ list
(** [split_record t] splits a union of record types 
    into a list of individual record types *)

val remove_field_info : typ -> string -> typ
(** [remove_field_info t label] removes all the information
    about the field label in the record t. *)
