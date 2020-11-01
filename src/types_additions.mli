
open Cduce

(* Construction of types *)

type type_base =
    TInt of int option * int option
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

module StrMap : Map.S with type key = string
type type_env = node StrMap.t

val empty_tenv : type_env

val type_base_to_typ : type_base -> typ

val type_expr_to_typ : type_env -> type_expr -> typ

val define_atom : type_env -> string -> type_env

val define_types : type_env -> (string * type_expr) list -> type_env

val get_atom : type_env -> string -> typ

(* Operations on types *)

val conj : typ list -> typ
val disj : typ list -> typ

val square : typ -> typ -> typ (* Does not work with polymorphism yet *)
val square_approx : typ -> typ -> typ
val square_exact : typ -> typ -> typ
