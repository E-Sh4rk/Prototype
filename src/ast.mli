
open Types_additions
type typ = Cduce.typ

type varname = string
type varid = int (* It is NOT De Bruijn indexes, but unique IDs *)
type exprid = int

type annotation = exprid Position.located

type const =
| Magic
| Unit
| EmptyRecord
| Bool of bool
| Int of int
| Char of char
| Atom of string

type projection = Fst | Snd | Field of string

type 'typ type_annot = Unnanoted | ADomain of 'typ | AArrow of 'typ

type ('a, 'typ, 'v) ast =
| Const of const
| Var of 'v
| Lambda of ('typ type_annot) * 'v * ('a, 'typ, 'v) t
| Ite of ('a, 'typ, 'v) t * 'typ * ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| App of ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Let of 'v * ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Pair of ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Projection of projection * ('a, 'typ, 'v) t
| RecordUpdate of ('a, 'typ, 'v) t * string * ('a, 'typ, 'v) t option
| Debug of string * ('a, 'typ, 'v) t

and ('a, 'typ, 'v) t = 'a * ('a, 'typ, 'v) ast

type annot_expr = (annotation, typ, varid) t
type expr = (unit, typ, varid) t
type parser_expr = (annotation, type_expr, varname) t

module Expr : sig
    type t = expr
    val compare : t -> t -> int
    val equiv : t -> t -> bool
end
module ExprMap : Map.S with type key = expr
module VarIdMap : Map.S with type key = varid
module VarIdSet : Set.S with type elt = varid

type id_map = int StrMap.t
val empty_id_map : id_map

val unique_exprid : unit -> exprid
val unique_varid : unit -> varid

val identifier_of_expr : (annotation, 'a, 'b) t -> exprid
val position_of_expr : (annotation, 'a, 'b) t -> Position.t

val new_annot : Position.t -> annotation
val copy_annot : annotation -> annotation

val parser_expr_to_annot_expr : type_env -> id_map -> parser_expr -> annot_expr

val unannot : annot_expr -> expr
val fv : annot_expr -> VarIdSet.t

val const_to_typ : const -> typ

type parser_element =
| Definition of (string * parser_expr)
| Atoms of string list
| Types of (string * type_expr) list

type parser_program = parser_element list
