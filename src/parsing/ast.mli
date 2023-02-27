open Types.Base
open Types.Additions
open Variable
open Pomap

exception SymbolError of string
exception LexicalError of Position.t * string
exception SyntaxError of Position.t * string

type varname = string
type exprid = int

type annotation = exprid Position.located

type const =
| Unit | Nil
| EmptyRecord
| Bool of bool
| Int of int
| Float of float
| Char of char
| String of string
| Atom of string

type projection = Fst | Snd | Field of string

type 'typ type_annot = Unnanoted | ADomain of 'typ list

type ('a, 'typ, 'v) pattern =
| PatType of 'typ
| PatVar of 'v
| PatAnd of ('a, 'typ, 'v) pattern * ('a, 'typ, 'v) pattern
| PatOr of ('a, 'typ, 'v) pattern * ('a, 'typ, 'v) pattern
| PatPair of ('a, 'typ, 'v) pattern * ('a, 'typ, 'v) pattern
| PatRecord of (string * (('a, 'typ, 'v) pattern)) list * bool
| PatAssign of 'v * const

and ('a, 'typ, 'v) ast =
| Abstract of 'typ
| Const of const
| Var of 'v
| Lambda of ('typ type_annot) * 'v * ('a, 'typ, 'v) t
| Fixpoint of ('a, 'typ, 'v) t
| Ite of ('a, 'typ, 'v) t * 'typ * ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| App of ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Let of 'v * ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Pair of ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Projection of projection * ('a, 'typ, 'v) t
| RecordUpdate of ('a, 'typ, 'v) t * string * ('a, 'typ, 'v) t option
| TypeConstr of ('a, 'typ, 'v) t * 'typ
| PatMatch of ('a, 'typ, 'v) t * (('a, 'typ, 'v) pattern * ('a, 'typ, 'v) t) list

and ('a, 'typ, 'v) t = 'a * ('a, 'typ, 'v) ast

type annot_expr = (annotation, typ, Variable.t) t
type expr = (unit, typ, Variable.t) t
type parser_expr = (annotation, type_expr, varname) t

module Expr : Pomap_intf.PARTIAL_ORDER with type el = expr
module ExprMap : Pomap_intf.POMAP with type key = expr

type name_var_map = Variable.t StrMap.t
val empty_name_var_map : name_var_map

val unique_exprid : unit -> exprid
val identifier_of_expr : (annotation, 'a, 'b) t -> exprid
val position_of_expr : (annotation, 'a, 'b) t -> Position.t

val new_annot : Position.t -> annotation
val copy_annot : annotation -> annotation

val dummy_pat_var : Variable.t

val parser_expr_to_annot_expr : type_env -> var_type_env -> name_var_map -> parser_expr -> annot_expr

(*val unannot : annot_expr -> expr*)
val unannot_and_normalize : annot_expr -> expr
(*val fv : annot_expr -> VarSet.t*)
val map_ast : (annot_expr -> annot_expr) -> annot_expr -> annot_expr 
val substitute : annot_expr -> Variable.t -> annot_expr -> annot_expr

val const_to_typ : const -> typ

type parser_element =
| Definition of (int (* log level *) * (string * parser_expr * type_expr option))
| Atoms of string list
| Types of (string * string list * type_expr) list

type parser_program = (annotation * parser_element) list

(* Pretty printers *)

val pp_const : Format.formatter -> const -> unit
val pp_projection : Format.formatter -> projection -> unit
val pp_type_annot : (Format.formatter -> 'a -> unit) ->
                    Format.formatter -> 'a type_annot -> unit
val show_const : const -> string
val show_projection : projection -> string
val show_type_annot : (Format.formatter -> 'a -> unit) ->
                    'a type_annot -> string
