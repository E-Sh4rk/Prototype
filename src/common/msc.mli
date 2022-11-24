open Parsing
open Types.Base
open Parsing.Variable

(* TODO: Implement new MSC *)

type 'va a =
  | Abstract of typ
  | Const of Ast.const
  | Lambda of 'va * (typ Ast.type_annot) * Variable.t * 'va e
  | Ite of Variable.t * typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t

and 'va e =
  | Bind of 'va * Variable.t * 'va a * 'va e
  | Var of Variable.t

val convert_to_msc : Ast.annot_expr -> unit e
val map_e : ('a e -> 'a e) -> ('a a -> 'a a) -> 'a e -> 'a e
val map_a : ('a e -> 'a e) -> ('a a -> 'a a) -> 'a a -> 'a a
val map_annot_e : ('a -> 'b) -> ('a -> 'b) -> 'a e -> 'b e
val map_annot_a : ('a -> 'b) -> ('a -> 'b) -> 'a a -> 'b a
val fold_e : ('a e -> 'b list -> 'b) -> ('a a -> 'b list -> 'b) -> 'a e -> 'b
val fold_a : ('a e -> 'b list -> 'b) -> ('a a -> 'b list -> 'b) -> 'a a -> 'b

val bv_a : 'a a -> VarSet.t
val bv_e : 'a e -> VarSet.t
val fv_a : 'a a -> VarSet.t
val fv_e : 'a e -> VarSet.t

val pp_a : (Format.formatter -> 'va -> unit) -> Format.formatter -> 'va a -> unit
val pp_e : (Format.formatter -> 'va -> unit) -> Format.formatter -> 'va e -> unit
val show_a : (Format.formatter -> 'va -> unit) -> 'va a -> string
val show_e : (Format.formatter -> 'va -> unit) -> 'va e -> string
