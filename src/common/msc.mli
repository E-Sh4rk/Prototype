open Parsing
open Types.Base
open Parsing.Variable

type a =
  | Alias of Variable.t
  | Abstract of typ
  | Const of Ast.const
  | Lambda of (typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t
  | TypeConstr of Variable.t * typ

and e =
  | Bind of Variable.t * a * e
  | Var of Variable.t

val initial_env : Env.t

val convert_to_msc : Ast.annot_expr -> e
val map_e : (e -> e) -> (a -> a) -> e -> e
val map_a : (e -> e) -> (a -> a) -> a -> a
val fold_e : (e -> 'b list -> 'b) -> (a -> 'b list -> 'b) -> e -> 'b
val fold_a : (e -> 'b list -> 'b) -> (a -> 'b list -> 'b) -> a -> 'b

val bv_a : a -> VarSet.t
val bv_e : e -> VarSet.t
val fv_a : a -> VarSet.t
val fv_e : e -> VarSet.t

val pp_a : Format.formatter -> a -> unit
val pp_e : Format.formatter -> e -> unit
val show_a : a -> string
val show_e : e -> string
