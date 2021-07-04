open Variable
open Annotations

type a =
  | Abstract of Cduce.typ
  | Const of Ast.const
  | Lambda of VarAnnot.t * (Cduce.typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * Cduce.typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t

and e =
  | Bind of VarAnnot.t * Variable.t * a * e
  | Var of Variable.t

val convert_to_normal_form : Ast.annot_expr -> e
val map_e : (e -> e) -> (a -> a) -> e -> e
val map_a : (e -> e) -> (a -> a) -> a -> a
val fold_e : (e -> 'a list -> 'a) -> (a -> 'a list -> 'a) -> e -> 'a
val fold_a : (e -> 'a list -> 'a) -> (a -> 'a list -> 'a) -> a -> 'a

val bv_a : a -> VarSet.t
val bv_e : e -> VarSet.t
val fv_a : a -> VarSet.t
val fv_e : e -> VarSet.t

val merge_annots_a : a list -> a
val merge_annots_e : e list -> e

val pp_a : Format.formatter -> a -> unit
val pp_e : Format.formatter -> e -> unit
val show_a : a -> string
val show_e : e -> string
