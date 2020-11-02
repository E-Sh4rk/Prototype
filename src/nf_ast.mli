open Variable

type a =
  | Const of Ast.const
  | Var of Variable.t
  | Lambda of (Cduce.typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * Cduce.typ * e * e
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Debug of string * Variable.t

and e =
  | Let of Variable.t * a * e
  | Atomic of a

val convert_to_normal_form : Ast.annot_expr -> e
