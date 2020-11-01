
type typ = Cduce.typ

module Variable : sig
    type t
    val compare : t -> t -> int
    val equals : t -> t -> bool
    val create : string option -> t
    val attach_location : t -> Position.t -> unit
    val get_locations : t -> Position.t list
    val get_name : t -> string option
end

type a =
  | Const of Ast.const
  | Var of Variable.t
  | Lambda of (typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * typ * e * e
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Debug of string * Variable.t

and e =
  | Let of Variable.t * a * e
  | Atomic of a

val convert_to_normal_form : Ast.annot_expr -> e
