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
  | EVar of Variable.t (* We restrict to variables instead of atomics,
                          in order for every atomic to be localized by a variable *)
  | Hole

val convert_to_normal_form : Ast.annot_expr -> e
val convert_a_to_e : a -> Position.t list -> e
val map_e : (e -> e) -> (a -> a) -> e -> e
val map_a : (e -> e) -> (a -> a) -> a -> a
val fold_e : (e -> 'a list -> 'a) -> (a -> 'a list -> 'a) -> e -> 'a
val fold_a : (e -> 'a list -> 'a) -> (a -> 'a list -> 'a) -> a -> 'a

val pp_a : Format.formatter -> a -> unit
val pp_e : Format.formatter -> e -> unit
val show_a : a -> string
val show_e : e -> string
