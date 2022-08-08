open Parsing.Variable
open Types.Base

type t
val empty : t
val is_empty : t -> bool
val singleton : Variable.t -> typ -> t
val construct : (Variable.t * typ) list -> t
val add : Variable.t -> typ -> t -> t
val strengthen : Variable.t -> typ -> t -> t
val domain : t -> Variable.t list
val bindings : t -> (Variable.t * typ) list
val mem : Variable.t -> t -> bool
val mem_not_absent : Variable.t -> t -> bool
val find : Variable.t -> t -> typ
val rm : Variable.t -> t -> t
val cap : t -> t -> t
val conj : t list -> t
val filter : (Variable.t -> typ -> bool) -> t -> t

val equiv : t -> t -> bool
val leq : t -> t -> bool

val show : t -> string
val pp : Format.formatter -> t -> unit
val pp_filtered : string list -> Format.formatter -> t -> unit
