open Variable
open Cduce

type t
val empty : t
val is_empty : t -> bool
val contains_empty : t -> bool
val singleton : Variable.t -> typ -> t
val add : Variable.t -> typ -> t -> t
val strengthen : Variable.t -> typ -> t -> t
val domain : t -> Variable.t list
val mem : Variable.t -> t -> bool
val find : Variable.t -> t -> typ
val rm : Variable.t -> t -> t
val cap : t -> t -> t
val conj : t list -> t
val filter : (Variable.t -> typ -> bool) -> t -> t

val equiv : t -> t -> bool
val leq : t -> t -> bool
val disjoint : t -> t -> bool

val show : t -> string
val pp : Format.formatter -> t -> unit
val pp_filtered : string list -> Format.formatter -> t -> unit
