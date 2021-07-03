open Variable
open Cduce

type t
val empty : Env.t -> t
val is_empty : t -> bool

val strengthen : Variable.t -> typ -> t -> t
val strengthen_strict : Variable.t -> typ -> t -> t
val rm : Variable.t -> t -> t

val refined_domain : t -> Variable.t list
val domain : t -> Variable.t list
val mem : Variable.t -> t -> bool
val find : Variable.t -> t -> typ

val show : t -> string
val pp : Format.formatter -> t -> unit
val pp_filtered : string list -> Format.formatter -> t -> unit
