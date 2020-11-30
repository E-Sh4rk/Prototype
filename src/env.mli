open Variable
open Cduce

type t
val empty : t
val bottom : t
val is_bottom : t -> bool
val singleton : Variable.t -> typ -> t
val add : Variable.t -> typ -> t -> t
val mem : Variable.t -> t -> bool
val find : Variable.t -> t -> typ
val rm : Variable.t -> t -> t
val cap : t -> t -> t
val conj : t list -> t
val show : t -> string
val pp : Format.formatter -> t -> unit
