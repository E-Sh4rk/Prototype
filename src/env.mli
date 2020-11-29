open Variable
open Cduce

type t
val empty : t
val bottom : t
val is_bottom : t -> bool
val add : Variable.t -> typ -> t -> t
val find : Variable.t -> t -> typ
val rm : Variable.t -> t -> t
val conj : t list -> t
val show : t -> string
val pp : Format.formatter -> t -> unit
