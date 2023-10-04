open Parsing.Variable
open Types.Base
open Types.Tvar

type t
val empty : t
val is_empty : t -> bool
val singleton : Variable.t -> typ -> t
val construct : (Variable.t * typ) list -> t
val construct_dup : (Variable.t * typ) list -> t
val add : Variable.t -> typ -> t -> t
val strengthen : Variable.t -> typ -> t -> t
val domain : t -> Variable.t list
val bindings : t -> (Variable.t * typ) list
val mem : Variable.t -> t -> bool
val find : Variable.t -> t -> typ
val rm : Variable.t -> t -> t
val rms : Variable.t list -> t -> t
val restrict : Variable.t list -> t -> t
val map : (typ -> typ) -> t -> t
val cap : t -> t -> t
val conj : t list -> t
val filter : (Variable.t -> typ -> bool) -> t -> t
val tvars : t -> TVarSet.t
val apply_subst : Subst.t -> t -> t

val equiv : t -> t -> bool
val leq : t -> t -> bool

val show : t -> string
val pp : Format.formatter -> t -> unit
val pp_filtered : string list -> Format.formatter -> t -> unit
