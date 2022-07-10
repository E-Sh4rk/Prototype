open Variable
open Cduce

type t
val from_env : Env.t -> t
val to_env : t -> Env.t

val push : t -> t
val merge : t -> t
val pop : t -> t

val domain : t -> Variable.t list
val mem : Variable.t -> t -> bool
val find : Variable.t -> t -> typ
val is_empty : t -> bool
val bindings : t -> (Variable.t * typ) list

val domain_ref : t -> Variable.t list
val mem_ref : Variable.t -> t -> bool
val find_ref : Variable.t -> t -> typ
val is_empty_ref : t -> bool
val bindings_ref : t -> (Variable.t * typ) list

val strengthen : Variable.t -> typ -> t -> t
val refine_old : Variable.t -> typ -> t -> t option
val refine : Variable.t -> typ -> t -> t option
val rm_ref : Variable.t -> t -> t
val rm_deep : Variable.t -> t -> t
val neg_ref : t -> t list
val neg_refs : t (* Base *) -> t list -> t list

val equiv : t -> t -> bool
val leq : t -> t -> bool

val equiv_ref : t -> t -> bool
val leq_ref : t -> t -> bool

val show : t -> string
val pp : Format.formatter -> t -> unit
val pp_filtered : string list -> Format.formatter -> t -> unit
