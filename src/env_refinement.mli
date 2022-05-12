open Variable
open Cduce

type t
val empty : Env.t -> t
val is_empty : t -> bool

val refine_existing : Variable.t -> typ -> t -> t option
val refine : Variable.t -> typ -> t -> t option
val strengthen : Variable.t -> typ -> t -> t
val rm : Variable.t -> t -> t

val refined_domain : t -> Variable.t list
val has_refinement : Variable.t -> t -> bool
val domain : t -> Variable.t list
val mem : Variable.t -> t -> bool
val find : Variable.t -> t -> typ

val to_env : t -> Env.t

val equiv_ref : t -> t -> bool
(* Assumes that the base environment is the same. *)
(* Use the functions equiv and leq if it is not the case. *)
val leq_ref : t -> t -> bool
val equiv : t -> t -> bool
val leq : t -> t -> bool

val show : t -> string
val pp : Format.formatter -> t -> unit
val pp_filtered : string list -> Format.formatter -> t -> unit
