open Types.Base
open Common

val partition : typ -> typ list -> typ list
val partition_for_full_domain : typ list -> typ list

module VarAnnot : sig
  type t
  val empty : t
  val any : t
  val initial_lambda : legacy:bool -> t
  val initial_binding : legacy:bool -> t
  val is_empty : t -> bool
  val singleton : Env.t -> typ -> t
  val full_domain : t -> typ
  val size : t -> int
  val splits : Env.t -> t -> typ list
  val splits_or : typ -> Env.t -> t -> typ list
  val add_split : Env.t -> typ -> t -> t
  val restrict : Env.t -> t -> t
  val cup : t -> t -> t
  val union : t list -> t
  val pp_filtered : string list -> Format.formatter -> t -> unit
  val pp : Format.formatter -> t -> unit
end
