
val partition : Cduce.typ -> Cduce.typ list -> Cduce.typ list
val partition_for_full_domain : Cduce.typ list -> Cduce.typ list

module VarAnnot : sig
  type t
  val empty : t
  val any : t
  val initial : t
  val is_empty : t -> bool
  val singleton : Env.t -> Cduce.typ -> t
  val full_domain : t -> Cduce.typ
  val size : t -> int
  val splits : Env.t -> t -> Cduce.typ list
  val add_split : Env.t -> Cduce.typ -> t -> t
  val restrict : Env.t -> t -> t
  val cup : t -> t -> t
  val union : t list -> t
  val pp_filtered : string list -> Format.formatter -> t -> unit
  val pp : Format.formatter -> t -> unit
end
