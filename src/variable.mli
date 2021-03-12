
module Variable : sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val compare : t -> t -> int
  val equals : t -> t -> bool
  val create : string option -> t
  val attach_location : t -> Position.t -> unit
  val get_locations : t -> Position.t list
  val get_name : t -> string option
end

val get_predefined_var : int -> Variable.t

module VarMap : Map.S with type key=Variable.t
module VarSet : Set.S with type elt=Variable.t
