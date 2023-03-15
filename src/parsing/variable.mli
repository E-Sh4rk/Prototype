module Variable : sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val compare : t -> t -> int
  val equals : t -> t -> bool
  (* val create : binding:bool -> lambda:bool -> string option -> t *)
  val create_binding : string option -> t
  val create_lambda : string option -> t
  val create_other : string option -> t
  val attach_location : t -> Position.t -> unit
  val get_locations : t -> Position.t list
  val is_binding_var : t -> bool
  val is_lambda_var : t -> bool
  val get_name : t -> string option
end

module VarMap : Map.S with type key=Variable.t
module VarSet : Set.S with type elt=Variable.t
