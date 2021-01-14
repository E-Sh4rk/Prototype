open Variable

module VarAnnot : sig
  type t
  val empty : t
  val is_empty : t -> bool
  val splits : Env.t -> ?initial:Cduce.typ -> t -> Cduce.typ list
  val splits_strict : Env.t -> t -> Cduce.typ list
  val add_split : Env.t -> Cduce.typ -> t -> t
  val cup : t -> t -> t
  val partition : Cduce.typ list -> Cduce.typ list
  val pp_filtered : string list -> Format.formatter -> t -> unit
end

module Annotations : sig
  type t
  val empty : t
  val is_empty : Variable.t -> t -> bool
  val splits : Variable.t -> Env.t -> ?initial:Cduce.typ -> t -> Cduce.typ list
  val splits_strict : Variable.t -> Env.t -> t -> Cduce.typ list
  val add_split : Variable.t -> Env.t -> Cduce.typ -> t -> t
  val cup : t -> t -> t
  val union : t list -> t

  val mem_var : Variable.t -> t -> bool
  val add_var : Variable.t -> VarAnnot.t -> t -> t
  val remove_var : Variable.t -> t -> t
  val get_var : Variable.t -> t -> VarAnnot.t
  val restrict : VarSet.t -> t -> t
end
