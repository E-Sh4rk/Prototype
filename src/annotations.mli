open Variable

module VarAnnot : sig
  type t
  val empty : t
  val splits : Env.t -> t -> Cduce.typ list
  val add_split : Env.t -> Cduce.typ -> t -> t
end

module Annotations : sig
  type t
  val empty : t
  val splits : Variable.t -> Env.t -> t -> Cduce.typ list
  val add_split : Variable.t ->Env.t ->  Cduce.typ -> t -> t

  val mem_var : Variable.t -> t -> bool
  val add_var : Variable.t -> VarAnnot.t -> t -> t
  val remove_var : Variable.t -> t -> t
  val get_var : Variable.t -> t -> VarAnnot.t
end
