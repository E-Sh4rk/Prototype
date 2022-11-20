
module TVar : sig
    type t = Cduce_types.Var.t

    val is_unregistered : t -> bool
    val is_mono : t -> bool
    val is_poly : t -> bool
    val can_infer : t -> bool

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val name : t -> string
    val display_name : t -> string

    val mk_mono : ?infer:bool -> string option -> t
    val mk_poly : string option -> t
    val lookup : string -> t option

    val typ : t -> Base.typ

    val pp : Format.formatter -> t -> unit
end

module type TVarSet = sig
    type t
    val empty : t
    val construct : TVar.t list -> t
    val is_empty : t -> bool
    val mem : t -> TVar.t -> bool
    val filter : (TVar.t -> bool) -> t -> t
    val union : t -> t -> t
    val add : TVar.t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val rm : TVar.t -> t -> t
    val destruct : t -> TVar.t list
    val pp : Format.formatter -> t -> unit
end
module TVarSet : TVarSet

type subst
module type Subst = sig
    type t = subst
    val construct : (TVar.t * Base.typ) list -> t
    val identity : t
    val is_identity : t -> bool
    val dom : t -> TVarSet.t
    val mem : t -> TVar.t -> bool
    val rm: TVar.t -> t -> t
    val find : t -> TVar.t -> Base.typ
    val equiv : t -> t -> bool
    val apply : t -> Base.typ -> Base.typ
    val destruct : t -> (TVar.t * Base.typ) list
    val pp : Format.formatter -> t -> unit
end
module Subst : Subst

val vars : Base.typ -> TVarSet.t
val top_vars : Base.typ -> TVarSet.t
val vars_with_polarity : Base.typ -> (TVar.t * [ `Both | `Neg | `Pos ]) list
val check_var : Base.typ -> [ `Not_var | `Pos of TVar.t | `Neg of TVar.t ]

val generalize : TVarSet.t -> Subst.t
val monomorphize : TVarSet.t -> Subst.t
val lookup_unregistered : TVarSet.t -> Subst.t
val register_unregistered : mono:bool -> TVarSet.t -> Subst.t
