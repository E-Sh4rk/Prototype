
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
    val mk_fresh : t -> t
    val mk_unregistered : unit -> t
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

val refresh : mono:bool -> TVarSet.t -> Subst.t
val refresh_all : TVarSet.t -> Subst.t
val generalize : TVarSet.t -> Subst.t
val monomorphize : TVarSet.t -> Subst.t
val lookup_unregistered : TVarSet.t -> Subst.t
val register_unregistered : mono:bool -> TVarSet.t -> Subst.t

(* Operations on types *)

(* TODO : Move all functions that use a delta in a Legacy module *)

val inf_typ : TVarSet.t -> Base.typ -> Base.typ
val sup_typ : TVarSet.t -> Base.typ -> Base.typ

(* Tallying *)
val clean_type : pos:Base.typ -> neg:Base.typ -> TVarSet.t -> Base.typ -> Base.typ
val rectype : Base.typ -> TVar.t -> Base.typ (* [rectype t u] returns the type corresponding to the equation u=t *)
(* Variables not in var_order are considered greater. In the result, a variable will be expressed
in term of the variables that are greater. Thus, greater variables (in particular variables not in var_order)
are less likely to be constrained. *)
val tallying : var_order:TVar.t list -> TVarSet.t -> (Base.typ * Base.typ) list -> Subst.t list

(* Some additions *)
val factorize : TVarSet.t * TVarSet.t -> Base.typ -> Base.typ * Base.typ
