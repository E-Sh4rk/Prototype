
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

    val typ : t -> Base.typ

    val pp : Format.formatter -> t -> unit
end

module TVarSet : sig
    type t
    val empty : t
    val construct : TVar.t list -> t
    val is_empty : t -> bool
    val mem : t -> TVar.t -> bool
    val filter : (TVar.t -> bool) -> t -> t
    val union : t -> t -> t
    val union_many : t list -> t
    val add : TVar.t -> t -> t
    val inter : t -> t -> t
    val inter_many : t list -> t
    val diff : t -> t -> t
    val rm : TVar.t -> t -> t
    val equal : t -> t -> bool
    val destruct : t -> TVar.t list
    val pp : Format.formatter -> t -> unit
end

module Subst : sig
    type t
    val construct : (TVar.t * Base.typ) list -> t
    val identity : t
    val is_identity : t -> bool
    val dom : t -> TVarSet.t
    val codom : t -> TVarSet.t
    val mem : t -> TVar.t -> bool
    val rm: TVar.t -> t -> t
    val find : t -> TVar.t -> Base.typ
    val find' : t -> TVar.t -> Base.typ
    val equiv : t -> t -> bool
    val apply : t -> Base.typ -> Base.typ
    val destruct : t -> (TVar.t * Base.typ) list
    val compose : t -> t -> t
    val compose_restr : t -> t -> t
    val combine : t -> t -> t
    val restrict : t -> TVarSet.t -> t
    val remove : t -> TVarSet.t -> t
    val split : t -> TVarSet.t -> t * t
    val is_renaming : t -> bool
    (* val inverse_renaming : t -> t *)
    val short_names : TVarSet.t -> t
    val pp : Format.formatter -> t -> unit
end

val vars : Base.typ -> TVarSet.t
val vars_mono : Base.typ -> TVarSet.t
val vars_poly : Base.typ -> TVarSet.t
val vars_infer : Base.typ -> TVarSet.t
val top_vars : Base.typ -> TVarSet.t
val vars_with_polarity : Base.typ -> (TVar.t * [ `Both | `Neg | `Pos ]) list
val check_var : Base.typ -> [ `Not_var | `Pos of TVar.t | `Neg of TVar.t ]
val is_mono_typ : Base.typ -> bool
val is_novar_typ : Base.typ -> bool

val refresh : TVarSet.t -> Subst.t
val generalize : TVarSet.t -> Subst.t
val monomorphize : TVarSet.t -> Subst.t
val pp_typ_short : Format.formatter -> Base.typ -> unit
val string_of_type_short : Base.typ -> string

(* Operations on types *)

module Raw : sig
    val clean_type : pos:Base.typ -> neg:Base.typ -> TVarSet.t -> Base.typ -> Base.typ
    val rectype : Base.typ -> TVar.t -> Base.typ (* [rectype t u] returns the type corresponding to the equation u=t *)
    (* Variables not in var_order are considered greater. In the result, a variable will be expressed
    in term of the variables that are greater. Thus, greater variables (in particular variables not in var_order)
    are less likely to be constrained. *)
    val tallying : var_order:(TVar.t list) -> TVarSet.t -> (Base.typ * Base.typ) list -> Subst.t list
    val test_tallying : var_order:(TVar.t list) -> TVarSet.t -> (Base.typ * Base.typ) list -> bool
end

val clean_type : pos:Base.typ -> neg:Base.typ -> Base.typ -> Base.typ
val clean_type_subst : pos:Base.typ -> neg:Base.typ -> Base.typ -> Subst.t
val ground_inf : Base.typ -> Base.typ (* ground type smaller than every instance of t *)
val ground_sup : Base.typ -> Base.typ (* ground type larger than every instance of t *)
val test_tallying : (Base.typ * Base.typ) list -> bool
val tallying : (Base.typ * Base.typ) list -> Subst.t list
val tallying_infer : (Base.typ * Base.typ) list -> Subst.t list

(* Some additions *)
val factorize : TVarSet.t * TVarSet.t -> Base.typ -> Base.typ * Base.typ
