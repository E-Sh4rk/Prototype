open Types.Base
open Types.Additions

module Refinements = Annotations.Refinements

module Annot : sig
    type substs = Subst.t list
    (* NOTE: the bool is just an optimisation for keeping track of splits
       that have already been propagated. *)
    type split = (typ*(bool*t)) list
    (* By decreasing order of importance *)
    (* NOTE: the bool is just a marker for remembering which branches
       are issued from a "complete". *)
    (* TODO: remove this marker... (not used anymore) *)
    and branches = (typ*(bool*split)) list
    and a =
        | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
        | RecordUpdateA of substs
        | LambdaA of branches
    and t =
        | VarA | DoA of (typ * a * split) | SkipA of t | EmptyA of (a * t)
        | UnkA of (a * split)

    val pp_substs : Format.formatter -> substs -> unit
    val pp_split : Format.formatter -> split -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_substs : Subst.t -> substs -> substs
    val apply_subst_branches : Subst.t -> branches -> branches
    val apply_subst_split : Subst.t -> split -> split
    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t

    val initial_a : Msc.a -> a
    val initial_e : Msc.e -> t
end

val partition : typ list-> typ list
val regroup : ('a -> 'a -> bool) -> ('a * 'b) list -> ('a * ('b list)) list
val remove_redundant_branches : Annot.branches ->  Annot.branches
val remove_empty_branches : Annot.branches -> Annot.branches
