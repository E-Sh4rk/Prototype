open Types.Base
open Parsing.Variable

val partition : typ list-> typ list
val regroup : ('a -> 'a -> bool) -> ('a * 'b) list -> ('a * ('b list)) list
val remove_redundant_branches : TVarSet.t -> (typ * 'a) list -> (typ * 'a) list
val remove_empty_branches : (typ * 'a) list -> (typ * 'a) list

module Refinements : sig
    type t = Common.Env.t list
    val dom : t -> Variable.t list
    val project : t -> Variable.t -> typ list
    val partition : t -> t
    val compatibles : Common.Env.t -> t -> t
end

module Annot : sig
    type substs = Subst.t list
    (* NOTE: the bool is just an optimisation for keeping track of splits
       that have already been propagated. *)
    type split = (typ*(bool*t)) list
    and a =
        | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
        | RecordUpdateA of substs
        | LambdaA of (typ * split) list (* By decreasing order of importance *)
    and t =
        | VarA | DoA of (typ * a * split) | SkipA of t | EmptyA of (a * t)
        | UnkA of (a * split)

    val pp_substs : Format.formatter -> substs -> unit
    val pp_split : Format.formatter -> split -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_substs : Subst.t -> substs -> substs
    val apply_subst_branches : Subst.t -> (typ * split) list -> (typ * split) list
    val apply_subst_split : Subst.t -> split -> split
    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t

    val initial_a : Msc.a -> a
    val initial_e : Msc.e -> t
end