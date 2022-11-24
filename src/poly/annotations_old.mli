open Types.Base
open Types.Tvar
open Parsing.Variable

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
       that have yet to be propagated. *)
    type split = (typ*(bool*t)) list
    and branches = (typ*split) list
    and a =
        | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
        | RecordUpdateA of substs
        | LambdaA of branches (* Fully Explored *) * branches (* Remaining *)
    and t =
        | VarA | DoA of (a * typ option * split) | SkipA of t | DoSkipA of (a * split * t)

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
