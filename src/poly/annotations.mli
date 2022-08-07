open Types.Base
open Common
open Parsing.Variable

val partition : typ list-> typ list
val regroup : ('a -> 'a -> bool) -> ('a * 'b) list -> ('a * ('b list)) list

module Refinements : sig
    type t = Env.t list
    val dom : t -> Variable.t list
    val project : t -> Variable.t -> typ list
    val partition : t -> t
    val compatibles : Env.t -> t -> t
end

module Annot : sig
    type substs = Subst.t list
    type split = (typ*t) list
    and a =
        | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
        | RecordUpdateA of substs | LambdaA of (typ * split) list
    and t =
        | VarA | DoA of (typ * a * split) | SkipA of t | EmptyA of (a * t)
        | UnkA of (a * (split option) * (t option) * (t option))

    val pp_substs : Format.formatter -> substs -> unit
    val pp_split : Format.formatter -> split -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_substs : Subst.t -> substs -> substs
    val apply_subst_split : Subst.t -> split -> split
    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t
end