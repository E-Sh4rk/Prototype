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

type substs = Subst.t list
type anns_split = (typ*anns) list
and anns_a =
    | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
    | RecordUpdateA of substs | LambdaA of (typ * anns_split) list
and anns =
    | VarA | DoA of (typ * anns_a * anns_split) | SkipA of anns
    | EmptyA of (anns_a * anns)
    | UnkA of (anns_a * (anns_split option) * (anns option) * (anns option))

val pp_substs : Format.formatter -> substs -> unit
val pp_anns_split : Format.formatter -> anns_split -> unit
val pp_anns_a : Format.formatter -> anns_a -> unit
val pp_anns : Format.formatter -> anns -> unit