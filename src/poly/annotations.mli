open Types.Base
open Parsing.Variable

module Refinements : sig
    type t = Common.Env.t list
    val dom : t -> Variable.t list
    val project : t -> Variable.t -> typ list
    val partition : t -> t
    val compatibles : Common.Env.t -> t -> t
end

module Annot : sig
    type t
end

val partition : typ list-> typ list
val regroup : ('a -> 'a -> bool) -> ('a * 'b) list -> ('a * ('b list)) list
