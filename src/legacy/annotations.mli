
open Types.Base
open Common

val regroup : ('a -> 'a -> bool) -> ('a * 'b) list -> ('a * ('b list)) list
(*val remove_redundance : typ list -> typ list*)
val partition : typ list -> typ list
val partition_non_empty : typ list -> typ list

module type Annot = sig
    type a
    type e
    val equals_a : a -> a -> bool
    val equals_e : e -> e -> bool
    val merge_a : a -> a -> a
    val merge_e : e -> e -> e
    val initial_a : Msc.a -> a
    val initial_e : Msc.e -> e
    val pp_a : Format.formatter -> a -> unit
    val pp_e : Format.formatter -> e -> unit
    val show_a : a -> string
    val show_e : e -> string
end
module type LambdaSA_Common = sig
    type annot
    type t
    val empty : unit -> t
    val merge : t -> t -> t
    val splits : t -> typ list
    val normalize : t -> t
    val equals : t -> t -> bool
    val pp : Format.formatter -> t -> unit
end
module type LambdaSA = sig
    include LambdaSA_Common
    val destruct : t -> (typ * (annot * typ * bool)) list
    val add : t -> typ * (annot * typ * bool) -> t
    val construct : (typ * (annot * typ * bool)) list -> t
    val construct_with_custom_eq : string -> (typ * (annot * typ * bool)) list -> t
    val map_top : (typ -> typ -> bool -> typ * typ * bool) -> t -> t
    val apply : t -> typ -> typ -> bool -> annot
    val enrich : opt_branches_maxdom:typ -> former_typ:typ -> annot
    -> t -> (typ * typ) list -> t
end
module type LambdaSAP = sig
    include LambdaSA_Common
    val destruct : t -> (typ * (annot * typ)) list
    val add : t -> typ * (annot * typ) -> t
    val construct : (typ * (annot * typ)) list -> t
    val construct_with_custom_eq : string -> (typ * (annot * typ)) list -> t
    val apply : t -> typ -> typ -> annot
    val enrich : former_typ:typ -> annot
    -> t -> (typ * typ) list -> t
end
module type BindSA_Common = sig
    type annot
    type t
    val empty : unit -> t
    val destruct : t -> (typ * annot) list
    val add : t -> typ * annot -> t
    val merge : t -> t -> t
    val construct : (typ * annot) list -> t
    val construct_with_custom_eq : string -> (typ * annot) list -> t
    val splits : t -> typ list
    val apply : t -> typ -> annot
    val equals : t -> t -> bool
    val pp : Format.formatter -> t -> unit
end
module type BindSA = sig
    include BindSA_Common
    val normalize : t -> typ -> t
    val map_top : (typ -> typ) -> t -> t
end
module type BindSAP = sig
    include BindSA_Common
    val normalize : t -> t
end

(* === MONOMORPHIC SYSTEM === *)

type 'lsa anns_a =
| EmptyAtomA
| UntypAtomA
| AppA of typ * bool
| LambdaA of (typ (* Last type of the lambda *) * 'lsa)
type ('lsa, 'bsa) anns_e =
| EmptyA
| BindA of ('lsa anns_a * 'bsa)

module type AnnotMono = sig
    include Annot
    val annotate_def_with_last_type : typ -> a -> a
end

module rec BindSA : (BindSA with type annot=AnnotMono.e)
and LambdaSA : (LambdaSA with type annot=AnnotMono.e)
and AnnotMono : (AnnotMono with type a=LambdaSA.t anns_a and type e=(LambdaSA.t, BindSA.t) anns_e)

(* === POLYMORPHIC SYSTEM === *)

module Inst: sig
    type t = subst list
    val empty : t
    val equals : t -> t -> bool
    val add : t -> subst -> t
    val union : t -> t -> t
end

type 'lsa anns_a_poly =
| PEmptyAtomA
| PUntypAtomA
| PInstA of Inst.t
| PLambdaA of (typ (* Last type of the lambda *) * 'lsa)
type ('lsa, 'bsa) anns_e_poly =
| PEmptyA
| PBindA of ('lsa anns_a_poly * 'bsa)

module type AnnotPoly = sig
    include Annot
    val annotate_def_with_last_type : typ -> a -> a
end

module rec BindSAP : (BindSAP with type annot=AnnotPoly.e)
and LambdaSAP : (LambdaSAP with type annot=AnnotPoly.e)
and AnnotPoly : (AnnotPoly with type a=LambdaSAP.t anns_a_poly and type e=(LambdaSAP.t, BindSAP.t) anns_e_poly)
