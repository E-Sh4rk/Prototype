type 'a annot_a' =
    | EmptyAtomA
    | UntypAtomA
    | AppA of Cduce.typ * bool
    | LambdaA of 'a

type ('a, 'b) annot' =
    | EmptyA
    | BindA of ('a annot_a' * 'b)

module rec LambdaSA : sig
    type t
    val empty : unit -> t
    val destruct : t -> (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ)) list
    val add : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ) -> t
    val construct : (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ)) list -> t
    val map_top : (Cduce.typ -> Cduce.typ) -> (Cduce.typ -> Cduce.typ) -> t -> t
    val enrich : t -> (Cduce.typ * Cduce.typ) list -> t
    val splits : t -> Cduce.typ list
    val dom : t -> Cduce.typ
end
and BindSA : sig
    type t
    val empty : unit -> t
    val destruct : t -> (Cduce.typ * (LambdaSA.t, t) annot') list
    val add : t -> Cduce.typ * (LambdaSA.t, t) annot' -> t
    val construct : (Cduce.typ * (LambdaSA.t, t) annot') list -> t
    val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
    val splits : t -> Cduce.typ list
    val dom : t -> Cduce.typ
end

type annot_a = LambdaSA.t annot_a'
type annot = (LambdaSA.t, BindSA.t) annot'

val pp_annot_a : Format.formatter -> annot_a -> unit
val pp_annot : Format.formatter -> annot -> unit
val show_annot_a : annot_a -> string
val show_annot : annot -> string