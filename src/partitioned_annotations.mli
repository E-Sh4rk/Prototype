
val partition : Cduce.typ list -> Cduce.typ list

type various =
    | VTyp of Cduce.typ

type 'a annot_a' =
    | No_annot_a
    | Various of various
    | Annot_a of 'a

type 'a annot' =
    | No_annot
    | Annot of ('a annot_a' * 'a)

module SplitAnnot : sig
    type t
    val create : (Cduce.typ * (t annot')) list -> t
    val splits : t -> Cduce.typ list
    val dom : t -> Cduce.typ
    val apply : t -> Cduce.typ -> t annot'
    val destruct : t -> (Cduce.typ * (t annot')) list
    (*val floor : t -> t
    val ceil : t -> t*)
end

type annot_a = SplitAnnot.t annot_a'
type annot = SplitAnnot.t annot'

val merge_annots_a : annot_a -> annot_a -> annot_a
val map_annot_a : (Cduce.typ -> Cduce.typ) -> annot_a -> annot_a
val map_annot : (Cduce.typ -> Cduce.typ) -> annot -> annot
val map_sa : (Cduce.typ -> Cduce.typ) -> SplitAnnot.t -> SplitAnnot.t
val subst_annot_a : Cduce.subst -> annot_a -> annot_a
val subst_annot : Cduce.subst -> annot -> annot
val subst_sa : Cduce.subst -> SplitAnnot.t -> SplitAnnot.t

val pp_annot_a : Format.formatter -> annot_a -> unit
val pp_annot : Format.formatter -> annot -> unit
val show_annot_a : annot_a -> string
val show_annot : annot -> string