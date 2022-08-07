open Old_annotations

type a = VarAnnot.t Common.Msc.a
type e = VarAnnot.t Common.Msc.e

val from_common_msc : legacy:bool -> unit Common.Msc.e -> e

val pp_a : Format.formatter -> a -> unit
val pp_e : Format.formatter -> e -> unit
val show_a : a -> string
val show_e : e -> string

val merge_annots_a : a list -> a
val merge_annots_e : e list -> e
