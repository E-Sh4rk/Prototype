open Base
open Pomap

exception Uncomparable

(* /!\ Not a total order (can raise Uncomparable) *)
val compare_typ : typ -> typ -> int

module TypeMap : Pomap_intf.POMAP with type key = typ
