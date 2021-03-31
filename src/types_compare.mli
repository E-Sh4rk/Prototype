open Cduce

exception Uncomparable

(* /!\ Not a total order (can raise Uncomparable) *)
val compare_typ : typ -> typ -> int
