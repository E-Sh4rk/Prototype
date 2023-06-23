open Base
open Pomap

exception Uncomparable

let compare_typ t1 t2 =
  (*Format.printf "@.Comparison of %a with %a@." pp_typ t1 pp_typ t2 ;*)
  let sub = subtype t1 t2 in
  let super = subtype t2 t1 in
  if sub && super then 0
  else if sub then -1
  else if super then 1
  else raise Uncomparable

  module Type = struct
    type el = typ
    type ord = Unknown | Lower | Equal | Greater
    let compare t1 t2 =
      begin try
          match compare_typ t1 t2 with
          | -1 -> Lower
          | 1 -> Greater
          | 0 -> Equal
          | _ -> assert false
      with Uncomparable -> Unknown end
end
module TypeMap = Pomap_impl.Make(Type)
