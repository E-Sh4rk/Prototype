
let dump_type t =
    Format.printf "%a\n" Cduce.dump t

let print_type t =
    Format.printf "%s\n" (Cduce.string_of_type t)
    (*Format.printf "%s\n" (Cduce.string_of_type (Cduce.domain t))*)

let warning pos msg =
  Format.printf "Warning: %s\t%s\n" (Position.string_of_pos pos) msg

let error pos msg =
  Format.printf "Error: %s\t%s\n" (Position.string_of_pos pos) msg



let option_map f = function None -> None | Some e -> Some (f e)

let memoize f input_transform ht =
  let rec aux input =
    let htbl_key = input_transform input in
    try Hashtbl.find ht htbl_key
    with Not_found ->
    (
      let res = f aux input in
      Hashtbl.replace ht htbl_key res ;
      res
    )
  in aux

let do_not_memoize f =
  let rec aux input =
    f aux input
  in aux
  
