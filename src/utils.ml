
let dump_type t =
    Format.printf "%a\n" Cduce.dump t

let print_type t =
    Format.printf "%s\n" (Cduce.string_of_type t)
    (*Format.printf "%s\n" (Cduce.string_of_type (Cduce.domain t))*)

let warning pos msg =
  let pos = List.fold_left (
    fun acc pos ->
    Format.asprintf "%s %s" acc (Position.string_of_pos pos)
  ) "" pos in
  Format.printf "Warning:%s\t%s\n" pos msg

let error pos msg =
  let pos = List.fold_left (
    fun acc pos ->
    Format.asprintf "%s %s" acc (Position.string_of_pos pos)
  ) "" pos in
  Format.printf "Error:%s\t%s\n" pos msg



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

let rec remove_duplicates equiv lst =
  let remove elt lst = List.filter (fun e -> equiv elt e |> not) lst in
  match lst with
  | [] -> []
  | e::lst -> e::(remove e lst |> remove_duplicates equiv)

let pp_list pp_elt fmt lst =
  Format.fprintf fmt "[" ;
  List.iter (fun elt -> Format.fprintf fmt " %a ;" pp_elt elt) lst ;
  Format.fprintf fmt " ]"
