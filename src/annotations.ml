
let partition lst =
  let rec aux lst =
    let rm_empty = List.filter (fun t -> Cduce.is_empty t |> not) in
    let inter t1 t2 =
      if Cduce.disjoint t1 t2 then t1 else Cduce.cap_o t1 t2
    in
    match rm_empty lst with
    | [] -> []
    | t::lst ->
      let s = List.fold_left inter t lst in
      let lst = (t::lst)
      |> List.map (fun t -> Cduce.diff t s)
      |> aux
      in
      s::lst
  in aux lst

let rec check_disjointness ts =
  match ts with
  | [] -> true
  | t::ts ->
    List.for_all (fun t' -> Cduce.disjoint t t') ts
    && check_disjointness ts

type 'a annot_a' =
  | No_annot_a
  | Annot_a of 'a
  [@@deriving show]

type 'a annot' =
  | No_annot
  | Annot of ('a annot_a' * 'a)
  [@@deriving show]

module SplitAnnot = struct
    type t = T of (Cduce.typ * (t annot')) list
    [@@deriving show]
    let create lst =
      assert (lst |> List.map fst |> check_disjointness) ;
      T lst
    let splits (T t) = List.map fst t
    let dom t =
      splits t |> Types_additions.disj
    let apply (T t) typ =
      match t |> List.filter (fun (t',_) -> Cduce.subtype typ t') with
      | [] -> No_annot
      | [(_, annots)] -> annots
      | _ -> assert (Cduce.is_empty typ) ; No_annot
    let destruct (T t) = t
    let floor (T t) =
      T (List.map (fun (t,anns) -> (Types_additions.floor t, anns)) t)
    let ceil (T t) =
      T (List.map (fun (t,anns) -> (Types_additions.ceil t, anns)) t)
end

type annot_a = SplitAnnot.t annot_a'
[@@deriving show]
type annot = SplitAnnot.t annot'
[@@deriving show]
