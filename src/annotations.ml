
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

type 'a annot' =
  | No_annot
  | Annot of ('a annot_a' * 'a)

module SplitAnnot = struct
    type t = T of (Cduce.typ * (t annot')) list
    let create lst =
      assert (lst |> List.map fst |> check_disjointness) ;
      T lst
    let splits (T t) = List.map fst t
    let dom t =
      let ts = splits t in
      assert (ts <> []) ;
      Types_additions.disj ts
    let apply (T t) typ =
      match t |> List.filter (fun (t',_) -> Cduce.subtype typ t') with
      | [] -> No_annot
      | [(_, annots)] -> annots
      | _ -> assert false
end

type annot_a = SplitAnnot.t annot_a'
type annot = SplitAnnot.t annot'
