
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
      |> List.map (fun t -> Cduce.diff_o t s)
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

type various =
    | VTyp of Cduce.typ
    [@@deriving show]

type 'a annot_a' =
    | No_annot_a
    | Various of various
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
    (*let floor (T t) =
      T (List.map (fun (t,anns) -> (Types_additions.floor t, anns)) t)
    let ceil (T t) =
      T (List.map (fun (t,anns) -> (Types_additions.ceil t, anns)) t)*)
end

let merge_annots_a anns1 anns2 =
  match anns1, anns2 with
  | No_annot_a, No_annot_a -> No_annot_a
  | No_annot_a, _ | _, No_annot_a -> assert false
  | Various a, Various b when a=b -> Various a
  | Various _, _ | _, Various _ -> assert false
  | Annot_a va1, Annot_a va2 ->
    let splits = (SplitAnnot.splits va1)@(SplitAnnot.splits va2) |> partition in
    let dom = SplitAnnot.dom va2 in
    let lst = List.map (fun s ->
      let a =
        if Cduce.subtype s dom
        then SplitAnnot.apply va2 s
        else SplitAnnot.apply va1 s
      in (s, a)
    ) splits in
    Annot_a (SplitAnnot.create lst)

let rec map_annot_a f anns =
  match anns with
  | No_annot_a -> No_annot_a
  | Various v -> Various v
  | Annot_a va -> Annot_a (map_sa f va)
and map_annot f anns =
  match anns with
  | No_annot -> No_annot
  | Annot (anns_a, va) -> Annot (map_annot_a f anns_a, map_sa f va)
and map_sa f va =
  let lst = SplitAnnot.destruct va in
  lst |> List.map
    (fun (t, anns) -> (f t, map_annot f anns))
  |> SplitAnnot.create

let subst_annot_a s = map_annot_a (Cduce.substitute s)
let subst_annot s = map_annot (Cduce.substitute s)
let subst_sa s = map_sa (Cduce.substitute s)

type annot_a = SplitAnnot.t annot_a'
[@@deriving show]
type annot = SplitAnnot.t annot'
[@@deriving show]
