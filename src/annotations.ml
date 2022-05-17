open Msc

let regroup equiv res =
  let rec add_if_equiv treated lst t o =
    match lst with
    | [] -> (t,[o])::treated
    | (t', os)::lst when equiv t t' ->
      ((t, o::os)::lst)@treated
    | elt::lst -> add_if_equiv (elt::treated) lst t o
  in
  let aux acc (t, o) =
    add_if_equiv [] acc t o
  in
  List.fold_left aux [] res

let remove_redundance ts =
  let change = ref false in
  let aux ts t =
    let t' = ts |> List.filter (fun t' ->
      Cduce.subtype t' t && not (Cduce.subtype t t'))
      |> Types_additions.disj
    in
    if Cduce.is_empty t' then t
    else (change := true ; Cduce.diff t t')
  in
  let rec it ts =
    change := false ;
    let ts = List.map (aux ts) ts in
    if !change then it ts else ts
  in
  it ts |> Utils.remove_duplicates Cduce.equiv

type 'a annot_a' =
  | EmptyAtomA
  | UntypAtomA
  | AppA of Cduce.typ * bool
  | LambdaA of 'a
  [@@deriving show]

type ('a, 'b) annot' =
  | EmptyA
  | BindA of ('a annot_a' * 'b)
  [@@deriving show]

let rec annot_a_equals el a1 a2 =
  match a1, a2 with
  | EmptyAtomA, EmptyAtomA -> true
  | UntypAtomA, UntypAtomA -> true
  | AppA (t1, b1), AppA (t2, b2) -> Cduce.equiv t1 t2 && b1 = b2
  | LambdaA a1, LambdaA a2 -> el a1 a2
  | _, _ -> false
and annot_equals el eb a1 a2 =
  match a1, a2 with
  | EmptyA, EmptyA -> true
  | BindA (a1, b1), BindA (a2, b2) ->
    annot_a_equals el a1 a2 && eb b1 b2
  | _, _ -> false

let annot_a_initial il a =
  match a with
  | Abstract _ | Const _ | Ite _ | Pair _ | Projection _
  | RecordUpdate _ | Let _ -> EmptyAtomA
  | App _ -> AppA (Cduce.any_or_absent, false)
  | Lambda (_, _, _, e) -> LambdaA (il e)

let annot_initial il ib e =
  match e with
  | Var _ -> EmptyA
  | Bind (_, _, a, e) -> BindA (annot_a_initial il a, ib e)

let merge_annot_a ml a1 a2 =
  match a1, a2 with
  | UntypAtomA, a | a, UntypAtomA -> a
  | EmptyAtomA, EmptyAtomA -> EmptyAtomA
  | AppA (t1, b1), AppA (t2, b2) -> AppA (Cduce.cap_o t1 t2, b1 || b2)
  | LambdaA a1, LambdaA a2 -> LambdaA (ml a1 a2)
  | _, _ -> assert false

let merge_annot ml mb a1 a2 =
  match a1, a2 with
  | EmptyA, EmptyA -> EmptyA
  | BindA (a1, b1), BindA (a2, b2) ->
    BindA (merge_annot_a ml a1 a2, mb b1 b2)
  | _, _ -> assert false

module rec LambdaSA : sig
  type t
  val empty : unit -> t
  val initial : Msc.e -> t
  val destruct : t -> (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list
  val add : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool) -> t
  val merge : t -> t -> t
  val construct : (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> (Cduce.typ -> Cduce.typ) -> t -> t
  val enrich : new_branches_maxdom:Cduce.typ -> t -> (Cduce.typ * Cduce.typ) list -> t
  val splits : t -> Cduce.typ list
  val apply : t -> Cduce.typ -> Cduce.typ -> bool -> (t,BindSA.t) annot'
  val normalize : t -> t
  val equals : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end = struct
  type node = { id:int }
  [@@deriving show]
  let initial_node = { id=1 }
  (* NOTE: For simplicity, we consider all the initial annots equal. *)
  let empty_node = { id=0 }
  let new_node =
    let last_id = ref 1 in
    fun () -> last_id := !last_id + 1 ; {id = !last_id}
  type t = T of node * (Cduce.typ * ((t, BindSA.t) annot' * Cduce.typ * bool)) list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) =
    n1.id = n2.id
  let empty () = T (empty_node, [])
  let rec initial e =
    let a = annot_initial initial BindSA.initial e in
    T (initial_node, [(Cduce.any, (a, Cduce.any, false))])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, (a, t, b)) =
    if List.exists (fun (s', (a', t', b')) ->
      annot_equals equals BindSA.equals a a' &&
      b=b' && Cduce.equiv s s' && Cduce.equiv t t') lst
    then T (node, lst)
    else T (new_node (), (s, (a, t, b))::lst)
  let merge a1 a2 =
    if equals a1 a2 then a1
    else destruct a2 |> List.fold_left add a1
  let construct lst =
    List.fold_left add (empty ()) lst
  let map_top f1 f2 (T (_, lst)) =
    lst |> List.map (fun (s, (a,t,b)) -> (f1 s, (a, f2 t, b)))
    (* |> construct*)
    |> (fun res -> T (new_node (), res))
  let enrich ~new_branches_maxdom lst ts =
    let t =
      destruct lst |>
      List.map (fun (s, (_,t,_)) ->
      (* NOTE: we should only consider branches with b=true as the others
         are not guaranteed. But it would duplicate most of the branches...
         and the faulty scenarios shouldn't happen.
         The paper always consider annotations to have b=false
         and consider them here anyway. *)
      Cduce.mk_arrow (Cduce.cons s) (Cduce.cons t)
    ) |> Types_additions.conj in
    let annot (s',t') =
      let s' = Cduce.cap_o s' new_branches_maxdom in
      let t' = Cduce.mk_arrow (Cduce.cons s') (Cduce.cons t') in
      if Cduce.subtype t t' then None
      else
        let req = (Types_additions.top_jokers Types_additions.Max s') = [] in
        let s' = Types_additions.substitute_top_jokers Types_additions.Max s' Cduce.any in
        let t' = Types_additions.substitute_top_jokers Types_additions.Min t' Cduce.any in
        Some (s', (EmptyA (* TODO *), t', req))
    in
    let new_anns = List.filter_map annot ts in
    List.fold_left add lst new_anns
  let splits (T (_, lst)) =
    List.map fst lst
  let apply_aux lst s =
    let anns = lst |> List.filter_map (fun (s', (anns, _, _)) ->
      if Cduce.subtype s s'
      then Some anns else None
    ) in
    match anns with
    | [] -> assert false
    | a1::anns -> List.fold_left (merge_annot merge BindSA.merge) a1 anns
  let apply (T (_, lst)) s t b =
    let lst = lst |> List.filter (fun (_, (_, t', b')) ->
      b = b' && Cduce.equiv t t'
    ) in
    apply_aux lst s
  let normalize (T (node, lst)) =
    let equiv (t1,b1) (t2,b2) =
      b1 = b2 && Cduce.equiv t1 t2
    in
    let regroup = regroup equiv in
    let ts = lst
      |> List.map (fun (s, (anns, t, b)) -> ((t, b), (s, anns)))
      |> regroup in
    let lst = ts
      |> List.map (fun ((t,b), lst) ->
        let ss = List.map (fun (s,_) -> s) lst |> remove_redundance in
        let lst = lst |> List.map (fun (s, anns) -> (s, (anns, t, b))) in
        List.map (fun s -> (s, (apply_aux lst s, t, b))) ss
      )
    in
    T (node, List.flatten lst)
end
and BindSA : sig
  type t
  val empty : unit -> t
  val initial : Msc.e -> t
  val destruct : t -> (Cduce.typ * (LambdaSA.t, t) annot') list
  val add : t -> Cduce.typ * (LambdaSA.t, t) annot' -> t
  val merge : t -> t -> t
  val construct : (Cduce.typ * (LambdaSA.t, t) annot') list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
  val choose : t -> Cduce.typ -> t
  val splits : t -> Cduce.typ list
  val apply : t -> Cduce.typ -> (LambdaSA.t, t) annot'
  val normalize : t -> Cduce.typ -> t
  val equals : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end = struct
  type node = { id:int }
  [@@deriving show]
  let initial_node = { id=1 }
  (* NOTE: For simplicity, we consider all the initial annots equal. *)
  let empty_node = { id=0 }
  let new_node =
    let last_id = ref 1 in
    fun () -> last_id := !last_id + 1 ; {id = !last_id}
  type t = T of node * (Cduce.typ * (LambdaSA.t, t) annot') list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) =
    n1.id = n2.id
  let empty () = T (empty_node, [])
  let rec initial e =
    let a = annot_initial LambdaSA.initial initial e in
    T (initial_node, [(Cduce.any_or_absent, a)])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, a) =
    if List.exists (fun (s', a') ->
      annot_equals LambdaSA.equals equals a a' && Cduce.equiv s s') lst
    then T (node, lst)
    else T (new_node (), (s, a)::lst)
  let merge a1 a2 =
    if equals a1 a2 then a1
    else destruct a2 |> List.fold_left add a1
  let construct lst =
    List.fold_left add (empty ()) lst
  let map_top f (T (_, lst)) =
    lst |> List.map (fun (s, a) -> (f s, a))
    (* |> construct*)
    |> (fun res -> T (new_node (), res))
  let choose (T (_, lst)) t =
    let max lst =
      lst |> List.partition (fun (t,_) ->
        lst |> List.exists (fun (t', _) ->
          Cduce.subtype t t' && not (Cduce.subtype t' t)
        ) |> not
      )
    in
    let rec aux acc lst t =
      match lst with
      | [(t', anns')] when acc=[] -> [(t', anns')]
      | [] -> acc
      | lst ->
        begin match max lst with
        | ([], _) -> assert false
        | (hd::tl, lst) ->
          let lst = tl@lst in
          let ot = List.map fst lst |> Types_additions.disj in
          if Cduce.subtype t ot
          then aux acc lst t
          else aux (hd::acc) lst (Cduce.diff t (fst hd))
        end
    in
    T (new_node (), aux [] lst t)
  let splits (T (_, lst)) =
    List.map fst lst
  let apply (T (_, lst)) t =
    let anns = lst |> List.filter_map (fun (t', anns) ->
      if Cduce.subtype t t'
      then Some anns else None
    ) in
    match anns with
    | [] -> assert false
    | a1::anns -> List.fold_left (merge_annot LambdaSA.merge merge) a1 anns
  let normalize ((T (node, _)) as anns) s =
    let ts = splits anns
      |> List.map (Cduce.cap_o s)
      |> remove_redundance in
    T (node, List.map (fun t -> (t, apply anns t)) ts)
end

type annot_a = LambdaSA.t annot_a'
[@@deriving show]
type annot = (LambdaSA.t, BindSA.t) annot'
[@@deriving show]

let equals_annot_a = annot_a_equals LambdaSA.equals
let equals_annot = annot_equals LambdaSA.equals BindSA.equals

let initial_annot_a = annot_a_initial LambdaSA.initial
let initial_annot = annot_initial LambdaSA.initial BindSA.initial

let merge_annot_a = merge_annot_a LambdaSA.merge
let merge_annot = merge_annot LambdaSA.merge BindSA.merge
