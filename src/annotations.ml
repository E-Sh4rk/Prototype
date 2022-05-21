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

let remove_redundance ts =
  (* Format.printf "Remove redundance: %a@." (Utils.pp_list Cduce.pp_typ) ts ; *)
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
  (* |> (fun r -> Format.printf "Result: %a@." (Utils.pp_list Cduce.pp_typ) r ; r) *)

type 'a annot_a' =
  | EmptyAtomA
  | UntypAtomA
  | AppA of Cduce.typ * bool
  | LambdaA of (Cduce.typ (* Last type of the lambda *) * 'a)
  [@@deriving show]

type ('a, 'b) annot' =
  | EmptyA
  | BindA of ('a annot_a' * 'b)
  [@@deriving show]

let rec annot_a_equals el a1 a2 =
  match a1, a2 with
  | EmptyAtomA, EmptyAtomA -> true
  | UntypAtomA, UntypAtomA -> true
  | AppA (t1, b1), AppA (t2, b2) -> b1 = b2 && Cduce.equiv t1 t2
  | LambdaA (t1, a1), LambdaA (t2, a2) -> el a1 a2 && Cduce.equiv t1 t2
  | _, _ -> false
and annot_equals el eb a1 a2 =
  match a1, a2 with
  | EmptyA, EmptyA -> true
  | BindA (a1, b1), BindA (a2, b2) ->
    annot_a_equals el a1 a2 && eb b1 b2
  | _, _ -> false

let rec annot_a_initial cl cb a =
  match a with
  | Abstract _ | Const _ | Ite _ | Pair _ | Projection _
  | RecordUpdate _ | Let _ -> EmptyAtomA
  | App _ -> AppA (Cduce.any_or_absent, false)
  | Lambda (_, Ast.Unnanoted, _, e) ->
    let initial_e = annot_initial cl cb e in
    LambdaA (Cduce.any_or_absent,
      cl "initial" [(Cduce.any, (initial_e, Cduce.any, false))])
  | Lambda (_, _, _, _) ->
    LambdaA (Cduce.any_or_absent, cl "initial" [])

and annot_initial cl cb e =
  match e with
  | Var _ -> EmptyA
  | Bind (_, _, a, e) ->
    let initial_a = annot_a_initial cl cb a in
    let initial_e = annot_initial cl cb e in
    BindA (initial_a, cb "initial" [(Cduce.any_or_absent, initial_e)])

let merge_annot_a ml a1 a2 =
  match a1, a2 with
  | UntypAtomA, a | a, UntypAtomA -> a
  | EmptyAtomA, EmptyAtomA -> EmptyAtomA
  | AppA (t1, b1), AppA (t2, b2) -> AppA (Cduce.cap_o t1 t2, b1 || b2)
  | LambdaA (t1, a1), LambdaA (t2, a2) -> LambdaA (Cduce.cap_o t1 t2, ml a1 a2)
  | _, _ -> assert false

let merge_annot ml mb a1 a2 =
  match a1, a2 with
  | EmptyA, EmptyA -> EmptyA
  | BindA (a1, b1), BindA (a2, b2) ->
    BindA (merge_annot_a ml a1 a2, mb b1 b2)
  | _, _ -> assert false

module Node = struct
  type t = { id:int }
  [@@deriving show]
  let default_node = { id=0 }
  let new_node =
    let last_id = ref 0 in
    fun () -> last_id := !last_id + 1 ; {id = !last_id}
  let node_of_id =
    let h = Hashtbl.create 1000 in
    fun str ->
      match Hashtbl.find_opt h str with
      | None ->
        let res = new_node () in
        Hashtbl.add h str res ;
        res
      | Some n -> n
  let equals n1 n2 = n1.id = n2.id
end

module rec LambdaSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list
  val add : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool) -> t
  val merge : t -> t -> t
  val construct : (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list -> t
  val construct_with_custom_eq : string -> (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list -> t
  val map_top : (Cduce.typ -> Cduce.typ -> bool -> Cduce.typ * Cduce.typ * bool) -> t -> t
  val enrich : opt_branches_maxdom:Cduce.typ -> former_typ:Cduce.typ -> (t,BindSA.t) annot'
               -> t -> (Cduce.typ * Cduce.typ) list -> t
  val splits : t -> Cduce.typ list
  val apply : t -> Cduce.typ -> Cduce.typ -> bool -> (t,BindSA.t) annot'
  val normalize : t -> t
  val equals : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of Node.t * (Cduce.typ * ((t, BindSA.t) annot' * Cduce.typ * bool)) list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) = Node.equals n1 n2
  let empty () = T (Node.default_node, [])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, (a, t, b)) =
    if List.exists (fun (s', (a', t', b')) ->
      annot_equals equals BindSA.equals a a' &&
      b=b' && Cduce.equiv s s' && Cduce.equiv t t') lst
    then T (node, lst)
    else T (Node.new_node (), (s, (a, t, b))::lst)
  let merge a1 a2 =
    if equals a1 a2 then a1
    else destruct a2 |> List.fold_left add a1
  let construct lst =
    List.fold_left add (empty ()) lst
  let construct_with_custom_eq str lst =
    let T (_, a) = construct lst in
    T (Node.node_of_id str, a)
  let map_top f (T (_, lst)) =
    lst |> List.map (fun (s, (a,t,b)) ->
      let (s, t, b) = f s t b in
      (s, (a, t, b)))
    (* |> construct*)
    |> (fun res -> T (Node.new_node (), res))
  let enrich ~opt_branches_maxdom ~former_typ default_anns lst ts =
    let t =
      destruct lst |>
      List.filter_map (fun (s, (_,t,b)) ->
      if b
      then Some (Cduce.mk_arrow (Cduce.cons s) (Cduce.cons t))
      else None
    ) |> Types_additions.conj |> Cduce.cap_o former_typ in
    let annot (s',t') =
      let req = (Types_additions.top_jokers Types_additions.Max s') = [] in
      let s' = if req then s' else Cduce.cap_o s' opt_branches_maxdom in
      let arrow_type = Cduce.mk_arrow (Cduce.cons s') (Cduce.cons t') in
      if Cduce.subtype t arrow_type then None
      else
        let s' = Types_additions.substitute_top_jokers Types_additions.Max s' Cduce.any in
        let t' = Types_additions.substitute_top_jokers Types_additions.Min t' Cduce.any in
        Some (s', (default_anns, t', req))
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
  val destruct : t -> (Cduce.typ * (LambdaSA.t, t) annot') list
  val add : t -> Cduce.typ * (LambdaSA.t, t) annot' -> t
  val merge : t -> t -> t
  val construct : (Cduce.typ * (LambdaSA.t, t) annot') list -> t
  val construct_with_custom_eq : string -> (Cduce.typ * (LambdaSA.t, t) annot') list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
  val splits : t -> Cduce.typ list
  val apply : t -> Cduce.typ -> (LambdaSA.t, t) annot'
  val normalize : t -> Cduce.typ -> t
  val equals : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of Node.t * (Cduce.typ * (LambdaSA.t, t) annot') list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) = Node.equals n1 n2
  let empty () = T (Node.default_node, [])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, a) =
    if List.exists (fun (s', a') ->
      annot_equals LambdaSA.equals equals a a' && Cduce.equiv s s') lst
    then T (node, lst)
    else T (Node.new_node (), (s, a)::lst)
  let merge a1 a2 =
    if equals a1 a2 then a1
    else destruct a2 |> List.fold_left add a1
  let construct lst =
    List.fold_left add (empty ()) lst
  let construct_with_custom_eq str lst =
    let T (_, a) = construct lst in
    T (Node.node_of_id str, a)
  let map_top f (T (_, lst)) =
    lst |> List.map (fun (s, a) -> (f s, a))
    (* |> construct*)
    |> (fun res -> T (Node.new_node (), res))
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

let initial_annot_a =
  annot_a_initial LambdaSA.construct_with_custom_eq BindSA.construct_with_custom_eq
let initial_annot =
  annot_initial LambdaSA.construct_with_custom_eq BindSA.construct_with_custom_eq

let merge_annot_a = merge_annot_a LambdaSA.merge
let merge_annot = merge_annot LambdaSA.merge BindSA.merge

let annotate_def_with_last_type t anns =
  match anns with
  | EmptyAtomA -> EmptyAtomA
  | UntypAtomA -> UntypAtomA
  | AppA (t,b) -> AppA (t,b)
  | LambdaA (_, lsa) -> LambdaA (t, lsa)
