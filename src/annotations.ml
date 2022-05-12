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

let annot_equals_approx a1 a2 =
  match a1, a2 with
  | EmptyA, EmptyA -> true
  | _, _ -> false

module rec LambdaSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list
  val add : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool) -> t
  val construct : (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ * bool)) list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> (Cduce.typ -> Cduce.typ) -> t -> t
  val enrich : new_branches_maxdom:Cduce.typ -> t -> (Cduce.typ * Cduce.typ) list -> t
  val splits : t -> Cduce.typ list
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of (Cduce.typ * ((t, BindSA.t) annot' * Cduce.typ * bool)) list
  [@@deriving show]
  let empty () = T []
  let destruct (T lst) = lst
  let add (T lst) (s, (a, t, b)) =
    if List.exists (fun (s', (a', t', b')) ->
      annot_equals_approx a a' &&
      b=b' && Cduce.equiv s s' && Cduce.equiv t t') lst
    then T lst
    else T ((s, (a, t, b))::lst)
  let construct lst =
    List.fold_left add (empty ()) lst
  let map_top f1 f2 (T lst) =
    lst |> List.map (fun (s, (a,t,b)) -> (f1 s, (a, f2 t, b)))
    (* |> construct*)
    |> (fun res -> T res)
  let enrich ~new_branches_maxdom (T lst) ts =
    let t = List.map (fun (s, (_,t,_)) ->
      (* NOTE: we should only consider branches with b=true as the others
         are not guaranteed. But it would duplicate most of the branches...
         and the faulty scenarios shouldn't happen.
         The paper always consider annotations to have b=false
         and consider them here anyway. *)
      Cduce.mk_arrow (Cduce.cons s) (Cduce.cons t)
    ) lst
    |> Types_additions.conj in
    let annot (s',t') =
      let s' = Cduce.cap_o s' new_branches_maxdom in
      let t' = Cduce.mk_arrow (Cduce.cons s') (Cduce.cons t') in
      if Cduce.subtype t t' then None
      else
        let req = (Types_additions.top_jokers Types_additions.Max s') = [] in
        let s' = Types_additions.substitute_top_jokers Types_additions.Max s' Cduce.any in
        let t' = Types_additions.substitute_top_jokers Types_additions.Min t' Cduce.any in
        Some (s', (EmptyA, t', req))
    in
    let new_anns = List.filter_map annot ts in
    List.fold_left add (T lst) new_anns
  let splits (T lst) =
    List.map fst lst
end

and BindSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> (Cduce.typ * (LambdaSA.t, t) annot') list
  val add : t -> Cduce.typ * (LambdaSA.t, t) annot' -> t
  val construct : (Cduce.typ * (LambdaSA.t, t) annot') list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
  val choose : t -> Cduce.typ -> t
  val splits : t -> Cduce.typ list
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of (Cduce.typ * (LambdaSA.t, t) annot') list
  [@@deriving show]
  let empty () = T []
  let destruct (T lst) = lst
  let add (T lst) (s, a) =
    if List.exists (fun (s', a') ->
      annot_equals_approx a a' && Cduce.equiv s s') lst
    then T lst
    else T ((s, a)::lst)
  let construct lst =
    List.fold_left add (empty ()) lst
  let map_top f (T lst) =
    lst |> List.map (fun (s, a) -> (f s, a))
    (* |> construct*)
    |> (fun res -> T res)
  let choose (T lst) t =
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
    T (aux [] lst t)
  let splits (T lst) =
    List.map fst lst
end

type annot_a = LambdaSA.t annot_a'
[@@deriving show]
type annot = (LambdaSA.t, BindSA.t) annot'
[@@deriving show]
