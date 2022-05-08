type 'a annot_a' =
  | EmptyAtomA
  | UntypAtomA
  | AppA of Cduce.typ * bool
  | LambdaA of 'a
  [@@deriving show]

type ('a, 'b) annot' =
  | EmptyA
  | UntypA
  | BindA of ('a annot_a' * 'b)
  [@@deriving show]

let annot_equals_approx a1 a2 =
  match a1, a2 with
  | EmptyA, EmptyA -> true
  | UntypA, UntypA -> true
  | _, _ -> false

module rec LambdaSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ)) list
  val add : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ) -> t
  val construct : (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ)) list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> (Cduce.typ -> Cduce.typ) -> t -> t
  val enrich : t -> (Cduce.typ * Cduce.typ) list -> t
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of (Cduce.typ * ((t, BindSA.t) annot' * Cduce.typ)) list
  [@@deriving show]
  let empty () = T []
  let destruct (T lst) = lst
  let add (T lst) (s, (a, t)) =
    if List.exists (fun (s', (a', t')) ->
      annot_equals_approx a a' && Cduce.equiv s s' && Cduce.equiv t t') lst
    then T lst
    else T ((s, (a, t))::lst)
  let construct lst =
    List.fold_left add (empty ()) lst
  let map_top f1 f2 (T lst) =
    lst |> List.map (fun (s, (a,t)) -> (f1 s, (a, f2 t)))
    (* |> construct*)
    |> (fun res -> T res)
  let enrich (T lst) ts =
    let t = List.map (fun (s, (_,t)) ->
      Cduce.mk_arrow (Cduce.cons s) (Cduce.cons t)
    ) lst
    |> Types_additions.conj in
    let annot (s',t') =
      let t' = Cduce.mk_arrow (Cduce.cons s') (Cduce.cons t') in
      if Cduce.subtype t t' then None else Some (s', (EmptyA, t'))
    in
    let new_anns = List.filter_map annot ts in
    List.fold_left add (T lst) new_anns
end

and BindSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> (Cduce.typ * (t,BindSA.t) annot') list
  val add : t -> Cduce.typ * (t,BindSA.t) annot' -> t
  val construct : (Cduce.typ * (t,BindSA.t) annot') list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
  val splits : t -> Cduce.typ list
  val dom : t -> Cduce.typ
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of (Cduce.typ * (LambdaSA.t, t) annot') list
  [@@deriving show]
  let empty () = T []
  let destruct = failwith "TODO"
  let add = failwith "TODO"
  let construct = failwith "TODO"
  let map_top = failwith "TODO"
  let splits = failwith "TODO"
  let dom = failwith "TODO"
end

type annot_a = LambdaSA.t annot_a'
[@@deriving show]
type annot = (LambdaSA.t, BindSA.t) annot'
[@@deriving show]
