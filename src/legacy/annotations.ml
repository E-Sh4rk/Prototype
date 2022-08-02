open Common.Msc
open Types.Base
open Types.Additions
open Parsing

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

(*let remove_redundance ts =
  (* Format.printf "Remove redundance: %a@." (Utils.pp_list pp_typ) ts ; *)
  let change = ref false in
  let aux ts t =
    let t' = ts |> List.filter (fun t' ->
      subtype t' t && not (subtype t t'))
      |> disj
    in
    if is_empty t' then t
    else (change := true ; diff t t')
  in
  let rec it ts =
    change := false ;
    let ts = List.map (aux ts) ts in
    if !change then it ts else ts
  in
  it ts |> Utils.remove_duplicates equiv
  (* |> (fun r -> Format.printf "Result: %a@." (Utils.pp_list pp_typ) r ; r) *)*)

let partition lst =
  let rec aux lst =
    let rm_empty = List.filter (fun t -> is_empty t |> not) in
    let inter t1 t2 =
      if disjoint t1 t2 then t1 else cap_o t1 t2
    in
    match rm_empty lst with
    | [] -> []
    | t::lst ->
      let s = List.fold_left inter t lst in
      let lst = (t::lst)
      |> List.map (fun t -> diff_o t s)
      |> aux
      in
      s::lst
  in aux lst

  let partition_non_empty lst =
    match partition lst with
    | [] -> [empty]
    | lst -> lst

  module type Annot = sig
    type a
    type e
    val equals_a : a -> a -> bool
    val equals_e : e -> e -> bool
    val merge_a : a -> a -> a
    val merge_e : e -> e -> e
    val initial_a : Msc.a -> a
    val initial_e : Msc.e -> e
    val pp_a : Format.formatter -> a -> unit
    val pp_e : Format.formatter -> e -> unit
    val show_a : a -> string
    val show_e : e -> string
end
module type LambdaSA_Common = sig
  type annot
  type t
  val empty : unit -> t
  val merge : t -> t -> t
  val splits : t -> typ list
  val normalize : t -> t
  val equals : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end
module type LambdaSA = sig
  include LambdaSA_Common
  val destruct : t -> (typ * (annot * typ * bool)) list
  val add : t -> typ * (annot * typ * bool) -> t
  val construct : (typ * (annot * typ * bool)) list -> t
  val construct_with_custom_eq : string -> (typ * (annot * typ * bool)) list -> t
  val map_top : (typ -> typ -> bool -> typ * typ * bool) -> t -> t
  val apply : t -> typ -> typ -> bool -> annot
  val enrich : opt_branches_maxdom:typ -> former_typ:typ -> annot
  -> t -> (typ * typ) list -> t
end
module type LambdaSAP = sig
  include LambdaSA_Common
  val destruct : t -> (typ * (annot * typ)) list
  val add : t -> typ * (annot * typ) -> t
  val construct : (typ * (annot * typ)) list -> t
  val construct_with_custom_eq : string -> (typ * (annot * typ)) list -> t
  val apply : t -> typ -> typ -> annot
  val enrich : former_typ:typ -> annot
  -> t -> (typ * typ) list -> t
end
module type BindSA_Common = sig
  type annot
  type t
  val empty : unit -> t
  val destruct : t -> (typ * annot) list
  val add : t -> typ * annot -> t
  val merge : t -> t -> t
  val construct : (typ * annot) list -> t
  val construct_with_custom_eq : string -> (typ * annot) list -> t
  val splits : t -> typ list
  val apply : t -> typ -> annot
  val equals : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end
module type BindSA = sig
  include BindSA_Common
  val normalize : t -> typ -> t
  val map_top : (typ -> typ) -> t -> t
end
module type BindSAP = sig
  include BindSA_Common
  val normalize : t -> t
end

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

module LambdaSAMake (A:Annot) =
struct
  type annot = A.e
  [@@deriving show]
  type t = T of Node.t * (typ * (annot * typ * bool)) list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) = Node.equals n1 n2
  let empty () = T (Node.default_node, [])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, (a, t, b)) =
    if List.exists (fun (s', (a', t', b')) ->
      A.equals_e a a' && b=b' && equiv s s' && equiv t t') lst
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
  let splits (T (_, lst)) =
    List.map fst lst
  let apply_aux lst s =
    let anns = lst |> List.filter_map (fun (s', (anns, _, _)) ->
      if subtype s s'
      then Some anns else None
    ) in
    match anns with
    | [] -> assert false
    | a1::anns -> List.fold_left A.merge_e a1 anns
  let apply (T (_, lst)) s t b =
    let lst = lst |> List.filter (fun (_, (_, t', b')) ->
      b = b' && equiv t t'
    ) in
    apply_aux lst s
  let normalize (T (node, lst)) =
    let equiv (t1,b1) (t2,b2) =
      b1 = b2 && equiv t1 t2
    in
    let ts = lst
      |> List.map (fun (s, (anns, t, b)) -> ((t, b), (s, anns)))
      |> regroup equiv in
    let lst = ts
      |> List.map (fun ((t,b), lst) ->
        let ss = List.map (fun (s,_) -> s) lst |> partition_non_empty in
        let lst = lst |> List.map (fun (s, anns) -> (s, (anns, t, b))) in
        List.map (fun s -> (s, (apply_aux lst s, t, b))) ss
      )
    in
    T (node, List.flatten lst)
  let enrich ~opt_branches_maxdom ~former_typ default_anns lst ts =
    let t =
      destruct lst |>
      List.filter_map (fun (s, (_,t,b)) ->
      if b
      then Some (mk_arrow (cons s) (cons t))
      else None
    ) |> conj |> cap_o former_typ in
    let annot (s',t') =
      let req = (top_jokers Max s') |> TVarSet.is_empty in
      let s' = if req then s' else cap_o s' opt_branches_maxdom in
      let arrow_type = mk_arrow (cons s') (cons t') in
      if subtype t arrow_type then None
      else
        let s' = substitute_top_jokers Max s' any in
        let t' = substitute_top_jokers Min t' any in
        Some (s', (default_anns, t', req))
    in
    let new_anns = List.filter_map annot ts in
    List.fold_left add lst new_anns
end
module LambdaSAPMake (A:Annot): (LambdaSAP with type annot=A.e) =
struct
  type annot = A.e
  [@@deriving show]
  type t = T of Node.t * (typ * (annot * typ)) list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) = Node.equals n1 n2
  let empty () = T (Node.default_node, [])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, (a, t)) =
    if List.exists (fun (s', (a', t')) ->
      A.equals_e a a' && equiv s s' && equiv t t') lst
    then T (node, lst)
    else T (Node.new_node (), (s, (a, t))::lst)
  let merge a1 a2 =
    if equals a1 a2 then a1
    else destruct a2 |> List.fold_left add a1
  let construct lst =
    List.fold_left add (empty ()) lst
  let construct_with_custom_eq str lst =
    let T (_, a) = construct lst in
    T (Node.node_of_id str, a)
  let splits (T (_, lst)) =
    List.map fst lst
  let apply_aux lst s =
    let anns = lst |> List.filter_map (fun (s', (anns, _)) ->
      if subtype s s'
      then Some anns else None
    ) in
    match anns with
    | [] -> assert false
    | a1::anns -> List.fold_left A.merge_e a1 anns
  let apply (T (_, lst)) s t =
    let lst = lst |> List.filter (fun (_, (_, t')) ->
      equiv t t'
    ) in
    apply_aux lst s
  let normalize (T (node, lst)) =
    let ts = lst
      |> List.map (fun (s, (anns, t)) -> (t, (s, anns)))
      |> regroup equiv in
    let lst = ts
      |> List.map (fun (t, lst) ->
        let ss = List.map (fun (s,_) -> s) lst |> partition_non_empty in
        let lst = lst |> List.map (fun (s, anns) -> (s, (anns, t))) in
        List.map (fun s -> (s, (apply_aux lst s, t))) ss
      )
    in
    T (node, List.flatten lst)
  let enrich ~former_typ default_anns lst ts =
    let t =
      destruct lst |>
      List.map (fun (s, (_,t)) ->
      mk_arrow (cons s) (cons t)
    ) |> conj |> cap_o former_typ in
    let annot (s',t') =
      let arrow_type = mk_arrow (cons s') (cons t') in
      if subtype t arrow_type then None
      else Some (s', (default_anns, t'))
    in
    let new_anns = List.filter_map annot ts in
    List.fold_left add lst new_anns
end

module BindSACMake (A:Annot) = struct
  type annot = A.e
  [@@deriving show]
  type t = T of Node.t * (typ * annot) list
  [@@deriving show]
  let equals (T (n1,_)) (T (n2,_)) = Node.equals n1 n2
  let empty () = T (Node.default_node, [])
  let destruct (T (_, lst)) = lst
  let add (T (node, lst)) (s, a) =
    if List.exists (fun (s', a') -> A.equals_e a a' && equiv s s') lst
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
  let splits (T (_, lst)) =
    List.map fst lst
  let apply (T (_, lst)) t =
    let anns = lst |> List.filter_map (fun (t', anns) ->
      if subtype t t'
      then Some anns else None
    ) in
    match anns with
    | [] -> assert false
    | a1::anns -> List.fold_left A.merge_e a1 anns
end
module BindSAMake (A:Annot): (BindSA with type annot=A.e) = struct
  include BindSACMake(A)
  let normalize ((T (node, _)) as anns) s =
    let ts = splits anns
      |> List.map (cap_o s)
      |> partition_non_empty in
    T (node, List.map (fun t -> (t, apply anns t)) ts)
  let map_top f (T (_, lst)) =
    lst |> List.map (fun (s, a) -> (f s, a))
    (* |> construct*)
    |> (fun res -> T (Node.new_node (), res))
end
module BindSAPMake (A:Annot): (BindSAP with type annot=A.e) = struct
  include BindSACMake(A)
  let normalize ((T (node, _)) as anns) =
    let ts = splits anns
      |> partition_non_empty in
    T (node, List.map (fun t -> (t, apply anns t)) ts)
end

(* === MONOMORPHIC SYSTEM === *)

type 'lsa anns_a =
| EmptyAtomA
| UntypAtomA
| AppA of typ * bool
| LambdaA of (typ (* Last type of the lambda *) * 'lsa)
[@@deriving show]
type ('lsa, 'bsa) anns_e =
| EmptyA
| BindA of ('lsa anns_a * 'bsa)
[@@deriving show]

module type AnnotMono = sig
  include Annot
  val annotate_def_with_last_type : typ -> a -> a
end

module rec BindSA : (BindSA with type annot=AnnotMono.e) = BindSAMake(AnnotMono)
and LambdaSA : (LambdaSA with type annot=AnnotMono.e) = LambdaSAMake(AnnotMono)
and AnnotMono : (AnnotMono with type a=LambdaSA.t anns_a and type e=(LambdaSA.t, BindSA.t) anns_e) =
struct
  type a = LambdaSA.t anns_a
  [@@deriving show]
  type e = (LambdaSA.t, BindSA.t) anns_e
  [@@deriving show]

  let equals_a a1 a2 =
    match a1, a2 with
    | EmptyAtomA, EmptyAtomA -> true
    | UntypAtomA, UntypAtomA -> true
    | AppA (t1, b1), AppA (t2, b2) -> b1 = b2 && equiv t1 t2
    | LambdaA (t1, a1), LambdaA (t2, a2) ->
      LambdaSA.equals a1 a2 && equiv t1 t2
    | _, _ -> false
  let equals_e a1 a2 =
    match a1, a2 with
    | EmptyA, EmptyA -> true
    | BindA (a1, b1), BindA (a2, b2) ->
      BindSA.equals b1 b2 && equals_a a1 a2
    | _, _ -> false

  let rec initial_a a : a =
    match a with
    | Abstract _ | Const _ | Ite _ | Pair _ | Projection _
    | RecordUpdate _ | Let _ -> EmptyAtomA
    | App _ -> AppA (any_or_absent, false)
    | Lambda (_, Ast.Unnanoted, _, e) ->
      let initial_e = initial_e e in
      LambdaA (any_or_absent,
        LambdaSA.construct_with_custom_eq "initial"
        [(any, (initial_e, any, false))])
    | Lambda (_, _, _, _) ->
      LambdaA (any_or_absent,
      LambdaSA.construct_with_custom_eq "initial" [])
  and initial_e e : e =
    match e with
    | Var _ -> EmptyA
    | Bind (_, _, a, e) ->
      let initial_a = initial_a a in
      let initial_e = initial_e e in
      BindA (initial_a, BindSA.construct_with_custom_eq "initial"
      [(any_or_absent, initial_e)])

  let merge_a a1 a2 =
    match a1, a2 with
    | UntypAtomA, a | a, UntypAtomA -> a
    | EmptyAtomA, EmptyAtomA -> EmptyAtomA
    | AppA (t1, b1), AppA (t2, b2) -> AppA (cap_o t1 t2, b1 || b2)
    | LambdaA (t1, a1), LambdaA (t2, a2) ->
      LambdaA (cap_o t1 t2, LambdaSA.merge a1 a2)
    | _, _ -> assert false
  let merge_e a1 a2 =
    match a1, a2 with
    | EmptyA, EmptyA -> EmptyA
    | BindA (a1, b1), BindA (a2, b2) ->
      BindA (merge_a a1 a2, BindSA.merge b1 b2)
    | _, _ -> assert false

  let annotate_def_with_last_type t anns =
    match anns with
    | EmptyAtomA -> EmptyAtomA
    | UntypAtomA -> UntypAtomA
    | AppA (t,b) -> AppA (t,b)
    | LambdaA (_, lsa) -> LambdaA (t, lsa)
end

(* === POLYMORPHIC SYSTEM === *)

module Inst = struct
  type t = Subst.t list
  [@@deriving show]

  let empty = []
  let equals _ _ = false (* Approximation *)
  let add t s =
    if List.exists (Subst.equiv s) t
    then t else s::t
  let union t1 t2 =
    List.fold_left add t1 t2
end

type 'lsa anns_a_poly =
| PEmptyAtomA
| PUntypAtomA
| PInstA of Inst.t
| PLambdaA of (typ (* Last type of the lambda *) * 'lsa)
[@@deriving show]
type ('lsa, 'bsa) anns_e_poly =
| PEmptyA
| PBindA of ('lsa anns_a_poly * 'bsa)
[@@deriving show]

module type AnnotPoly = sig
    include Annot
    val annotate_def_with_last_type : typ -> a -> a
end

module rec BindSAP : (BindSAP with type annot=AnnotPoly.e) = BindSAPMake(AnnotPoly)
and LambdaSAP : (LambdaSAP with type annot=AnnotPoly.e) = LambdaSAPMake(AnnotPoly)
and AnnotPoly : (AnnotPoly with type a=LambdaSAP.t anns_a_poly and type e=(LambdaSAP.t, BindSAP.t) anns_e_poly) =
struct
  type a = LambdaSAP.t anns_a_poly
  [@@deriving show]
  type e = (LambdaSAP.t, BindSAP.t) anns_e_poly
  [@@deriving show]

  let equals_a a1 a2 =
    match a1, a2 with
    | PEmptyAtomA, PEmptyAtomA -> true
    | PUntypAtomA, PUntypAtomA -> true
    | PInstA i1, PInstA i2 -> Inst.equals i1 i2
    | PLambdaA (t1, a1), PLambdaA (t2, a2) ->
      LambdaSAP.equals a1 a2 && equiv t1 t2
    | _, _ -> false
  let equals_e a1 a2 =
    match a1, a2 with
    | PEmptyA, PEmptyA -> true
    | PBindA (a1, b1), PBindA (a2, b2) ->
      BindSAP.equals b1 b2 && equals_a a1 a2
    | _, _ -> false

  let rec initial_a a : a =
    match a with
    | Abstract _ | Const _ | Ite _ | Pair _
    | RecordUpdate _ | Let _ -> PEmptyAtomA
    | Projection _ | App _ -> PInstA []
    | Lambda (_, Ast.Unnanoted, v, e) ->
      let initial_e = initial_e e in
      PLambdaA (any_or_absent,
      LambdaSAP.construct_with_custom_eq "initial"
        [(Variable.Variable.to_typevar v |> var_typ, (initial_e, any))])
    | Lambda (_, _, _, _) ->
      PLambdaA (any_or_absent,
      LambdaSAP.construct_with_custom_eq "initial" [])
  and initial_e e : e =
    match e with
    | Var _ -> PEmptyA
    | Bind (_, _, a, e) ->
      let initial_a = initial_a a in
      let initial_e = initial_e e in
      PBindA (initial_a, BindSAP.construct_with_custom_eq "initial"
      [(any_or_absent, initial_e)])

  let merge_a a1 a2 =
    match a1, a2 with
    | PUntypAtomA, a | a, PUntypAtomA -> a
    | PEmptyAtomA, PEmptyAtomA -> PEmptyAtomA
    | PInstA i1, PInstA i2 -> PInstA (Inst.union i1 i2)
    | PLambdaA (t1, a1), PLambdaA (t2, a2) ->
      PLambdaA (cap_o t1 t2, LambdaSAP.merge a1 a2)
    | _, _ -> assert false
  let merge_e a1 a2 =
    match a1, a2 with
    | PEmptyA, PEmptyA -> PEmptyA
    | PBindA (a1, b1), PBindA (a2, b2) ->
      PBindA (merge_a a1 a2, BindSAP.merge b1 b2)
    | _, _ -> assert false

  let annotate_def_with_last_type t anns =
    match anns with
    | PEmptyAtomA -> PEmptyAtomA
    | PUntypAtomA -> PUntypAtomA
    | PInstA ss -> PInstA ss
    | PLambdaA (_, lsa) -> PLambdaA (t, lsa)
end
