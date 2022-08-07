open Types.Base
open Types.Additions
open Common
open Parsing.Variable

let partition lst =
  let inter t1 t2 = if disjoint t1 t2 then t1 else cap_o t1 t2 in
  let rec aux dom lst =
    if lst = [] then [dom]
    else
      let lst = lst
        |> List.map (fun t -> cap_o t dom)
        |> List.filter (fun t -> is_empty t |> not) in
      let s = List.fold_left inter dom lst in
      s::(aux (diff_o dom s) lst)
  in aux any lst

let regroup equiv res =
  let rec add_if_equiv treated lst k o =
    match lst with
    | [] -> (k,[o])::treated
    | (k', os)::lst when equiv k k' ->
      ((k, o::os)::lst)@treated
    | elt::lst -> add_if_equiv (elt::treated) lst k o
  in
  let aux acc (k, o) = add_if_equiv [] acc k o in
  List.fold_left aux [] res

module Refinements = struct
  type t = Env.t list
  let dom lst =
    lst |> List.map (fun e -> Env.domain e |> VarSet.of_list)
    |> List.fold_left VarSet.union VarSet.empty |> VarSet.elements
  let project lst x =
    lst |> List.filter_map (fun e -> try Some (Env.find x e) with _ -> None)
  let partition lst =
    let rec aux vs = match vs with
    | [] -> [Env.empty]
    | v::vs ->
      let res = aux vs in
      project lst v |> partition
      |> List.map (fun t -> List.map (Env.add v t) res)
      |> List.flatten
    in
    aux (dom lst)
  let compatibles env lst =
    let dom = Env.domain env |> VarSet.of_list in
    lst |> List.filter (fun env' ->
      let compat x =
        let t = Env.find x env in
        let t' = Env.find x env' in
        is_empty t || non_empty (cap t t')
      in
      let dom' = Env.domain env' |> VarSet.of_list in
      VarSet.subset dom' dom && VarSet.for_all compat dom'
    )
end

module Annot = struct
  type substs = Subst.t list
  let pp_substs fmt ss =
    Format.fprintf fmt "Substs[%i]" (List.length ss)
  let apply_subst_substs s ss =
    List.map (fun s' -> Subst.compose_restr s s') ss

  type split = (typ*t) list
  [@@deriving show]

  and a =
      | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
      | RecordUpdateA of substs | LambdaA of (typ * split) list
      [@@deriving show]

  and t =
      | VarA | DoA of (typ * a * split) | SkipA of t
      | EmptyA of (a * t)
      | UnkA of (a * (split option) * (t option) * (t option))
      [@@deriving show]

  let apply_subst_split = failwith "TODO"
  let apply_subst_a = failwith "TODO"
  let apply_subst = failwith "TODO"
end