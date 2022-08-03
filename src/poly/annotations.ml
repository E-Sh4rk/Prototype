open Types.Base
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
end
