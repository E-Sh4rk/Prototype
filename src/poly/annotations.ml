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
      (List.rev lst)@((k, o::os)::treated)
    | elt::lst -> add_if_equiv (elt::treated) lst k o
  in
  let aux acc (k, o) = add_if_equiv [] acc k o in
  List.fold_left aux [] res |> List.rev |>
  List.map (fun (k,v) -> (k, List.rev v))

let remove_redundant_default_branches mono lst =
  let rec is_useful s rs others =
    if is_empty rs then false
    else match others with
    | [] -> true
    | o::others ->
      if subtype o s
      then is_useful s (diff rs o) others
      else is_useful s rs others
  in
  let rec aux treated current = (* TODO: disable removing of unmarked branches *)
    match current with
    | [] -> treated
    (* | (s,(true as b),v)::current -> *)
    | (s,b,v)::current ->
      let others = treated@current |> List.map Utils.fst3 in
      if is_useful s s others
      then aux ((s,b,v)::treated) current
      else aux treated current
    (* | c::current -> aux (c::treated) current *)
  in
  lst |> List.map (fun (t,(b,a)) -> (sup_typ mono t,b,(t,(b,a)))) |>
  (* (fun x -> Utils.log "remove_redundant_default_branches: %a@." (Utils.pp_list pp_typ) (List.map fst x) ; x) |> *)
  List.rev |> aux [] |> List.map Utils.trd3

let remove_empty_branches lst =
  lst |> List.filter (fun (s,_) -> non_empty s)

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
    ss |> List.iteri (fun i s ->
      Format.fprintf fmt "----- Subst %i -----@.%a@." i Subst.pp s
    )
  let apply_subst_substs s ss =
    List.map (fun s' -> Subst.compose_restr s s') ss

  type split = (typ*(bool*t)) list
  [@@deriving show]

  and branches = (typ*(bool*split)) list
  [@@deriving show]

  and a =
      | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
      | RecordUpdateA of substs | LambdaA of branches
      [@@deriving show]

  and t =
      | VarA | DoA of (typ * a * split) | SkipA of t | EmptyA of (a * t)
      | UnkA of (a * split)
      [@@deriving show]

  let rec apply_subst_split s lst =
    lst |> List.map (fun (ty,(b,t)) -> (Subst.apply_simplify s ty, (b, apply_subst s t)))
  and apply_subst_branches s lst =
    let aux (ty, (b,split)) = (Subst.apply_simplify s ty, (b,apply_subst_split s split)) in
    List.map aux lst
  and apply_subst_a s a = match a with
  | NoneA -> NoneA
  | ProjA ss -> ProjA (apply_subst_substs s ss)
  | IteA ss -> IteA (apply_subst_substs s ss)
  | AppA (ss1, ss2) -> AppA (apply_subst_substs s ss1, apply_subst_substs s ss2)
  | RecordUpdateA ss -> RecordUpdateA (apply_subst_substs s ss)
  | LambdaA lst -> LambdaA (apply_subst_branches s lst)
  and apply_subst s t =
  if Subst.is_identity s then t
  else match t with
  | VarA -> VarA
  | DoA (ty, a, split) ->
    DoA (Subst.apply_simplify s ty, apply_subst_a s a, apply_subst_split s split)
  | SkipA t -> SkipA (apply_subst s t)
  | EmptyA (a,t) -> EmptyA (apply_subst_a s a, apply_subst s t)
  | UnkA (a, split) ->
    UnkA (apply_subst_a s a, apply_subst_split s split)

  let rec initial_a a =
    let open Msc in match a with
    | Abstract _ | Const _ | Pair _ | Let _ -> NoneA
    | Ite _ -> IteA []
    | Projection _ -> ProjA []
    | RecordUpdate _ -> RecordUpdateA []
    | App _ -> AppA ([], [])
    | Lambda (_, Parsing.Ast.Unnanoted, v, e) ->
      let initial_s = [(any, (false, initial_e e))] in
      let v = Variable.to_typevar v |> var_typ in
      LambdaA [(v, (false, initial_s))]
    | Lambda (_, Parsing.Ast.ADomain dt, _, e) ->
      let initial_s = [(any, (false, initial_e e))] in
      LambdaA [(dt, (false, initial_s))]
    | Lambda (_, Parsing.Ast.AArrow t, _, e) ->
      let initial_s = [(any, (false, initial_e e))] in
      let branches =
        dnf t |> List.map (List.map fst) |> List.flatten
        |> List.map (fun s -> (s, (false, initial_s)))
      in
      LambdaA branches

  and initial_e e =
      let open Msc in match e with
      | Var _ -> VarA
      | Bind (_, _, a, e) ->
        let initial_a = initial_a a in
        let initial_s = [(any, (false, initial_e e))] in
        UnkA (initial_a, initial_s)
end