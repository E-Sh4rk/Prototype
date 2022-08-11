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

let remove_redundant_branches mono lst =
  (* NOTE: We should use tallying to determine subtyping and emptiness
     (in the case there are non-cleanable vars), but no need for it for now. *)
  let rec is_useful s rs others =
    if is_empty rs then false
    else match others with
    | [] -> true
    | o::others ->
      if subtype o s
      then is_useful s (diff rs o) others
      else is_useful s rs others
  in
  let rec aux treated current =
    match current with
    | [] -> treated
    | (s,v)::current ->
      let others = treated@current |> List.map fst in
      if is_useful s s others
      then aux ((s,v)::treated) current
      else aux treated current
  in
  lst |> List.map (fun (t,a) -> (clean_type ~pos:any ~neg:empty mono t,(t,a))) |>
  aux [] |> List.map snd

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

  type split = (typ*t) list
  [@@deriving show]

  and a =
      | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
      | RecordUpdateA of substs | LambdaA of (typ * split) list
      [@@deriving show]

  and t =
      | VarA | DoA of (typ * a * split) | SkipA of t | EmptyA of (a * t)
      | UnkA of (a * (split option) * (t option) * (t option))
      [@@deriving show]

  let rec apply_subst_split s lst =
    lst |> List.map (fun (ty,t) -> (Subst.apply_simplify s ty, apply_subst s t))
  and apply_subst_a s a = match a with
  | NoneA -> NoneA
  | ProjA ss -> ProjA (apply_subst_substs s ss)
  | IteA ss -> IteA (apply_subst_substs s ss)
  | AppA (ss1, ss2) -> AppA (apply_subst_substs s ss1, apply_subst_substs s ss2)
  | RecordUpdateA ss -> RecordUpdateA (apply_subst_substs s ss)
  | LambdaA lst ->
    let aux (ty, split) = (Subst.apply_simplify s ty, apply_subst_split s split) in
    LambdaA (List.map aux lst)
  and apply_subst s t =
  if Subst.is_identity s then t
  else match t with
  | VarA -> VarA
  | DoA (ty, a, split) ->
    DoA (Subst.apply_simplify s ty, apply_subst_a s a, apply_subst_split s split)
  | SkipA t -> SkipA (apply_subst s t)
  | EmptyA (a,t) -> EmptyA (apply_subst_a s a, apply_subst s t)
  | UnkA (a, so, to1, to2) ->
    UnkA (apply_subst_a s a, Option.map (apply_subst_split s) so,
      Option.map (apply_subst s) to1, Option.map (apply_subst s) to2)

  let rec initial_a a =
    let open Msc in match a with
    | Abstract _ | Const _ | Pair _ | Let _ -> NoneA
    | Ite _ -> IteA []
    | Projection _ -> ProjA []
    | RecordUpdate _ -> RecordUpdateA []
    | App _ -> AppA ([], [])
    | Lambda (_, Parsing.Ast.Unnanoted, v, e) ->
      let initial_s = [(any, initial_e e)] in
      let v = Variable.to_typevar v |> var_typ in
      LambdaA [(v, initial_s)]
    | Lambda (_, Parsing.Ast.ADomain dt, _, e) ->
      let initial_s = [(any, initial_e e)] in
      LambdaA [(dt, initial_s)]
    | Lambda (_, Parsing.Ast.AArrow t, _, e) ->
      let initial_s = [(any, initial_e e)] in
      let branches =
        dnf t |> List.map (List.map fst) |> List.flatten
        |> List.map (fun s -> (s, initial_s))
      in
      LambdaA branches

  and initial_e e =
      let open Msc in match e with
      | Var _ -> VarA
      | Bind (_, _, a, e) ->
        let initial_a = initial_a a in
        let initial_e = initial_e e in
        let initial_s = [(any, initial_e)] in
        UnkA (initial_a, Some initial_s, Some initial_e, Some initial_e)

  let retype a t =
    let a = initial_a a in
    match t with
    | VarA -> VarA
    | UnkA (_,s,t1,t2) -> UnkA (a,s,t1,t2)
    | SkipA (t) -> UnkA (a, Some [(any,t)], Some t, Some t)
    | DoA (_, _, s) -> UnkA (a, Some s, None, None)
    | EmptyA (_, t) -> UnkA (a, None, None, Some t)
end