open Types.Base
open Types.Tvar
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

  and branches = (typ*split) list
  [@@deriving show]

  and a =
    | NoneA | ProjA of substs | IteA of substs | AppA of (substs * substs)
    | RecordUpdateA of substs | ConstraintA of substs
    | LambdaA of branches (* Fully Explored *) * branches (* Remaining *)
    [@@deriving show]

  and t =
    | VarA | DoA of (a * typ option * split) | SkipA of t | DoSkipA of (a * split * t)
    [@@deriving show]

  let rec apply_subst_split s lst =
    lst |> List.map (fun (ty,(b,t)) -> (apply_subst_simplify s ty, (b, apply_subst s t)))
  and apply_subst_branches s lst =
    let aux (ty, split) = (apply_subst_simplify s ty, apply_subst_split s split) in
    List.map aux lst
  and apply_subst_a s a = match a with
  | NoneA -> NoneA
  | ProjA ss -> ProjA (apply_subst_substs s ss)
  | IteA ss -> IteA (apply_subst_substs s ss)
  | AppA (ss1, ss2) -> AppA (apply_subst_substs s ss1, apply_subst_substs s ss2)
  | RecordUpdateA ss -> RecordUpdateA (apply_subst_substs s ss)
  | LambdaA (b1,b2) -> LambdaA (apply_subst_branches s b1, apply_subst_branches s b2)
  | ConstraintA ss -> ConstraintA (apply_subst_substs s ss)
  and apply_subst s t =
  if Subst.is_identity s then t
  else match t with
  | VarA -> VarA
  | DoA (a, ty, split) ->
    DoA (apply_subst_a s a, Option.map (apply_subst_simplify s) ty,
      apply_subst_split s split)
  | SkipA t -> SkipA (apply_subst s t)
  | DoSkipA (a, split, t) ->
    DoSkipA (apply_subst_a s a, apply_subst_split s split, apply_subst s t)

  let rec initial_a a =
    let open Msc in match a with
    | Alias _ | Abstract _ | Const _ | Pair _ | Let _ -> NoneA
    | Ite _ -> IteA []
    | Projection _ -> ProjA []
    | TypeConstr _ -> ConstraintA []
    | RecordUpdate _ -> RecordUpdateA []
    | App _ -> AppA ([], [])
    | Lambda (_, Parsing.Ast.Unnanoted, v, e) ->
      let initial_s = [(any, (false, initial_e e))] in
      let v = Variable.to_typevar v |> TVar.typ in
      LambdaA ([], [(v, initial_s)])
    | Lambda (_, Parsing.Ast.ADomain dts, _, e) ->
      let initial_s = [(any, (false, initial_e e))] in
      LambdaA ([], List.map (fun dt -> (dt, initial_s)) dts)
    | Lambda (_, Parsing.Ast.AArrow _, _, _) ->
      LambdaA ([],[]) (* Not supported *)

  and initial_e e =
      let open Msc in match e with
      | Var _ -> VarA
      | Bind (_, _, _, e) -> SkipA (initial_e e)
end
