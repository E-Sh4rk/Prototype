open Types.Base
open Types.Additions
open Common
open Parsing.Variable

let partition = Annotations.partition
let regroup = Annotations.regroup

let remove_redundant_branches lst =
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
  lst |> List.map (fun (t,(b,a)) -> (t,(t,(b,a)))) |>
  (* (fun x -> Utils.log "remove_redundant_branches: %a@." (Utils.pp_list pp_typ) (List.map fst x) ; x) |> *)
  List.rev |> aux [] |> List.map snd

let remove_empty_branches lst =
  lst |> List.filter (fun (s,_) -> non_empty s)

module Refinements = Annotations.Refinements

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