open Cduce
open Nf_ast
open Types_additions
open Annotations
(*open Variable*)

exception Ill_typed of Position.t list * string

(*let all_possibilities lst =
  let rec aux acc lst =
    match lst with
    | [] -> [List.rev acc]
    | a::lst ->
      List.map (fun x -> aux (x::acc) lst) a
      |> List.flatten
  in
  aux [] lst

let rec remove_duplicates equiv lst =
  let remove elt lst = List.filter (equiv elt) lst in
  match lst with
  | [] -> []
  | e::lst -> e::(remove e lst |> remove_duplicates equiv)
*)


let rec typeof_a pos tenv env annots a =
  if Env.is_bottom env
  then raise (Ill_typed (pos, "Environment contains a divergent variable."))
  else begin match a with
  | Const (Atom str) -> get_type_or_atom tenv str
  | Const c -> Ast.const_to_typ c
  | Var v -> Env.find v env
  | Debug (_, v) -> Env.find v env
  | Pair (v1, v2) ->
    let t1 = Env.find v1 env in
    let t2 = Env.find v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (p, v) ->
    let t = Env.find v env in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Ill_typed (pos, "Projection can only be done on a pair."))
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    if subtype t1 arrow_any
    then
      let t2 = Env.find v2 env in
      let dom = domain t1 in
      if subtype t2 dom
      then
        let res = apply t1 t2 in
        if is_empty res
        then raise (Ill_typed (pos, "This application always diverges."))
        else res
      else raise (Ill_typed (pos, "Argument not in the domain of the function."))
    else raise (Ill_typed (pos, "Application can only be done on a function."))
  | Ite (v, t, x1, x2) ->
    let tv = Env.find v env in
    if subtype tv t
    then Env.find x1 env
    else if subtype tv (neg t)
    then Env.find x2 env
    else raise (Ill_typed (pos, "Cannot select a branch for the typecase."))
  | Lambda (Ast.ADomain s, v, e) ->
    let splits = Annotations.splits v env ~initial:s annots in
    (* The splits are guaranteed not to contain the empty type *)
    if disj splits |> subtype s
    then
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        let res = typeof tenv env annots e in
        mk_arrow (cons t) (cons res)
      ) |> conj |> simplify_arrow
    else raise (Ill_typed (pos, "Invalid split (does not cover the whole domain)."))
  | Lambda _ -> failwith "Not implemented"
  end

and typeof (*tenv env annots*) _ _ _ e =
  match e with
  (*| EVar v -> failwith "TODO"
  | Let (v, a, e) -> failwith "TODO"*)
  | _ -> failwith "TODO"

let refine_a _ ~backward _ env a t =
  begin match a with
  | Const c when backward ->
    if disjoint (Ast.const_to_typ c) t then [] else [Env.empty]
  | Const c ->
    if subtype (Ast.const_to_typ c) t then [Env.empty] else []
  | Var v -> [Env.singleton v t]
  | Debug (_, v) -> [Env.singleton v t]
  | Pair (v1, v2) ->
    split_pair t
    |> List.map (
      fun (t1, t2) ->
        let env1 = Env.singleton v1 t1 in
        let env2 = Env.singleton v2 t2 in
        Env.cap env1 env2
    )
  | Projection (Fst, v) -> [mk_times (cons t) any_node |> Env.singleton v]
  | Projection (Snd, v) -> [mk_times any_node (cons t) |> Env.singleton v]
  | Projection _ -> failwith "Not implemented"
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    (if backward then square_split t1 t else triangle_split t1 t)
    |> List.map (
      fun (t1, t2) ->
        let env1 = Env.singleton v1 t1 in
        let env2 = Env.singleton v2 t2 in
        Env.cap env1 env2
    )
  | Ite (v, s, x1, x2) ->
    let env1 = Env.singleton v s in
    let env2 = Env.singleton v (neg s) in
    let env1' = Env.singleton x1 t in
    let env2' = Env.singleton x2 t in
    [Env.cap env1 env1' ; Env.cap env2 env2']
  | Lambda (Ast.ADomain s, _, _) when backward ->
    if subtype (domain t) s then [Env.empty] else []
  | Lambda (Ast.ADomain _, _, _) -> []
  | Lambda _ -> failwith "Not implemented"
  end
  |> List.map (fun env' -> List.fold_left (fun acc v ->
    if Env.mem v env then Env.strengthen v (Env.find v env) acc else acc)
    env' (Env.domain env')) (* Inter *)
  |> List.filter (fun env -> Env.is_bottom env |> not) (* Normalize *)

let infer _ _ _ _ = failwith "TODO"
and infer_a _ _ _ _ _ = failwith "TODO"

let typeof_simple (*tenv env e*) _ _ _ = failwith "TODO"
