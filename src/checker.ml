open Cduce
open Nf_ast
open Types_additions
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


let typeof_a (*pos tenv env env'*) _ _ _ _ a =
  match a with
  (*| Const (Atom str) -> failwith "TODO"
  | Const c -> failwith "TODO"
  | Var v -> failwith "TODO"
  | Debug (_, v) -> failwith "TODO"
  | Pair (v1, v2) -> failwith "TODO"
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (p, v) -> failwith "TODO"
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) -> failwith "TODO"
  | Ite (v, t, x1, x2) -> failwith "TODO"
  | Lambda (Ast.ADomain s, v, e) -> failwith "TODO"
  | Lambda _ -> failwith "Not implemented"*)
  | _ -> failwith "TODO"

and typeof (*tenv env env'*) _ _ _ e =
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
