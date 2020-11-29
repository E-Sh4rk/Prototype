open Cduce
open Nf_ast
open Types_additions

exception Ill_typed of Position.t list * string

type typ_tree =
  | TNode of Env.t * (Env.t list * typ_tree) list
  | TLeaf of Env.t * typ

let rec leaves tree = match tree with
  | TLeaf (env, t) -> [(env, t)]
  | TNode (_, lst) ->
    List.map (fun (_, tree) -> leaves tree) lst
    |> List.flatten


type context = TODO

let empty_context = TODO


let rec typeof_a (*pos tenv env env' ctx a*) _ _ _ _ _ _ =
  failwith "Not implemented"

and typeof (*tenv env env' ctx e *) _ _ _ _ _ =
  failwith "Not implemented"

and refine_a pos ~backward tenv env a t =
  if Env.is_bottom env then []
  else begin
    match a with
    | Const c when backward ->
      if  disjoint (Ast.const_to_typ c) t then [] else [Env.empty]
    | Const c ->
      if  subtype (Ast.const_to_typ c) t then [Env.empty] else []
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
    | Ite (v, s, e1, e2) ->
      let env1 = Env.singleton v s in
      let env2 = Env.singleton v (neg s) in
      let res1 = refine ~backward tenv (Env.cap env env1) e1 t in
      let res2 = refine ~backward tenv (Env.cap env env2) e2 t in
      (List.map (fun env -> Env.cap env env1) res1)@
      (List.map (fun env -> Env.cap env env2) res2)
    | Lambda (Ast.ADomain s, _, _) when backward ->
      if subtype (domain t) s then [Env.empty] else []
    | Lambda (Ast.ADomain _, _, _) ->
      leaves (typeof_a pos tenv env Env.empty empty_context a)
      |> List.filter (fun (_, t') -> subtype t' t)
      |> List.map fst
    | Lambda _ -> failwith "Not implemented"
  end
  |> List.filter (fun env -> Env.is_bottom env |> not)

and refine (*~backward tenv env e t*) ~backward _ _ _ _ =
  ignore backward ;
  failwith "Not implemented"


let typeof_simple tenv env e =
  leaves (typeof tenv env Env.empty empty_context e)
  |> List.map snd
  |> disj
