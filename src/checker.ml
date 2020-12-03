open Cduce
open Nf_ast
open Types_additions
open Variable

exception Ill_typed of Position.t list * string

type typ_tree =
  | TNode of Env.t * (Env.t list * typ_tree) list
  | TLeaf of Env.t * typ

let rec leaves tree = match tree with
  | TLeaf (env, t) -> [(env, t)]
  | TNode (_, lst) ->
    List.map (fun (_, tree) -> leaves tree) lst
    |> List.flatten

let rec map_tree fn fl tree =
  match tree with
  | TNode (env, children) ->
    let children = children
    |> List.map (fun (labels, child) -> (labels, map_tree fn fl child))
    in fn env children
  | TLeaf (env, t) -> fl env t


type context = e

let empty_context = Hole

let fill_context ctx e =
  map_e (function Hole -> e | e -> e) (fun a -> a) ctx


let bound_vars =
  fold_e
  (fun e acc -> let acc = List.fold_left VarSet.union VarSet.empty acc in
    match e with Let (v, _, _) -> VarSet.add v acc | _ -> acc)
  (fun a acc -> let acc = List.fold_left VarSet.union VarSet.empty acc in
    match a with Lambda (_, v, _) -> VarSet.add v acc | _ -> acc)


let transfer_unbounded_vars e env env' =
  let bv = bound_vars e in
  let rec aux env env' vs =
    match vs with
    | [] -> (env, env')
    | v::vs when VarSet.mem v bv -> aux env env' vs
    | v::vs -> aux (Env.strengthen v (Env.find v env') env) (Env.rm v env') vs
  in
  try aux env env' (Env.domain env')
  with Env.EnvIsBottom -> (Env.bottom, Env.bottom)

let rec typeof_a (*pos tenv env env' ctx a*) _ _ _ _ _ _ =
  failwith "Not implemented"

and typeof tenv env env' ctx e =
  let (env, env') = transfer_unbounded_vars e env env' in
  if Env.is_bottom env then
    TLeaf (env, empty)
  else begin
    match e with
    | Hole -> assert false
    | EVar v -> typeof_a [] tenv env env' ctx (Var v)
    | Let (v, a, e) when not (Env.mem v env) -> (* LetFirst *)
      let pos = Variable.get_locations v in
      typeof_a pos tenv env env' ctx a
      |> map_tree
      (fun env children ->
        let env_nov = Env.rm v env in
        (* Shouldn't raise Env.EnvIsBottom because nodes env shouldn't be empty
        (otherwise it would be a leaf) *)
        let children = children
        |> List.map (fun (labels, child) ->
          let labels = labels
          |> List.map (fun label ->
            let label_nov = Env.rm v label in
            (* Shouldn't raise Env.EnvIsBottom because labels shouldn't be empty *)
            begin
              if Env.mem v label
              then refine_a [] ~backward:false tenv
                  (Env.cap env_nov label_nov) a (Env.find v label) 
              else [Env.empty]
            end
            |> List.map (Env.cap label_nov)
          )
          |> List.flatten in
          (labels, child)
        ) in
        TNode (env, children)
      )
      (fun env t ->
        typeof tenv (Env.add v t env) env' ctx (Let (v, a, e))
      )
    | Let (v, a, e) ->
      let pos = Variable.get_locations v in
      begin match typeof_a pos tenv env env' ctx a with
      | TNode _ -> assert false
      | TLeaf (_, t) ->
        let env = Env.strengthen v t env in
        if not (Env.mem v env') || subtype (Env.find v env) (Env.find v env')
        then (* LetNoRefine *)
          let ctx = fill_context ctx (Let (v, a, Hole)) in
          typeof tenv env (Env.rm v env') ctx e
        else (* LetRefine *)
          let t' = Env.find v env' in
          let env_nov' = Env.rm v env' in
          let trees =
            let envs'' = refine_a [] ~backward:true tenv env a t' in
            let env = Env.strengthen v t' env in
            envs'' |> List.map (fun env'' ->
              let env' = Env.cap env_nov' env'' in
              typeof tenv env env' Hole (fill_context ctx (Let (v, a, e)))
            )
          in
          TNode (env, List.map (fun tree -> ([], tree)) trees)
      end
  end

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

and refine ~backward tenv env e t =
  if Env.is_bottom env then []
  else begin
    match e with
    | Hole -> assert false
    | EVar v -> refine_a [] ~backward tenv env (Var v) t
    | Let (v, a, e) ->
      let rm_v = if backward then (fun env -> env) else (fun env -> Env.rm v env) in
      let env_nov = rm_v env in (* Shouldn't raise Env.EnvIsBottom because emptiness is checked before *)
      refine ~backward tenv env e t
      |> List.map (fun env' ->
        if Env.mem v env'
        then
          let env_nov' = rm_v env' in (* Shouldn't raise Env.EnvIsBottom because refine only return non-empty envs *)
          refine_a [] ~backward tenv (Env.cap env_nov env_nov') a (Env.find v env')
          |> List.map (Env.cap env_nov')
        else [env']
      )
      |> List.flatten
      |> (fun envs -> (if backward then [] else 
        refine_a [] ~backward tenv env_nov a empty
        )@envs)
  end
  |> List.filter (fun env -> Env.is_bottom env |> not)

let typeof_simple tenv env e =
  leaves (typeof tenv env Env.empty empty_context e)
  |> List.map snd
  |> disj
