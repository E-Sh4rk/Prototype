open Cduce
open Variable
open Nf_ast
open Types_additions

module Env = struct
  type t = typ VarMap.t * VarSet.t (* bottom vars *)
  let empty = (VarMap.empty, VarSet.empty)
  let is_bottom (_, bvs) = VarSet.is_empty bvs |> not
  let add v t (env, bvs) =
    let bvs =
      if is_empty t
      then VarSet.add v bvs
      else VarSet.remove v bvs
    in
    (VarMap.add v t env, bvs)
  let find v (env, _) = VarMap.find v env
end

exception Ill_typed of Position.t list * string

let rec typeof_a pos tenv env a =
  if Env.is_bottom env
  then empty
  else match a with 
  (* Var & const *)
  | Const (Atom str) -> get_type_or_atom tenv str
  | Const c -> Ast.const_to_typ c
  | Var v -> Env.find v env
  | Debug (str, v) ->
    let res = Env.find v env in
    Format.printf "%s (typeof): " str ; Utils.print_type res ;
    res
  (* Projections & Pairs *)
  | Projection (Fst, v) ->
    let t = Env.find v env in
    if subtype t pair_any then pi1 t
    else raise (Ill_typed (pos, "Fst can only be applied to a pair."))
  | Projection (Snd, v) ->
    let t = Env.find v env in
    if subtype t pair_any then pi2 t
    else raise (Ill_typed (pos, "Snd can only be applied to a pair."))
  | Projection (Field str, v) ->
    let t = Env.find v env in
    if subtype t record_any
    then
      try get_field t str
      with Not_found ->
      raise (Ill_typed (pos, Printf.sprintf "The record does not surely contains the field %s." str))
    else raise (Ill_typed (pos, "Field projection can only be applied to a record."))
  | Pair (x1, x2) ->
    let t1 = Env.find x1 env in
    let t2 = Env.find x2 env in
    mk_times (cons t1) (cons t2)
  | RecordUpdate (x1, str, x2) ->
    let t1 = Env.find x1 env in
    if subtype t1 record_any
    then begin
      match x2 with
      | None -> remove_field t1 str
      | Some x2 ->
        let t2 = Env.find x2 env in
        let t' = mk_record false [str, cons t2] in
        merge_records t1 t'
    end else raise (Ill_typed (pos, "Field assignation can only be applied to a record."))
  (* App & Case *)
  | App (x1, x2) ->
    let t1 = Env.find x1 env in
    let t2 = Env.find x2 env in
    let dom_t1 = domain t1 in
    if subtype t2 dom_t1
    then apply t1 t2
    else
      let error = Printf.sprintf
        "Bad domain for the application: expected %s - found: %s" 
        (string_of_type dom_t1) (string_of_type t2) in
      raise (Ill_typed (pos, error))
  | Ite (v,t,e1,e2) ->
    let vt = Env.find v env in
    let env1 = Env.add v (cap vt t) env in
    let env2 = Env.add v (cap vt (neg t)) env in
    (* TODO: some marking in order to detect unreachable code *)
    (*let logs1 = get_logs_expr e1 in
    let logs2 = get_logs_expr e2 in
    let bottom_1 = is_bottom env1 in
    let t1 = if bottom_1
    then (set_logs e1 {logs1 with ignored=logs1.ignored+1} ; empty)
    else (set_logs e1 {logs1 with visited=logs1.visited+1} ; self (env1, e1)) in
    let t2 = if is_bottom env2
      then
        (* Remove false to experiment with failure instead of empty *)
        if false && bottom_1 then raise (Ill_typed (pos, "No branch can be selected"))
        else (set_logs e2 {logs2 with ignored=logs2.ignored+1} ; empty)
      else (set_logs e2 {logs2 with visited=logs2.visited+1} ; self (env2, e2)) in*)
    let t1 = typeof tenv env1 e1 in
    let t2 = typeof tenv env2 e2 in
    cup t1 t2
  (* Abstractions *)
  | Lambda (Ast.ADomain s, x, e) ->
    let refine_env_cont env t = [t, env] in
    split_and_refine tenv env e x s refine_env_cont
    |> List.map (fun (s, env) -> mk_arrow (cons s) (cons (typeof tenv env e)))
    |> conj
  | Lambda _ -> failwith "Only abstractions with typed domain are supported for now."

and typeof tenv env e =
  if Env.is_bottom env
  then empty
  else match e with 
  | Atomic a -> typeof_a [] tenv env a
  (* Let bindings *)
  | Let (x, a, e) ->
    let s = typeof_a (Variable.get_locations x) tenv env a in
    let refine_env_cont env t = refine_a ~backward:true tenv env a t in
    split_and_refine tenv env e x s refine_env_cont
    |> List.map (fun (_, env) -> typeof tenv env e)
    |> disj

and split_and_refine tenv env e x initial_t refine_env_cont =
  let rec aux env t =
    let envs = refine_env_cont env t in
    let treat_env (t, env) =
      let env = Env.add x t env in
      match candidates_partition tenv env e x t with
      | [] -> assert false
      | [t] -> [t, env]
      | lst ->
        List.map (aux env) lst
        |> List.flatten
    in
    List.map treat_env envs
    |> List.flatten
  in
  aux env initial_t

and candidates_partition tenv env e x t =
  let ts =
    candidates tenv env e x
    |> List.map (cap t)
  in
  let aux (u, ts) t =
    (cup u t, (diff t u)::ts)
  in
  let (u, ts) = List.fold_left aux (empty, []) ts in
  let ts = (diff t u)::ts in
  List.filter non_empty ts

and candidates_a (*tenv env a x*) _ _ _ _ =
  failwith "TODO"

and candidates (*tenv env e x*) _ _ _ _ =
  failwith "TODO"

and res_non_empty (t, _) = non_empty t
and filter_res lst = List.filter res_non_empty lst

and refine_a ~backward tenv env a t =
  let t = cap t (typeof_a [] tenv env a) in
  begin match a with
  (* Var & const *)
  | Const _ -> [t, env]
  | Var v -> [t, Env.add v t env]
  | Debug (_, v) -> [t, Env.add v t env]
  (* Projections & Pairs *)
  | Projection (Fst, v) ->
    let tv = Env.find v env in
    [t, Env.add v (cap tv (mk_times (cons t) any_node)) env]
  | Projection (Snd, v) ->
    let tv = Env.find v env in
    [t, Env.add v (cap tv (mk_times any_node (cons t))) env]
  | Projection (Field str, v) ->
    let tv = Env.find v env in
    [t, Env.add v (cap tv (mk_record true [str, cons t])) env]
  | Pair (x1, x2) ->
    split_pair t
    |> List.map (
      fun (t1, t2) ->
        let env =
          if Variable.equals x1 x2
          then Env.add x1 (cap t1 t2) env
          else Env.add x1 t1 (Env.add x2 t2 env)
        in
        (mk_times (cons t1) (cons t2), env)
    )
  | RecordUpdate (*(x1, str, x2)*) _ ->
    failwith "Refinement of records not implemented yet."
  (* App & Case *)
  | App (x1, x2) ->
    let t1 = Env.find x1 env in
    let t2 = Env.find x2 env in
    (if backward then square t1 t else triangle t1 t)
    |> List.map (
      fun (t1', t2') ->
        let t1 = cap t1 t1' in
        let t2 = cap t2 t2' in
        let env =
          if Variable.equals x1 x2
          then Env.add x1 (cap t1 t2) env
          else Env.add x1 t1 (Env.add x2 t2 env)
        in
        (apply t1 t2, env)
    )
  | Ite (v,t,e1,e2) ->
    let vt = Env.find v env in
    let env1 = Env.add v (cap vt t) env in
    let env2 = Env.add v (cap vt (neg t)) env in
    (refine ~backward tenv env1 e1 t)@(refine ~backward tenv env2 e2 t)
  (* Abstractions *)
  | Lambda (Ast.ADomain s, x, e) ->
    let dom = domain t in
    if subtype dom s then
      let refine_env_cont env t = [t, env] in
      split_and_refine tenv env e x dom refine_env_cont
      |> List.map (fun (s, env) -> refine ~backward tenv env e (apply t s))
      |> List.flatten
    else []
  | Lambda _ -> failwith "Only abstractions with typed domain are supported for now."
  end
  |> filter_res

and refine ~backward tenv env e t =
  (*let t = cap t (typeof tenv env e) in*) (* NOTE: Only needed in refine_a. *)
  begin match e with 
  | Atomic a -> refine_a ~backward tenv env a t
  (* Let bindings *)
  | Let (x, a, e) ->
    let s = typeof_a (Variable.get_locations x) tenv env a in
    let refine_env_cont env t = refine_a ~backward:true tenv env a t in
    split_and_refine tenv env e x s refine_env_cont
    |> List.map (fun (_, env) -> refine ~backward tenv env e t)
    |> List.flatten
  end
  (*|> filter_res*) (* NOTE: Only needed in refine_a. *)
