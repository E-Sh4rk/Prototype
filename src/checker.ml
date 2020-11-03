open Cduce
open Variable
open Nf_ast
open Types_additions

type env = typ VarMap.t
let empty_env = VarMap.empty

let is_bottom env =
    let is_bottom (_,t) = is_empty t in
    List.exists is_bottom (VarMap.bindings env)

let add_to_env v t env = VarMap.add v t env

exception Ill_typed of Position.t list * string

let rec typeof tenv env e =
  let rec aux_a pos env a =
    (* NOTE: I think we do not need to test EFQ here...
       doing it in aux_e should be enough. *)
    match a with
    (* Var & const *)
    | Const (Atom str) -> get_type_or_atom tenv str
    | Const c -> Ast.const_to_typ c
    | Var v -> VarMap.find v env
    | Debug (str, v) ->
      let res = VarMap.find v env in
      Format.printf "%s (typeof): " str ; Utils.print_type res ;
      res
    (* Projections & Pairs *)
    | Projection (Fst, v) ->
      let t = VarMap.find v env in
      if subtype t pair_any then pi1 t
      else raise (Ill_typed (pos, "Fst can only be applied to a pair."))
    | Projection (Snd, v) ->
      let t = VarMap.find v env in
      if subtype t pair_any then pi2 t
      else raise (Ill_typed (pos, "Snd can only be applied to a pair."))
    | Projection (Field str, v) ->
      let t = VarMap.find v env in
      if subtype t record_any
      then
        try get_field t str
        with Not_found ->
        raise (Ill_typed (pos, Printf.sprintf "The record does not surely contains the field %s." str))
      else raise (Ill_typed (pos, "Field projection can only be applied to a record."))
    | Pair (x1, x2) ->
      let t1 = VarMap.find x1 env in
      let t2 = VarMap.find x2 env in
      mk_times (cons t1) (cons t2)
    | RecordUpdate (x1, str, x2) ->
      let t1 = VarMap.find x1 env in
      if subtype t1 record_any
      then begin
        match x2 with
        | None -> remove_field t1 str
        | Some x2 ->
          let t2 = VarMap.find x2 env in
          let t' = mk_record false [str, cons t2] in
          merge_records t1 t'
      end else raise (Ill_typed (pos, "Field assignation can only be applied to a record."))
    (* App & Case *)
    | App (x1, x2) ->
      let t1 = VarMap.find x1 env in
      let t2 = VarMap.find x2 env in
      let dom_t1 = domain t1 in
      if subtype t2 dom_t1
      then apply t1 t2
      else
        let error = Printf.sprintf
          "Bad domain for the application: expected %s - found: %s" 
          (string_of_type dom_t1) (string_of_type t2) in
        raise (Ill_typed (pos, error))
    | Ite (v,t,e1,e2) ->
      let vt = VarMap.find v env in
      let env1 = VarMap.add v (cap vt t) env in
      let env2 = VarMap.add v (cap vt (neg t)) env in
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
      let t1 = aux_e pos env1 e1 in
      let t2 = aux_e pos env2 e2 in
      cup t1 t2
    (* Abstractions *)
    | Lambda (Ast.ADomain s, x, e) ->
      let refine_env_cont env t = [t, env] in
      split_and_refine tenv env e x s refine_env_cont
      |> List.map (fun (t, env) -> mk_arrow (cons t) (cons (aux_e pos env e)))
      |> conj
    | Lambda _ -> failwith "Only abstractions with typed domain are supported for now."
  and aux_e pos env e =
    if is_bottom env
    then empty
    else match e with 
    | Atomic a -> aux_a pos env a
    (* Let bindings *)
    | Let (x, a, e) ->
      let s = aux_a (Variable.get_locations x) env a in
      let refine_env_cont env t = refine ~backward:true tenv env (Atomic a) t in
      split_and_refine tenv env e x s refine_env_cont
      |> List.map (fun (_, env) -> aux_e pos env e)
      |> disj
  in
  aux_e [] env e

and split_and_refine tenv env e x initial_t refine_env_cont =
  let rec aux env t =
    let envs = refine_env_cont env t in
    let treat_env (t, env) =
      let env = VarMap.add x t env in
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

and candidates (*tenv env e x*) _ _ _ _ =
  failwith "TODO"

and refine ~backward tenv env e t =
  let res_non_empty (t, _) = non_empty t in
  let filter_res lst = List.filter res_non_empty lst in
  let rec aux_a env a t =
    let t = cap t (typeof tenv env (Atomic a)) in
    begin match a with
    (* Var & const *)
    | Const c -> [t, env]
    | Var v -> [t, VarMap.add v t env]
    | Debug (str, v) -> [t, VarMap.add v t env]
    (* Projections & Pairs *)
    | Projection (Fst, v) ->
      let tv = VarMap.find v env in
      [t, VarMap.add v (cap tv (mk_times (cons t) any_node)) env]
    | Projection (Snd, v) ->
      let tv = VarMap.find v env in
      [t, VarMap.add v (cap tv (mk_times any_node (cons t))) env]
    | Projection (Field str, v) ->
      let tv = VarMap.find v env in
      [t, VarMap.add v (cap tv (mk_record true [str, cons t])) env]
    | Pair (x1, x2) ->
      split_pair t
      |> List.map (
        fun (t1, t2) ->
          let env =
            if Variable.equals x1 x2
            then VarMap.add x1 (cap t1 t2) env
            else VarMap.add x1 t1 (VarMap.add x2 t2 env)
          in
          [mk_times (cons t1) (cons t2), env]
      )
    | RecordUpdate (x1, str, x2) ->
      failwith "Refinement of records not implemented yet."
    (* App & Case *)
    | App (x1, x2) ->
      
    | Ite (v,t,e1,e2) ->

    (* Abstractions *)
    | Lambda (Ast.ADomain s, x, e) ->

    | Lambda _ -> failwith "Only abstractions with typed domain are supported for now."
    end
    |> filter_res
  and aux_e env e t =
    (* NOTE: I think we do not need to filter_res (EFQ)
       and intersect with typeof here... doing it in aux_a should be enough. *)
    match e with 
    | Atomic a -> aux_a env a t
    (* Let bindings *)
    | Let (x, a, e) ->
      let s = typeof tenv env (Atomic a) in
      let refine_env_cont env t = refine ~backward:true tenv env (Atomic a) t in
      split_and_refine tenv env e x s refine_env_cont
      |> List.map (fun (_, env) -> aux_e env e t)
      |> List.flatten
  in
  ignore backward ; (* TODO: remove *)
  aux_e env e t
