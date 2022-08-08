open Types.Base
open Types.Additions
open Common.Msc
open Annotations
open Annot
open Common
open Parsing.Variable
open Utils

exception Untypeable of Position.t list * string

(* ===== TYPEOF ===== *)

let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable pos v =
  raise (Untypeable (pos, "Unbound variable "^(Variable.show v)^"."))
  
let var_type pos v env =
  if Env.mem v env then Env.find v env else unbound_variable pos v

let instantiate_check pos mono ss t =
  let check_s s =
    Subst.dom s |> TVarSet.inter mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instanciation: attempting to substitute a monomorphic variable."))  
  
let rec typeof_a pos tenv env mono annot_a a =
  let type_lambda env annot v e =
    if annot = []
    then raise (Untypeable (pos, "Invalid lambda: empty annotations."))
    else
      annot |> List.map (fun (s, annot) ->
        let env = Env.add v s env in
        let mono = TVarSet.union mono (vars s) in
        let t = typeof_splits tenv env mono v annot e in
        mk_arrow (cons s) (cons t)
      ) |> conj_o
  in
  begin match a, annot_a with
  | Abstract t, NoneA -> t
  | Const c, NoneA -> typeof_const_atom tenv c
  | Pair (v1, v2), NoneA ->
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v), ProjA ss ->
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      try get_field t label
      with Not_found ->
        raise (Untypeable (pos, "Invalid projection: missing label " ^ label ^ "."))
    else raise (Untypeable (pos, "Invalid projection: not a record."))
  | Projection (p, v), ProjA ss ->
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Untypeable (pos, "Invalid projection: not a pair."))
  | RecordUpdate (v, label, op), RecordUpdateA ss -> 
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      begin match op with
      | None -> remove_field t label
      | Some v' ->
        let t' = var_type pos v' env in
        let right_record = mk_record false [label, cons t'] in
        merge_records t right_record  
      end
    else raise (Untypeable (pos, "Invalid field update: not a record."))
  | App (v1, v2), AppA (ss1, ss2) ->
    let t1 = var_type pos v1 env |> instantiate_check pos mono ss1 in
    let t2 = var_type pos v2 env |> instantiate_check pos mono ss2 in
    if subtype t1 arrow_any
    then
      if subtype t2 (domain t1)
      then apply t1 t2
      else raise (Untypeable (pos, "Invalid application: argument not in the domain."))
    else raise (Untypeable (pos, "Invalid application: not a function."))
  | Ite (v, s, v1, v2), IteA ss ->
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t empty
    then empty
    else if subtype t s
    then var_type pos v1 env
    else if subtype t (neg s)
    then var_type pos v2 env
    else raise (Untypeable (pos, "Invalid typecase: multiple branches possible."))
  | Let (v1, v2), NoneA ->
    if Env.mem v1 env
    then var_type pos v2 env
    else raise (Untypeable (pos, "Invalid let binding: definition has been skipped."))
  | Lambda (_, Parsing.Ast.Unnanoted, v, e), LambdaA annot ->
    type_lambda env annot v e
  | Lambda (_, Parsing.Ast.ADomain dt, v, e), LambdaA annot ->
    let t = type_lambda env annot v e in
    if equiv (domain t) dt
    then t
    else raise (Untypeable (pos, "Invalid lambda: domain does not match with user annotation."))
  | Lambda (_, Parsing.Ast.AArrow t, v, e), LambdaA annot ->
    let t' = type_lambda env annot v e in
    if subtype t' t
    then t
    else raise (Untypeable (pos, "Invalid lambda: type does not match with user annotation."))
  | _, _ -> raise (Untypeable (pos, "Invalid annotations."))
  end
  |> clean_type ~pos:empty ~neg:any mono |> simplify_typ

and typeof_splits tenv env mono v splits e =
  let pos = Variable.get_locations v in
  let dom = splits |> List.map fst |> disj in
  if subtype (Env.find v env) dom
  then splits |> List.map (fun (s, annot) ->
    let env = Env.strengthen v s env in
    let mono = TVarSet.union mono (vars s) in
    typeof tenv env mono annot e
  ) |> disj_o
  else raise (Untypeable (pos, "Invalid split: does not cover the whole domain."))

and typeof tenv env mono annot e =
  begin match e, annot with
  | Var v, VarA -> var_type (Variable.get_locations v) v env
  | Bind (_, v, a, e), EmptyA (annot_a, annot) ->
    let t = typeof_a (Variable.get_locations v) tenv env mono annot_a a in
    let env = Env.add v t env in
    if subtype t empty
    then typeof tenv env mono annot e
    else raise (Untypeable ([], "Invalid binding: does not cover the whole domain."))
  | Bind (_, v, a, e), DoA (_, annot_a, annot_split) ->
    let t = typeof_a (Variable.get_locations v) tenv env mono annot_a a in
    let env = Env.add v t env in
    typeof_splits tenv env mono v annot_split e
  | Bind (_, _, _, e), SkipA (annot) -> typeof tenv env mono annot e
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> clean_type ~pos:empty ~neg:any mono |> simplify_typ

(* ===== REFINE ===== *)

let refine_a env mono a t = (* empty possibilites are often omitted *)
  match a with
  | Abstract _ | Const _ | Lambda _ -> []
  | Pair (v1, v2) ->
    split_pair t
    |> List.map (
      fun (t1, t2) -> Env.construct [(v1,t1) ; (v2, t2)]
    )
  | Projection (Fst, v) -> [Env.singleton v (mk_times (cons t) any_node)]
  | Projection (Snd, v) -> [Env.singleton v (mk_times any_node (cons t))]
  | Projection (Field label, v) ->
    [Env.singleton v (mk_record true [(label, cons t)])]
  | RecordUpdate (v, label, None) ->
    let t = cap t (record_any_without label) in
    split_record t
    |> List.map (
      fun ti -> Env.singleton v (remove_field_info ti label)
    )
  | RecordUpdate (v, label, Some x) ->
    let t = cap t (record_any_with label) in
    split_record t
    |> List.map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        Env.construct [(v, ti) ; (x, field_type)]
      )
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    triangle_poly mono t1 t
    |> List.map (fun ti -> Env.singleton v2 ti)
  | Ite (v, s, v1, v2) ->
    [Env.construct [(v,s);(v1,t)] ; Env.construct [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ===== INFER ===== *)

type 'a result =
  | Ok of 'a
  | Split of (Env.t * 'a) list
  | Subst of (Subst.t * 'a) list

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Split lst ->
    Split (lst |> List.map (fun (e,a) -> (e, f a)))
  | Subst lst ->
    Subst (lst |> List.map (fun (s,a) -> (s, f a)))

let rec infer_a' pos tenv env mono noninferred annot_a a =
  ignore (infer_a', pos, tenv, env, mono, noninferred, annot_a, a) ;
  failwith "TODO"

and infer_splits' tenv env mono noninferred v splits e =
  let t = Env.find v env in
  let splits = splits |> List.filter (fun (s, _) -> disjoint s t |> not) in
  let rec aux splits =
    match splits with
    | [] -> Ok []
    | (s, annot)::splits ->
      begin match aux splits with
      | Ok (splits) ->
        let env = Env.strengthen v s env in
        let vs = vars s in
        let noninferred = TVarSet.union noninferred (TVarSet.diff vs mono) in
        let mono = TVarSet.union mono vs in
        begin match infer_iterated tenv env mono noninferred annot e with
        | Split _ -> failwith "TODO"
        | res -> map_res (fun annot -> (s,annot)::splits) res
        end
      | res -> map_res (fun splits -> (s, annot)::splits) res
      end
  in
  aux splits

and infer' tenv env mono noninferred annot e =
  ignore (refine_a, infer_a', tenv, env, mono, noninferred, annot, e) ;
  failwith "TODO"

and infer_a_iterated pos tenv env mono noninferred annot_a a =
  match infer_a' pos tenv env mono noninferred annot_a a with
  | Split [(env', annot_a)] when Env.leq env env' ->
    infer_a_iterated pos tenv env mono noninferred annot_a a
  | Subst [(subst, annot_a)] when Subst.is_identity subst ->
    infer_a_iterated pos tenv env mono noninferred annot_a a
  | res -> res

and infer_iterated tenv env mono noninferred annot e =
  match infer' tenv env mono noninferred annot e, e with
  | Split [(env', annot)], _ when Env.leq env env' ->
    infer_iterated tenv env mono noninferred annot e
  | Subst [(subst, annot)], _ when Subst.is_identity subst ->
    infer_iterated tenv env mono noninferred annot e
  | Split r, Bind (_, _, a, _) ->
    map_res (fun annot -> Annot.retype a annot) (Split r)
  | res, _ -> res

let infer tenv env mono e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind ((), v, Abstract (var_type [] v env), acc)
  ) fv e in
  let annot =
    match infer_iterated tenv Env.empty mono mono (Annot.initial_e e) e with
    | Subst [] -> raise (Untypeable ([], "Annotations inference failed."))
    | Ok annot -> (e, annot)
    | _ -> assert false
  in
  log "@." ; annot

let typeof_simple tenv env mono e =
  let (e, anns) = infer tenv env mono e in
  typeof tenv Env.empty mono anns e  
