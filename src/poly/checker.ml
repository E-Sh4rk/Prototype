open Types.Base
open Types.Additions
open Common.Msc
open Annotations
open Annot
open Common
open Parsing.Variable

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
        typeof_splits tenv env mono v annot e
        |> List.map (fun (s,t) -> mk_arrow (cons s) (cons t))
        |> conj_o
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
    (Env.find v env, typeof tenv env mono annot e)
  )
  else raise (Untypeable (pos, "Invalid split: does not cover the whole domain."))

and typeof tenv env mono annot e =
  ignore (tenv, env, mono, annot, e, typeof) ;
  failwith "TODO"
