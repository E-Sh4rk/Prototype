module PMsc = Msc
open Types.Base
open Types.Additions
open Common.Msc
open Annotations
open Annot
open Common
open Parsing.Variable
(* open Utils *)

exception Untypeable of Position.t list * string

(* ===== TYPEOF ===== *)
let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable v =
  raise (Untypeable (Variable.get_locations v, "Unbound variable "^(Variable.show v)^"."))
  
let var_type v env =
  if Env.mem v env then Env.find v env else unbound_variable v

let instantiate_check pos mono ss t =
  let check_s s =
    Subst.dom s |> TVarSet.inter mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instanciation: attempting to substitute a monomorphic variable."))

let rec typeof_a vardef tenv env mono annot_a a =
  let pos = Variable.get_locations vardef in
  let type_lambda env annot v e =
    if annot = []
    then raise (Untypeable (pos, "Invalid lambda: there must be at least 1 branch."))
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
    let t1 = var_type v1 env in
    let t2 = var_type v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v), ProjA ss ->
    let t = var_type v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      try get_field t label
      with Not_found ->
        raise (Untypeable (pos, "Invalid projection: missing label " ^ label ^ "."))
    else raise (Untypeable (pos, "Invalid projection: not a record."))
  | Projection (p, v), ProjA ss ->
    let t = var_type v env |> instantiate_check pos mono ss in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Untypeable (pos, "Invalid projection: not a pair."))
  | RecordUpdate (v, label, op), RecordUpdateA ss -> 
    let t = var_type v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      begin match op with
      | None -> remove_field t label
      | Some v' ->
        let t' = var_type v' env in
        let right_record = mk_record false [label, cons t'] in
        merge_records t right_record  
      end
    else raise (Untypeable (pos, "Invalid field update: not a record."))
  | App (v1, v2), AppA (ss1, ss2) ->
    let t1 = var_type v1 env |> instantiate_check pos mono ss1 in
    let t2 = var_type v2 env |> instantiate_check pos mono ss2 in
    if subtype t1 arrow_any
    then
      if subtype t2 (domain t1)
      then apply t1 t2
      else raise (Untypeable (pos, "Invalid application: argument not in the domain."))
    else raise (Untypeable (pos, "Invalid application: not a function."))
  | Ite (v, s, v1, v2), IteA ss ->
    let t = var_type v env |> instantiate_check pos mono ss in
    if is_empty t
    then empty
    else if subtype t s
    then var_type v1 env
    else if subtype t (neg s)
    then var_type v2 env
    else raise (Untypeable (pos, "Invalid typecase: multiple branches possible."))
  | Let (v1, v2), NoneA ->
    if Env.mem v1 env
    then var_type v2 env
    else raise (Untypeable (pos, "Invalid let binding: definition has been skipped."))
  | Lambda (_, Parsing.Ast.AArrow t, v, e), LambdaA (annot, _) ->
    let t' = type_lambda env annot v e in
    if subtype t' t
    then t
    else raise (Untypeable (pos, "Invalid lambda: type does not match with user annotation."))  
  | Lambda (_, _, v, e), LambdaA (annot, _) -> type_lambda env annot v e
  | _, _ -> raise (Untypeable (pos, "Invalid annotations."))
  end
  |> hard_clean mono |> simplify_typ

and typeof_splits tenv env mono v splits e =
  let pos = Variable.get_locations v in
  if splits = []
  then raise (Untypeable (pos, "Invalid decomposition: cannot be empty."))
  else
    let dom = splits |> List.map fst |> disj in
    if subtype (Env.find v env) dom
    then splits |> List.map (fun (s, (_, annot)) ->
      let env = Env.strengthen v s env in
      let mono = TVarSet.union mono (vars s) in
      typeof tenv env mono annot e
    ) |> disj_o
    else raise (Untypeable (pos, "Invalid decomposition: does not cover the whole domain."))

and typeof tenv env mono annot e =
  begin match e, annot with
  | Var v, VarA -> var_type v env
  | Bind (_, v, a, e), DoA (annot_a, annot_split) ->
    let t = typeof_a v tenv env mono annot_a a in
    let env = Env.add v t env in
    typeof_splits tenv env mono v annot_split e
  | Bind (_, _, _, e), SkipA (annot) -> typeof tenv env mono annot e
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> hard_clean mono |> simplify_typ

(* ===== REFINE ===== *)

(* ===== INFER ===== *)

let infer _ = failwith "TODO"

let typeof_simple _ = failwith "TODO"
