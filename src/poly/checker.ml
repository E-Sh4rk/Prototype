open Types.Base
open Types.Tvar
open Types.Additions
open Common
open Parsing.Variable

exception Untypeable of Position.t list * string

let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_atom_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable v =
  raise (Untypeable (Variable.get_locations v, "Unbound variable "^(Variable.show v)^"."))
  
let var_type v env =
  if Env.mem v env then Env.find v env else unbound_variable v

let instantiate_check pos ss t =
  let check_s s =
    Subst.dom s |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instantiation: attempting to substitute a monomorphic variable."))

let check_mono pos t =
  if is_mono_typ t
  then ()
  else raise (Untypeable (pos, "Invalid lambda branch: abstracted variable should be monomorphic."))

let rec typeof_a vardef tenv env annot_a a =
  let pos = Variable.get_locations vardef in
  let type_lambda env annot v e =
    if annot = []
    then raise (Untypeable (pos, "Invalid lambda: there must be at least 1 branch."))
    else
      annot |> List.map (fun (s, annot) ->
        check_mono pos s ;
        let env = Env.add v s env in
        let t = typeof tenv env annot e in
        mk_arrow (cons s) (cons t)
      ) |> conj_o
  in (* TODO *)
  ignore (type_lambda, env, annot_a, a, instantiate_check,
  typeof_const_atom, var_type) ;
  (*begin match a, annot_a with
  | Alias v, NoneA -> var_type v env
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
  | Lambda (_, Parsing.Ast.AArrow _, _, _), LambdaA _ ->
    raise (Untypeable (pos, "Invalid lambda: explicitely typed lambdas not supported."))
  | Lambda (_, _, v, e), LambdaA (annot, _) -> type_lambda env annot v e
  | _, _ -> raise (Untypeable (pos, "Invalid annotations."))
  end
  |> RawExt.clean_poly_vars mono |> simplify_typ*)
  failwith "TODO"
  
and typeof _ = ignore typeof_a ; failwith "TODO"

let infer _ = failwith "TODO"

let typeof_simple _ = failwith "TODO"
