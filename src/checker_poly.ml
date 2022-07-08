open Cduce
open Msc
open Types_additions
open Variable
open Annotations

exception Ill_typed of Position.t list * string

(* ===== Auxiliary functions ===== *)

let pp_splits = Utils.pp_list Cduce.pp_typ

let splits_domain splits domain =
  Format.asprintf "Splits: %a - Domain: %a"
    pp_splits splits Cduce.pp_typ domain

let actual_expected act exp =
  Format.asprintf "Actual: %a - Expected: %a" pp_typ act pp_typ exp

let unbound_variable pos v =
  raise (Ill_typed (pos, "Unbound variable "^(Variable.show v)^"."))

let var_type pos v env =
  if Env.mem_strict v env then Env.find v env else unbound_variable pos v

let get_bind_annots pos v anns =
  match anns with
  | PEmptyA -> raise (Ill_typed (pos, "Unrelevant annotation for variable "^(Variable.show v)^"."))
  | PBindA anns -> anns

let get_lambda_annots pos v anns =
  match anns with
  | PUntypAtomA -> raise (Ill_typed (pos, "Untypable annotation for variable "^(Variable.show v)^"."))
  | PEmptyAtomA | PInstA _ -> raise (Ill_typed (pos, "Unrelevant annotation for variable "^(Variable.show v)^"."))
  | PLambdaA (_, anns) -> anns

let get_inst_annots pos anns =
  match anns with
  | PUntypAtomA -> raise (Ill_typed (pos, "Untypable annotation."))
  | PEmptyAtomA | PLambdaA _ -> raise (Ill_typed (pos, "Unrelevant annotation."))
  | PInstA anns -> anns

let treat_untypable_annot_a pos anns =
  match anns with
  | PUntypAtomA -> raise (Ill_typed (pos, "Untypable annotation."))
  | _ -> ()

let instantiate pos mono ss t =
  let check_s s =
    let vs = subst_dom s |> varset_inter mono in
    varlist vs = []
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Ill_typed (pos, "Invalid instantiation (attempt to substitute monnomorphic variable)."))

(* ===== TYPEOF ===== *)

let typeof_const_atom tenv c =
  match c with
  | Ast.Atom str -> get_type tenv str
  | c -> Ast.const_to_typ c

let rec typeof_a pos tenv env mono anns a =
  treat_untypable_annot_a pos anns ;
  let type_lambda env v e =
    let va = get_lambda_annots pos v anns in
    let splits = LambdaSAP.splits va in
    (* log "Lambda %a: %a@." Variable.pp v pp_splits splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Empty annotation for variable "^(Variable.show v)^"."))
    else begin
      LambdaSAP.destruct va |> List.map (fun (t, (anns, _, _)) ->
        let env = Env.add v t env in
        let mono = varset_union mono (vars t) in
        let res = typeof tenv env mono anns e in
        mk_arrow (cons t) (cons res)
      ) |> conj_o |> simplify_typ
    end
  in
  match a with
  | Abstract t -> t
  | Const c -> typeof_const_atom tenv c
  | Pair (v1, v2) ->
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v) -> 
    let t = var_type pos v env in
    let ss = get_inst_annots pos anns in
    let t = instantiate pos mono ss t in
    if subtype t record_any then
      try get_field t label
      with Not_found -> raise (Ill_typed (pos, "Label " ^ label ^ " not present."))
    else
      raise (Ill_typed (pos, "Field projection can only be done on a record."))
  | Projection (p, v) ->
    let t = var_type pos v env in
    let ss = get_inst_annots pos anns in
    let t = instantiate pos mono ss t in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Ill_typed (pos, "Projection can only be done on a pair."))
  | RecordUpdate (r, label, None) -> 
    let t = var_type pos r env in
    if subtype t record_any then
      remove_field t label
    else
      raise (Ill_typed (pos, "Field removal can only be done on a record."))
  | RecordUpdate (r, label, Some v) ->
    let t = var_type pos r env in
    let t' = var_type pos v env in
    if subtype t record_any then
      let right_record = mk_record false [label, cons t'] in
      merge_records t right_record
    else
      raise (Ill_typed (pos, "Field update can only be done on a record."))
  | App (v1, v2) ->
    let t1 = var_type pos v1 env in
    let ss = get_inst_annots pos anns in
    let t1 = instantiate pos mono ss t1 in
    if subtype t1 arrow_any
    then
      let t2 = var_type pos v2 env in
      let t2 = instantiate pos mono ss t2 in
      let dom = domain t1 in
      if subtype t2 dom
      then apply t1 t2
      else raise (Ill_typed (pos,
        "Argument not in the domain of the function. "^(actual_expected t2 dom)))
    else raise (Ill_typed (pos, "Application can only be done on a function."))
  | Ite (v, t, x1, x2) ->
    let tv = var_type pos v env in
    if subtype tv empty
    then empty
    else if subtype tv t
    then var_type pos x1 env
    else if subtype tv (neg t)
    then var_type pos x2 env
    else raise (Ill_typed (pos, "Cannot select a branch for the typecase."))
  | Lambda (_, Ast.ADomain s, v, e) ->
    let inferred_t = type_lambda env v e in
    let dom = domain inferred_t in
    if equiv s dom
    then inferred_t
    else raise (Ill_typed (pos,
      "The inferred domain for the abstraction is different. "^(actual_expected dom s)))
  | Lambda (_, Ast.AArrow t, v, e) ->
    let inferred_t = type_lambda env v e in
    if subtype inferred_t t
    then t
    else raise (Ill_typed (pos,
      "The inferred type for the abstraction is too weak. "^(actual_expected inferred_t t)))
  | Lambda (_, Unnanoted, v, e) -> type_lambda env v e
  | Let (v1, v2) ->
    if Env.mem_strict v1 env
    then var_type pos v2 env
    else raise (Ill_typed (pos, "Unable to type the definition."))

and typeof tenv env mono anns e =
  match e with
  | Var v -> var_type (Variable.get_locations v) v env
  | Bind (_, v, a, e) ->
    let pos = Variable.get_locations v in
    let (anns_a, va) = get_bind_annots pos v anns in
    let splits = BindSAP.splits va in
    (* log "Bind %a: %a@." Variable.pp v pp_splits splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Empty annotation for variable "^(Variable.show v)^"."))
    else begin
      let d = disj_o splits in
      let s =
        if subtype any_or_absent d
        then any_or_absent
        else typeof_a pos tenv env mono anns_a a
      in
      if subtype s d
      then
        BindSAP.destruct va |> List.map (fun (t, anns) ->
          let env = Env.add v (cap_o t s) env in
          let mono = varset_union mono (vars t) in
          typeof tenv env mono anns e
        ) |> disj_o |> simplify_typ
      else raise (Ill_typed (pos,
        "Invalid splits (does not cover the initial domain). "^(splits_domain splits s)))
    end  

(* ===== INFER ===== *)

(* TODO: update regroup so that it only strenghten the split with the actual refinement *)
