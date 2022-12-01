open Types.Base
open Types.Tvar
open Types.Additions
open Common
open Parsing.Variable
open Msc
open Annotations

(* ====================================== *)
(* =============== TYPEOF =============== *)
(* ====================================== *)

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
  else raise (Untypeable (pos, "Invalid branch: abstracted variable should be monomorphic."))

let rename_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid renaming."))

let generalize_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_poly |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid generalization."))  
  
let rec typeof_a vardef tenv env annot_a a =
  let open FullAnnot in
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
  in
  begin match a, annot_a with
  | Alias v, AliasA -> var_type v env
  | Abstract t, AbstractA -> t
  | Const c, ConstA -> typeof_const_atom tenv c
  | Pair (v1, v2), PairA (r1, r2) ->
    let t1 = var_type v1 env |> rename_check pos r1 in
    let t2 = var_type v2 env |> rename_check pos r2 in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v), ProjA ss ->
    let t = var_type v env |> instantiate_check pos ss in
    if subtype t record_any
    then
      try get_field t label
      with Not_found ->
        raise (Untypeable (pos, "Invalid projection: missing label " ^ label ^ "."))
    else raise (Untypeable (pos, "Invalid projection: not a record."))
  | Projection (p, v), ProjA ss ->
    let t = var_type v env |> instantiate_check pos ss in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Untypeable (pos, "Invalid projection: not a pair."))
  | RecordUpdate (v, label, None), RecordUpdateA (ss, None) ->
    let t = var_type v env |> instantiate_check pos ss in
    if subtype t record_any
    then remove_field t label
    else raise (Untypeable (pos, "Invalid field deletion: not a record."))
  | RecordUpdate (v, label, Some v'), RecordUpdateA (ss, Some r) ->
    let t = var_type v env |> instantiate_check pos ss in
    if subtype t record_any
    then
      let t' = var_type v' env |> rename_check pos r in
      let right_record = mk_record false [label, cons t'] in
      merge_records t right_record  
    else raise (Untypeable (pos, "Invalid field update: not a record."))
  | App (v1, v2), AppA ss ->
    (* NOTE: different from the paper *)
    let t1 = var_type v1 env in
    let t2 = var_type v2 env in
    ss |> List.map (fun s ->
      let t1 = instantiate_check pos [s] t1 in
      let t2 = instantiate_check pos [s] t2 in
      if subtype t1 arrow_any
      then
        if subtype t2 (domain t1)
        then apply t1 t2
        else raise (Untypeable (pos, "Invalid application: argument not in the domain."))
      else raise (Untypeable (pos, "Invalid application: not a function."))    
    ) |> conj_o
  | Ite (v, _, _, _), EmptyA ss ->
    let t = var_type v env |> instantiate_check pos ss in
    if is_empty t then empty
    else raise (Untypeable (pos, "Invalid typecase: tested expression is not empty."))  
  | Ite (v, s, v1, _), ThenA ->
    let t = var_type v env in
    if subtype t s
    then var_type v1 env
    else raise (Untypeable (pos, "Invalid typecase: tested expression hasn't the required type."))
  | Ite (v, s, _, v2), ElseA ->
    let t = var_type v env in
    if subtype t (neg s)
    then var_type v2 env
    else raise (Untypeable (pos, "Invalid typecase: tested expression hasn't the required type."))  
  | Let (v1, v2), LetA ->
    if Env.mem v1 env
    then var_type v2 env
    else raise (Untypeable (pos, "Invalid let binding: definition has not been typed."))
  | Lambda (_, Parsing.Ast.AArrow _, _, _), LambdaA _ ->
    raise (Untypeable (pos, "Invalid lambda: explicitely typed lambdas are not supported."))
  | Lambda (_, _, v, e), LambdaA branches -> type_lambda env branches v e
  | _, _ -> raise (Untypeable (pos, "Invalid annotations."))
  end
  |> clean_poly_vars |> simplify_typ
  
and typeof tenv env annot e =
  let open FullAnnot in
  begin match e, annot with
  | Var v, BVar r -> var_type v env |> rename_check [] r
  | Bind (_, v, a, e), Keep (annot_a, gen, ty, branches) ->
    let t = (* TODO: We are cheating... *)
      begin match ty with
      | None -> typeof_a v tenv env annot_a a
      | Some t -> t
      end in
    let pos = Variable.get_locations v in
    if branches = []
    then raise (Untypeable (pos, "Invalid decomposition: cannot be empty."))
    else
      let dom = branches |> List.map fst |> disj in
      if subtype t dom
      then
        let t = generalize_check pos gen t in
        branches |> List.map (fun (s, annot) ->
          let env = Env.add v (cap t s) env in
          typeof tenv env annot e
        ) |> disj_o
      else raise (Untypeable (pos, "Invalid decomposition: does not cover the whole domain."))
  | Bind (_, v, _, e), Skip annot ->
    assert (Env.mem v env |> not) ;
    typeof tenv env annot e
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> clean_poly_vars |> simplify_typ

(* ====================================== *)
(* =============== REFINE =============== *)
(* ====================================== *)

let refine_a env a t =
  match a with
  | Alias _ | Abstract _ | Const _ | Lambda _ -> []
  | Pair (v1, v2) ->
    split_pair t
    |> List.map (
      fun (t1, t2) -> Env.construct_dup [(v1,t1) ; (v2, t2)]
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
        Env.construct_dup [(v, ti) ; (x, field_type)]
      )
  | App _ -> ignore env ; failwith "TODO"
  | Ite (v, s, v1, v2) ->
    [Env.construct_dup [(v,s);(v1,t)] ; Env.construct_dup [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ====================================== *)
(* ================ INFER =============== *)
(* ====================================== *)

let infer _ = ignore refine_a ; failwith "TODO"

let typeof_simple _ = failwith "TODO"
