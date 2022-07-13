open Cduce
open Msc
open Types_additions
open Variable
open Annotations
open Utils
open Annotations.AnnotPoly

exception Ill_typed of Position.t list * string

(* ===== Auxiliary functions ===== *)

let pp_splits = Utils.pp_list Cduce.pp_typ

let pp_lambda_splits fmt =
  let pp_lsplit fmt (s,(_,t)) =
    Format.fprintf fmt "%a -> %a" pp_typ s pp_typ t
  in
  Format.fprintf fmt "%a" (Utils.pp_list pp_lsplit)

let pp_branches fmt =
  let pp_lsplit fmt (s,t) =
    Format.fprintf fmt "%a -> %a" pp_typ s pp_typ t
  in
  Format.fprintf fmt "%a" (Utils.pp_list pp_lsplit)
  
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
      LambdaSAP.destruct va |> List.map (fun (t, (anns, _)) ->
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

(* ===== REFINE ===== *)

let tmpvar = mk_var "%TMP%"
let tmpvar_t = var_typ tmpvar

let sufficient_a env mono a prev_t t =
  assert (has_absent prev_t |> not && has_absent t |> not) ;
  if subtype prev_t t then [env]
  else match a with
  | Abstract _ | Const _ | Lambda _ -> []
  | Pair (v1, v2) ->
    split_pair t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Ref_env.refine v1 t1 ; Ref_env.refine v2 t2]
    )
  | Projection (Fst, v) -> [Ref_env.refine v (mk_times (cons t) any_node) env] |> filter_options
  | Projection (Snd, v) -> [Ref_env.refine v (mk_times any_node (cons t)) env] |> filter_options
  | Projection (Field label, v) ->
    [Ref_env.refine v (mk_record true [label, cons t]) env] |> filter_options
  | RecordUpdate (v, label, None) ->
    let t = cap_o t (record_any_without label) in
    split_record t
    |> List.filter_map (
      fun ti ->
          let ti = remove_field_info ti label in
          Ref_env.refine v ti env
    )
  | RecordUpdate (v, label, Some x) ->
    split_record t
    |> List.filter_map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        env |>
        option_chain [Ref_env.refine v ti ; Ref_env.refine x field_type]
      )
  | App (v1, v2) ->
    let mono = varset_union mono (vars t) in
    let lhs = Ref_env.find v1 env in
    let renaming = rename_poly mono lhs in
    let rhs = mk_arrow (cons tmpvar_t) (cons t) in
    tallying mono [(lhs,rhs)] |>
    List.filter_map (fun s ->
      let s = subst_find s tmpvar in
      let s = substitute renaming s in
      let s = clean_type ~pos:any ~neg:empty mono s in
      Ref_env.refine v2 s env
    )
  | Ite (v, s, x1, x2) ->
    [ env |> option_chain [Ref_env.refine v s       ; Ref_env.refine x1 t] ;
      env |> option_chain [Ref_env.refine v (neg s) ; Ref_env.refine x2 t] ]
    |> filter_options
  | Let (v1, v2) ->
    [ env |>
    option_chain [Ref_env.refine v1 any ; Ref_env.refine v2 t]]
    |> filter_options

let propagate_a env mono a prev_t t =
  let sufficient = sufficient_a (Ref_env.push env) mono a prev_t t in
  let merge = List.map Ref_env.merge in
  (sufficient |> merge, Ref_env.neg_refs env sufficient |> merge)

(* ===== INFER ===== *)

let regroup_res v res =
  res |> List.map (fun (t, gamma, o) ->
    let vt = if Ref_env.mem_ref v gamma
      then Ref_env.find_ref v gamma |> cap t else t in
    let gamma = Ref_env.rm_deep v gamma in
    (gamma, (vt, o))
  ) |> regroup Ref_env.equiv_ref

let try_typeof_a pos tenv env mono anns a =
  let s =
    try typeof_a pos tenv env mono anns a
    with Ill_typed _ -> any_or_absent
  in
  (s, annotate_def_with_last_type s anns)

let exactly_current_env lst =
  match lst with
  | [(gamma, anns)] when Ref_env.is_empty_ref gamma -> Some anns
  | _ -> None

let filter_res_a =
  List.filter_map (function (None, _) -> None | (Some gamma, anns) -> Some (gamma, anns))

let filter_res =
  List.filter_map (function (None, _) -> None | (Some gamma, anns) -> Some (gamma, anns))

  let pi1_type =
  let nv1 = mk_var "pi1" |> var_typ in
  let lhs = mk_times (cons nv1) any_node in
  mk_arrow (cons lhs) (cons nv1)
let pi2_type =
  let nv2 = mk_var "pi2" |> var_typ in
  let lhs = mk_times any_node (cons nv2) in
  mk_arrow (cons lhs) (cons nv2)
let pi_record_type label =
  let nv = mk_var ("pi_"^label) |> var_typ in
  let lhs = mk_record true [label, cons nv] in
  mk_arrow (cons lhs) (cons nv)

let strenghten_env_with_subst envr s =
  ignore (envr, s) ;
  failwith "TODO"

let rec infer_a' ?(no_lambda_ua=false) pos tenv env mono anns a ts =
  let envr = Ref_env.from_env env |> Ref_env.push in
  let type_lambda v e ts va ~former_typ =
    let t = disj ts in
    if subtype arrow_any t
    then begin
      log "@,@[<v 1>LAMBDA for variable %a (unconstrained)" Variable.pp v ;
      log "@,Initial splits: %a" pp_lambda_splits (LambdaSAP.destruct va) ;
      let va = va |> LambdaSAP.normalize in
      let splits = va |> LambdaSAP.destruct in
      log "@,Using the following splits: %a" pp_lambda_splits (LambdaSAP.destruct va) ;
      let res =
        splits |> List.map (fun (s, (anns, t)) ->
          assert (has_absent s |> not) ;
          let env = Env.add v s env in
          let mono = varset_union mono (vars s) in
          let res = infer_iterated tenv env mono anns e t in
          let changes = exactly_current_env res = None in
          let res = List.map (fun (gamma, anns) -> (s, gamma, (anns, t))) res in
          (res, changes)
        ) in
        let (ress, changess) = List.split res in
        let changes = List.exists identity changess in
        let res = List.flatten ress |> regroup_res v |> List.map (
          fun (gamma, anns_a) -> (gamma, PLambdaA (former_typ, LambdaSAP.construct anns_a))
        ) in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ;
      (res, changes)
    end else begin (* AbsConstr *)
      log "@,@[<v 1>LAMBDA for variable %a with t=%a" Variable.pp v pp_typ t ;
      log "@,Initial splits: %a" pp_lambda_splits (LambdaSAP.destruct va) ;
      let branches =
        ts |> List.map dnf |> List.map (List.filter (fun arrows -> subtype (branch_type arrows) t)) (* Optimisation *)
        |> List.map simplify_dnf |> List.flatten |> List.flatten
      in
      log "@,Branches suggested by t: %a" pp_branches branches ;
      let va = LambdaSAP.enrich ~former_typ (initial_e e) va branches in
      let res = infer_a_iterated ~no_lambda_ua:true pos tenv env mono (PLambdaA (former_typ,va)) a [arrow_any] in
      let best_t = res |>
        List.map (fun (_, anns) ->
          match anns with
          | PLambdaA (_, va) ->
            LambdaSAP.destruct va
            |> List.map (fun (s,(_,t)) -> mk_arrow (cons s) (cons t))
          |_ -> assert false
        )
        |> List.flatten |> conj |> cap former_typ
      in
      let res =
        if subtype best_t t then (res, false)
        else (log "@,Cannot obtain the required type: %s" (actual_expected best_t t) ; ([], false))
      in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ;
      res
    end
  in
  let type_app t1 t2 t =
    let vars_t = vars t in
    let mono = varset_union mono vars_t in
    let renaming1 = rename_poly mono t1 in
    let renaming2 = rename_poly mono t2 in
    let renaming = combine_subst renaming1 renaming2 in
    let fresh = mk_var "app" in
    let lhs = t1 in
    let rhs = mk_arrow (cons t2) (cap (var_typ fresh) t |> cons) in
    let substs = tallying vars_t [(lhs, rhs)] in
    let res =
      substs |> List.map (fun s ->
        (* TODO: simplify types *)
        let s = compose_subst s renaming in
        let (ms, ps) = split_subst s mono in
        (strenghten_env_with_subst envr ms, ps)
      ) in
    regroup Ref_env.equiv_ref res |>
    List.map (fun (e,il) -> (e, PInstA il))
  in
  if List.exists has_absent ts
  then begin (* Option *)
    let ts = ts |> List.map (cap_o any) in
    let (res, changes) = infer_a' pos tenv env mono anns a ts in
    let res =
      if subtype any (disj ts) && List.for_all (fun (gamma,_) -> Ref_env.is_empty_ref gamma |> not) res
      then (envr, PUntypAtomA)::res else res
    in
    (res, changes)
  end else begin
    let t = disj ts in
    match a, anns with
    | _, PUntypAtomA -> ([], false)
    | Abstract s, _ when subtype s t -> ([(envr, PEmptyAtomA)], false)
    | Abstract _, _ -> ([], false)
    | Const c, _ when subtype (typeof_const_atom tenv c) t ->
      ([(envr, PEmptyAtomA)], false)
    | Const _, _ -> ([], false)
    | Pair (v1, v2), _ ->
      let vt1 = Env.find v1 env in
      let vt2 = Env.find v2 env in
      let res =
        if has_absent vt1 || has_absent vt2
        then
          [(envr |> option_chain
            [Ref_env.refine v1 any ; Ref_env.refine v2 any], PEmptyAtomA)]
          |> filter_res_a
        else begin
          let s = mk_times (cons vt1) (cons vt2) in
          if subtype s t
          then [(envr, PEmptyAtomA)]
          else
            let t = cap_o t s in
            split_pair t
            |> List.map (fun (ti,si) ->
              (envr |> option_chain
              [Ref_env.refine v1 ti ; Ref_env.refine v2 si], PEmptyAtomA)
            ) |> filter_res_a
        end
      in (res, false)
    | Projection (p, v), PInstA _ ->
      let vt = Env.find v env in
      let res =
        if has_absent vt
        then [(Ref_env.refine v any envr, PInstA [])] |> filter_res_a
        else if is_empty vt
        then [(envr, PInstA [])]
        else
          let ft = match p with
          | Fst -> pi1_type | Snd -> pi2_type
          | Field label -> pi_record_type label
          in type_app ft vt t
      in (res, false)
    | Projection _, _ -> assert false
    | RecordUpdate (v, label, None), _ ->
      let t = cap_o (record_any_without label) t in
      let t = remove_field_info t label in
      let res = [(Ref_env.refine v t envr, PEmptyAtomA)] |> filter_res_a in
      (res, false)
    | RecordUpdate (v, label, Some f), _ ->
      let vt = Env.find v env in
      let ft = Env.find f env in
      let res =
        if subtype vt record_any |> not || has_absent ft
        then
          [(envr |> option_chain
            [Ref_env.refine v record_any ; Ref_env.refine f any], PEmptyAtomA)]
          |> filter_res_a
        else begin
          let right_record = mk_record false [label, cons ft] in
          let s = merge_records vt right_record in
          if subtype s t
          then [(envr, PEmptyAtomA)]
          else
            let t = cap_o t s in
            split_record t
            |> List.map (fun ti ->
              let si = get_field ti label in
              let ti = remove_field_info ti label in
              (envr |> option_chain
              [Ref_env.refine v ti ; Ref_env.refine f si], PEmptyAtomA)
            ) |> filter_res_a
        end
      in (res, false)
    | Ite (v, s, v1, v2), _ ->
      let vt = Env.find v env in
      let res =
        if is_empty vt then [(envr, PEmptyAtomA)]
        else if subtype vt s
        then [(Ref_env.refine v1 t envr, PEmptyAtomA)] |> filter_res_a
        else if subtype vt (neg s)
        then [(Ref_env.refine v2 t envr, PEmptyAtomA)] |> filter_res_a
        else [(Ref_env.refine v s envr, PEmptyAtomA) ;
              (Ref_env.refine v (neg s) envr, PEmptyAtomA)]
            |> filter_res_a
      in
      (res, false)
    | App (v1, v2), PInstA _ ->
      let vt1 = Env.find v1 env in
      let vt2 = Env.find v2 env in
      let res =
        if has_absent vt1 || has_absent vt2
        then [(envr |> option_chain [
          Ref_env.refine v1 arrow_any ; Ref_env.refine v2 any
          ], PInstA [])] |> filter_res_a
        else if is_empty vt1
        then [(Ref_env.refine v2 any envr, PInstA [])] |> filter_res_a
        else if is_empty vt2
        then [(Ref_env.refine v1 arrow_any envr, PInstA [])] |> filter_res_a
        else type_app vt1 vt2 t
      in (res, false)
    | App _, _ -> assert false
    | Let (v1, v2), _ ->
      let res =
        [(envr |> option_chain
          [Ref_env.refine v1 any ; Ref_env.refine v2 t ], PEmptyAtomA)]
        |> filter_res_a in
      (res, false)
    | Lambda (_, ua, v, e), PLambdaA (former_typ, va) when ua = Ast.Unnanoted || no_lambda_ua ->
      let ts = ts |> List.map (cap_o arrow_any) in
      type_lambda v e ts va ~former_typ
    | Lambda (_, Ast.ADomain s, v, e), PLambdaA (former_typ, va) ->
      let ts = ts |> List.map (cap_o (mk_arrow (cons s) any_node)) in
      type_lambda v e ts va ~former_typ
    | Lambda (_, Ast.AArrow s, v, e), PLambdaA (former_typ, va) when subtype s t ->
      let ts = [cap_o s arrow_any] in
      type_lambda v e ts va ~former_typ
    | Lambda (_, Ast.AArrow _, _, _), PLambdaA _ -> ([], false)
    | Lambda _, _ -> assert false
  end

and infer' tenv env mono anns e' t =
  let envr = Ref_env.from_env env |> Ref_env.push in
  assert (has_absent t |> not) ;
  match e', anns with
  | Var v, _ -> ([(Ref_env.refine v t envr, PEmptyA)] |> filter_res, false)
  | Bind (_, v, a, e), PBindA (anns_a, va) ->
    log "@,@[<v 1>BIND for variable %a with t=%a" Variable.pp v pp_typ t ;
    let pos = Variable.get_locations v in
    log "@,Initial splits: %a" pp_splits (BindSAP.splits va) ;
    let dom_a = BindSAP.splits va in
    let res =
      match BindSAP.destruct va with
      | [(s, anns)] when subtype any_or_absent s -> (* BindDefSkip *)
        log "@,Skipping definition." ;
        let env = Env.add v s env in
        let res = infer_iterated tenv env mono anns e t in
        let changes = exactly_current_env res = None in
        let res = res |> List.map (fun (g,e) -> (any_or_absent,g,e))
          |> regroup_res v |> List.map (
          fun (gamma, anns) -> (gamma, PBindA (anns_a, BindSAP.construct anns))
        ) in
        (res, changes)
      | splits ->
        let res_a = infer_a_iterated pos tenv env mono anns_a a dom_a in
        begin match exactly_current_env res_a with
        | None -> (* BindDefRefEnv *)
          if res_a = [] then log "@,Untypable definition..."
          else log "@,The definition need refinements (going up)." ;
          let res = res_a |> List.map (
            fun (gamma, anns_a) -> (gamma, PBindA (anns_a, va))
          ) in
          (res, false)
        | Some anns_a ->
          log "@,The definition has been successfully annotated." ;
          let (s, anns_a) = try_typeof_a pos tenv env mono anns_a a in
          log "@,Type of the definition: %a" Cduce.pp_typ s ;
          (*if subtype s dom_a |> not then Format.printf "%s@." (actual_expected s dom_a) ;*)
          assert (subtype s (List.map fst splits |> disj)) ;
          let va = BindSAP.normalize va in
          let splits = BindSAP.destruct va in
          let rec propagate lst treated =
            match lst with
            | [] -> None
            | (ns,anns)::lst ->
              let (sufficient, necessary) = propagate_a envr mono a s (neg (cap ns any)) in
              if sufficient <> []
              then propagate lst ((ns,anns)::treated)
              else Some ((ns,anns), lst@treated, necessary, sufficient)
          in
          let propagate =
            if subtype s any && List.length splits > 1
            then propagate splits []
            else None
          in
          begin match propagate with
          | Some ((s,anns), splits, necessary, sufficient) -> (* BindPropagate *)
            log "@,Some constraints must be propagated." ;
            let res1 = necessary |> List.map (fun gamma ->
              let anns = (s,anns)::splits |> BindSAP.construct in
              (gamma, PBindA (anns_a, anns))
            ) in
            let res2 = sufficient |> List.map (fun gamma ->
              let anns = splits |> BindSAP.construct in
              (gamma, PBindA (anns_a, anns))
            ) in
            (res1@res2, true)
          | None -> (* Bind *)
            log "@,Using the following splits: %a" pp_splits (List.map fst splits) ;
            let res =
              splits |> List.map (fun (s', anns) ->
                let env = Env.add v (cap_o s s') env in
                let mono = varset_union mono (vars s') in
                let res = infer_iterated tenv env mono anns e t in
                let changes = exactly_current_env res = None in
                let res = res |> List.map (fun (g, e) -> (s', g, e)) in
                (res, changes)
            ) in
            let (ress, changess) = List.split res in
            let changes = List.exists identity changess in
            let res = List.flatten ress |> regroup_res v |> List.map (
              fun (gamma, anns) -> (gamma, PBindA (anns_a, BindSAP.construct anns))
            ) in
            (res, changes)
          end
        end
    in
    log "@]@,END BIND for variable %a" Variable.pp v ; res
  | Bind _, _ -> assert false

and infer_a_iterated ?(no_lambda_ua=false) pos tenv env mono anns a ts =
  match infer_a' ~no_lambda_ua pos tenv env mono anns a ts with
  | (res, true) ->
    begin match exactly_current_env res with
    | None -> res
    | Some anns -> infer_a_iterated ~no_lambda_ua pos tenv env mono anns a ts
    end
  | (res, _) -> res

and infer_iterated tenv env mono anns e t =
  match infer' tenv env mono anns e t with
  | (res, true) ->
    begin match exactly_current_env res with
    | None -> res
    | Some anns -> infer_iterated tenv env mono anns e t
    end
  | (res, _) -> res

let infer tenv env mono e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (Old_annotations.VarAnnot.empty, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let anns =
    match infer_iterated tenv Env.empty mono (initial_e e) e any with
    | [] -> raise (Ill_typed ([], "Annotations inference failed."))
    | [(_, anns)] -> (e, anns)
    | _ -> assert false
  in
  log "@." ; anns

let typeof_simple tenv env mono e =
  let (e, anns) = infer tenv env mono e in
  typeof tenv Env.empty mono anns e |> simplify_typ
