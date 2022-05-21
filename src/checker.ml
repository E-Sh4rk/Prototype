open Cduce
open Msc
open Types_additions
open Variable
open Utils
open Annotations
open Annotations.AnnotMono

exception Ill_typed of Position.t list * string

(* ===== Auxiliary functions ===== *)

let pp_splits = Utils.pp_list Cduce.pp_typ

(*let count_conjuncts t =
  let f (_, (p,n)) = (List.length p) + (List.length n) in
  Cduce.full_dnf t |> List.map f
let sum_conjuncts t =
  count_conjuncts t |> List.fold_left (fun acc i -> acc+i) 0
let pp_splits fmt splits =
  let pp_int fmt = Format.fprintf fmt "%i" in
  (pp_list pp_int) fmt (List.map sum_conjuncts splits)*)

let pp_lambda_splits fmt =
  let pp_lsplit fmt (s,(_,t,b)) =
    Format.fprintf fmt "%a -> %a (%b)" pp_typ s pp_typ t b
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
  | EmptyA -> raise (Ill_typed (pos, "Unrelevant annotation for variable "^(Variable.show v)^"."))
  | BindA anns -> anns

let get_lambda_annots pos v anns =
  match anns with
  | UntypAtomA -> raise (Ill_typed (pos, "Untypable annotation for variable "^(Variable.show v)^"."))
  | EmptyAtomA | AppA _ -> raise (Ill_typed (pos, "Unrelevant annotation for variable "^(Variable.show v)^"."))
  | LambdaA (_, anns) -> anns

let treat_untypable_annot_a pos anns =
  match anns with
  | UntypAtomA -> raise (Ill_typed (pos, "Untypable annotation."))
  | _ -> ()

(* ===== TYPEOF ===== *)

let typeof_const_atom tenv c =
  match c with
  | Ast.Atom str -> get_type tenv str
  | c -> Ast.const_to_typ c

let rec typeof_a pos tenv env anns a =
  treat_untypable_annot_a pos anns ;
  let type_lambda env v e =
    let va = get_lambda_annots pos v anns in
    let splits = LambdaSA.splits va in
    (* log "Lambda %a: %a@." Variable.pp v pp_splits splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Empty annotation for variable "^(Variable.show v)^"."))
    else begin
      LambdaSA.destruct va |> List.map (fun (t, (anns, _, _)) ->
        let env = Env.add v t env in
        let res = typeof tenv env anns e in
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
    if subtype t record_any then
      try get_field t label
      with Not_found -> raise (Ill_typed (pos, "Label " ^ label ^ " not present."))
    else
      raise (Ill_typed (pos, "Field projection can only be done on a record."))
  | Projection (p, v) ->
    let t = var_type pos v env in
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
    if subtype t1 arrow_any
    then
      let t2 = var_type pos v2 env in
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

and typeof tenv env anns e =
  match e with
  | Var v -> var_type (Variable.get_locations v) v env
  | Bind (_, v, a, e) ->
    let pos = Variable.get_locations v in
    let (anns_a, va) = get_bind_annots pos v anns in
    let splits = BindSA.splits va in
    (* log "Bind %a: %a@." Variable.pp v pp_splits splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Empty annotation for variable "^(Variable.show v)^"."))
    else begin
      let d = disj_o splits in
      let s =
        if subtype any_or_absent d
        then any_or_absent
        else typeof_a pos tenv env anns_a a
      in
      if subtype s d
      then
        BindSA.destruct va |> List.map (fun (t, anns) ->
          let env = Env.add v t env in
          typeof tenv env anns e
        ) |> disj_o |> simplify_typ
      else raise (Ill_typed (pos,
        "Invalid splits (does not cover the initial domain). "^(splits_domain splits s)))
    end  

(* ===== REFINE ===== *)

let refine_a ~sufficient tenv env a prev_t t =
  assert (subtype t prev_t) ;
  assert (has_absent prev_t |> not) ;
  if not sufficient && is_empty t then []
  else if sufficient && subtype prev_t t then [env]
  else match a, sufficient with
  | Abstract s, false -> if disjoint s t then [] else [env]
  | Abstract s, true -> if subtype s t then [env] else []
  | Const c, false -> if disjoint (typeof_const_atom tenv c) t then [] else [env]
  | Const c, true -> if subtype (typeof_const_atom tenv c) t then [env] else []
  | Pair (v1, v2), _ ->
    split_pair t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Projection (Fst, v), _ -> [Env_refinement.refine v (mk_times (cons t) any_node) env] |> filter_options
  | Projection (Snd, v), _ -> [Env_refinement.refine v (mk_times any_node (cons t)) env] |> filter_options
  | Projection (Field label, v), _ ->
    [Env_refinement.refine v (mk_record true [label, cons t]) env] |> filter_options
  | RecordUpdate (v, label, None), _ ->
    let t = cap_o t (record_any_without label) in
    split_record t
    |> List.filter_map (
      fun ti ->
          let ti = remove_field_info ti label in
          Env_refinement.refine v ti env
    )
  | RecordUpdate (v, label, Some x), _ ->
    split_record t
    |> List.filter_map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        env |>
        option_chain [Env_refinement.refine v ti ; Env_refinement.refine x field_type]
      )
  | App (v1, v2), _ ->
    let t1 = Env_refinement.find v1 env in
    (if sufficient then triangle_split t1 t else square_split t1 t)
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Ite (v, s, x1, x2), _ ->
    [ env |> option_chain [Env_refinement.refine v s       ; Env_refinement.refine x1 t] ;
      env |> option_chain [Env_refinement.refine v (neg s) ; Env_refinement.refine x2 t] ]
    |> filter_options
  | Lambda _, false ->
    if disjoint arrow_any t then [] else [env]
  | Lambda _, true ->
    if subtype arrow_any t then [env] else []
  | Let (v1, v2), _ ->
    [ env |>
    option_chain [Env_refinement.refine v1 any ; Env_refinement.refine v2 t]]
    |> filter_options

(* ===== INFER ===== *)

let regroup v res =
  res |> List.map (fun (gamma, o) ->
    let vt = Env_refinement.find v gamma in
    let gamma = Env_refinement.rm v gamma in
    (gamma, (vt, o))
  ) |> regroup Env_refinement.equiv_ref

let try_typeof_a pos tenv env anns a =
  let s =
    try typeof_a pos tenv env anns a
    with Ill_typed _ -> any_or_absent
  in
  (s, annotate_def_with_last_type s anns)

let exactly_current_env lst =
  match lst with
  | [(gamma, anns)] when Env_refinement.is_empty gamma -> Some anns
  | _ -> None

let exactly_current_env_gammas gammas =
  gammas <> [] && List.for_all Env_refinement.is_empty gammas

let filter_res_a =
  List.filter_map (function (None, _) -> None | (Some gamma, anns) -> Some (gamma, anns))

let filter_res =
  List.filter_map (function (None, _) -> None | (Some gamma, anns) -> Some (gamma, anns))

let rec infer_a' ?(no_lambda_ua=false) pos tenv env anns a ts =
  let envr = Env_refinement.empty env in
  let type_lambda v e ts va ~opt_branches_maxdom ~former_typ =
    let t = disj ts in
    if subtype arrow_any t
    then begin
      log "@,@[<v 1>LAMBDA for variable %a (unconstrained)" Variable.pp v ;
      log "@,Initial splits: %a" pp_lambda_splits (LambdaSA.destruct va) ;
      let va = LambdaSA.map_top (fun s t b ->
        if b then (worst s, t, b) else (substitute_all_jokers s any, t, b)) va
        |> LambdaSA.normalize
      in
      let splits = va |> LambdaSA.destruct in
      log "@,Using the following splits: %a" pp_lambda_splits (LambdaSA.destruct va) ;
      let res =
        splits |> List.map (fun (s, (anns, t, b)) ->
          assert (has_absent s |> not) ;
          let env = Env.add v s env in
          let res = infer_iterated tenv env anns e t in
          let changes = exactly_current_env res = None in
          let res = List.map (fun (gamma, anns) -> (gamma, (anns, worst t, b))) res in
          (res, changes)
        ) in
        let (ress, changess) = List.split res in
        let changes = List.exists identity changess in
        let res = List.flatten ress |> regroup v |> List.map (
          fun (gamma, anns_a) -> (gamma, LambdaA (former_typ, LambdaSA.construct anns_a))
        ) in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ;
      (res, changes)
    end else begin (* AbsConstr *)
      log "@,@[<v 1>LAMBDA for variable %a with t=%a" Variable.pp v pp_typ t ;
      log "@,Initial splits: %a" pp_lambda_splits (LambdaSA.destruct va) ;
      let branches =
        ts |> List.map dnf |> List.map (List.filter (fun arrows -> subtype (branch_type arrows) t)) (* Optimisation *)
        |> List.map simplify_dnf |> List.flatten |> List.flatten
      in
      log "@,Branches suggested by t: %a" pp_branches branches ;
      let va = LambdaSA.enrich ~opt_branches_maxdom ~former_typ (initial_e e) va branches in
      let res = infer_a_iterated ~no_lambda_ua:true pos tenv env (LambdaA (former_typ,va)) a [arrow_any] in
      let best_t = res |>
        List.map (fun (_, anns) ->
          match anns with
          | LambdaA (_, va) ->
            LambdaSA.destruct va
            |> List.map (fun (s,(_,t,_)) -> mk_arrow (cons (worst s)) (cons t)) (* t shouldn't contain any joker *)
          |_ -> assert false
        )
        |> List.flatten |> conj |> cap former_typ
      in
      let worst_target_t = worst t in
      let res =
        if subtype best_t worst_target_t then (res, false)
        else (log "@,Cannot obtain the required type: %s" (actual_expected best_t worst_target_t) ; ([], false))
      in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ;
      res
    end
  in
  if List.exists has_absent ts
  then begin (* Option *)
    let ts = ts |> List.map (cap_o any) in
    let (res, changes) = infer_a' pos tenv env anns a ts in
    let res =
      if subtype any (disj ts) && List.for_all (fun (gamma,_) -> Env_refinement.is_empty gamma |> not) res
      then (envr, UntypAtomA)::res else res
    in
    (res, changes)
  end else begin
    let t = disj ts in
    let worst_t = worst t in
    match a, anns with
    | _, UntypAtomA -> ([], false)
    | Abstract s, _ when subtype s worst_t ->
      ([(envr, EmptyAtomA)], false)
    | Abstract _, _ -> ([], false)
    | Const c, _ when subtype (typeof_const_atom tenv c) t ->
      ([(envr, EmptyAtomA)], false)
    | Const _, _ -> ([], false)
    | Pair (v1, v2), _ ->
      let vt1 = Env.find v1 env in
      let vt2 = Env.find v2 env in
      let res =
        if has_absent vt1 || has_absent vt2
        then
          [(envr |> option_chain
            [Env_refinement.refine v1 any ; Env_refinement.refine v2 any], EmptyAtomA)]
          |> filter_res_a
        else begin
          let s = mk_times (cons vt1) (cons vt2) in
          if subtype s t
          then [(envr, EmptyAtomA)]
          else
            let t = cap_o t s in
            split_pair t
            |> List.map (fun (ti,si) ->
              (envr |> option_chain
              [Env_refinement.refine v1 ti ; Env_refinement.refine v2 si], EmptyAtomA)
            ) |> filter_res_a
        end
      in (res, false)
    | Projection (typ, v), _ ->
      let t =
        match typ with
        | Fst -> mk_times (cons t) any_node
        | Snd -> mk_times any_node (cons t)
        | Field label -> mk_record true [label, cons t]
      in
      let res = [(Env_refinement.refine v t envr, EmptyAtomA)] |> filter_res_a in
      (res, false)
    | RecordUpdate (v, label, None), _ ->
      let t = cap_o (record_any_without label) t in
      let t = remove_field_info t label in
      let res = [(Env_refinement.refine v t envr, EmptyAtomA)] |> filter_res_a in
      (res, false)
    | RecordUpdate (v, label, Some f), _ ->
      let vt = Env.find v env in
      let ft = Env.find f env in
      let res =
        if subtype vt record_any |> not || has_absent ft
        then
          [(envr |> option_chain
            [Env_refinement.refine v record_any ; Env_refinement.refine f any], EmptyAtomA)]
          |> filter_res_a
        else begin
          let right_record = mk_record false [label, cons ft] in
          let s = merge_records vt right_record in
          if subtype s t
          then [(envr, EmptyAtomA)]
          else
            let t = cap_o t s in
            split_record t
            |> List.map (fun ti ->
              let si = get_field ti label in
              let ti = remove_field_info ti label in
              (envr |> option_chain
              [Env_refinement.refine v ti ; Env_refinement.refine f si], EmptyAtomA)
            ) |> filter_res_a
        end
      in (res, false)
    | Ite (v, s, v1, v2), _ ->
      let vt = Env.find v env in
      let res =
        if is_empty vt then [(envr, EmptyAtomA)]
        else if subtype vt s
        then [(Env_refinement.refine v1 t envr, EmptyAtomA)] |> filter_res_a
        else if subtype vt (neg s)
        then [(Env_refinement.refine v2 t envr, EmptyAtomA)] |> filter_res_a
        else [(Env_refinement.refine v s envr, EmptyAtomA) ;
              (Env_refinement.refine v (neg s) envr, EmptyAtomA)]
            |> filter_res_a
      in
      (res, false)
    | App (v1, v2), AppA (t',b) ->
      let vt1 = Env.find v1 env in
      let vt2 = Env.find v2 env in
      let res =
        if is_empty vt1
        then [(Env_refinement.refine v2 any envr, AppA (t',b))] |> filter_res_a
        else if is_empty vt2
        then [(Env_refinement.refine v1 arrow_any envr, AppA (t',b))] |> filter_res_a
        else begin
          let can_refine_l = (has_absent vt1 || has_absent vt2) |> not in
          let can_refine_r = can_refine_l && subtype t' t in
          let wt1 = mk_arrow (cons vt2) (cons t) in
          let can_split_r = can_refine_r && subtype vt1 wt1 && not b in
          match dnf (cap_o vt1 arrow_any) |> simplify_dnf with
          | [arrows] when can_split_r -> (* AppSplitR *)
              arrows |> List.map (fun (si,_) ->
                (Env_refinement.refine v2 si envr, AppA (t',true))
              ) |> filter_res_a
          | [_] when can_refine_r -> (* AppRefineR *)
            let s = triangle_exact vt1 t in
            [(Env_refinement.refine v2 s envr, AppA (t',b))]
            |> filter_res_a
          | [_] when can_refine_l -> (* AppRefineL *)
            let arrow_type = mk_arrow (cons (cap vt2 (joker Max))) (cons (cap t (joker Min))) in
            [(Env_refinement.refine v1 arrow_type envr, AppA (cap_o t t',b))]
            |> filter_res_a
          | lst -> (* AppSplitL *)
            lst |> List.map (fun arrows ->
              (envr |> option_chain [
                Env_refinement.refine v1 (branch_type arrows) ; Env_refinement.refine v2 any
              ], AppA (t',b)
              )
            ) |> filter_res_a
        end
      in (res, false)
    | App _, _ -> assert false
    | Let (v1, v2), _ ->
      let res =
        [(envr |> option_chain
          [Env_refinement.refine v1 any ; Env_refinement.refine v2 t ], EmptyAtomA)]
        |> filter_res_a in
      (res, false)
    | Lambda (_, ua, v, e), LambdaA (former_typ, va) when ua = Ast.Unnanoted || no_lambda_ua ->
      let ts = ts |> List.map (cap_o arrow_any) in
      type_lambda v e ts va ~opt_branches_maxdom:any ~former_typ
    | Lambda (_, Ast.ADomain s, v, e), LambdaA (former_typ, va) ->
      let ts = ts |> List.map (cap_o (mk_arrow (cons s) any_node)) in
      type_lambda v e ts va ~opt_branches_maxdom:s ~former_typ
    | Lambda (_, Ast.AArrow s, v, e), LambdaA (former_typ, va) when subtype s worst_t ->
      let ts = [cap_o s arrow_any] in
      type_lambda v e ts va ~opt_branches_maxdom:empty ~former_typ
    | Lambda (_, Ast.AArrow _, _, _), LambdaA _ -> ([], false)
    | Lambda _, _ -> assert false
  end

and infer' tenv env anns e' t =
  let envr = Env_refinement.empty env in
  assert (has_absent t |> not) ;
  match e', anns with
  | Var v, _ -> ([(Env_refinement.refine v t envr, EmptyA)] |> filter_res, false)
  | Bind (_, v, a, e), BindA (anns_a, va) ->
    log "@,@[<v 1>BIND for variable %a with t=%a" Variable.pp v pp_typ t ;
    let pos = Variable.get_locations v in
    log "@,Initial splits: %a" pp_splits (BindSA.splits va) ;
    let dom_a = BindSA.splits va in
    let va = BindSA.map_top worst va in
    let res =
      match BindSA.destruct va with
      | [(s, anns)] when subtype any_or_absent s -> (* BindDefSkip *)
        log "@,Skipping definition." ;
        let env = Env.add v s env in
        let res = infer_iterated tenv env anns e t in
        let changes = exactly_current_env res = None in
        let res = regroup v res |> List.map (
          fun (gamma, anns) -> (gamma, BindA (anns_a, BindSA.construct anns))
        ) in
        (res, changes)
      | splits ->
        let res_a = infer_a_iterated pos tenv env anns_a a dom_a in
        begin match exactly_current_env res_a with
        | None -> (* BindDefRefEnv *)
          if res_a = [] then log "@,Untypable definition..."
          else log "@,The definition need refinements (going up)." ;
          let res = res_a |> List.map (
            fun (gamma, anns_a) -> (gamma, BindA (anns_a, va))
          ) in
          (res, false)
        | Some anns_a ->
          log "@,The definition has been successfully annotated." ;
          let (s, anns_a) = try_typeof_a pos tenv env anns_a a in
          log "@,Type of the definition: %a" Cduce.pp_typ s ;
          (*if subtype s dom_a |> not then Format.printf "%s@." (actual_expected s dom_a) ;*)
          assert (subtype s (List.map fst splits |> disj)) ;
          let va = BindSA.normalize va s in
          let splits = BindSA.destruct va in
          let rec propagate lst treated =
            match lst with
            | [] -> None
            | (ns,anns)::lst ->
              let necessary = refine_a ~sufficient:false tenv envr a s ns in
              if exactly_current_env_gammas necessary
              then propagate lst ((ns,anns)::treated)
              else
                let sufficient = refine_a ~sufficient:true tenv envr a s (cap_o (neg ns) s) in
                Some ((ns,anns), lst@treated, necessary, sufficient)
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
              let anns = (s,anns)::splits |> BindSA.construct in
              (gamma, BindA (anns_a, anns))
            ) in
            let res2 = sufficient |> List.map (fun gamma ->
              let anns = splits |> BindSA.construct in
              (gamma, BindA (anns_a, anns))
            ) in
            (res1@res2, true)
          | None -> (* Bind *)
            log "@,Using the following splits: %a" pp_splits (List.map fst splits) ;
            let res =
              splits |> List.map (fun (s, anns) ->
                let env = Env.add v s env in
                let res = infer_iterated tenv env anns e t in
                let changes = exactly_current_env res = None in
                (res, changes)
            ) in
            let (ress, changess) = List.split res in
            let changes = List.exists identity changess in
            let res = List.flatten ress |> regroup v |> List.map (
              fun (gamma, anns) -> (gamma, BindA (anns_a, BindSA.construct anns))
            ) in
            (res, changes)
          end
        end
    in
    log "@]@,END BIND for variable %a" Variable.pp v ; res
  | Bind _, _ -> assert false

and infer_a_iterated ?(no_lambda_ua=false) pos tenv env anns a ts =
  match infer_a' ~no_lambda_ua pos tenv env anns a ts with
  | (res, true) ->
    begin match exactly_current_env res with
    | None -> res
    | Some anns -> infer_a_iterated ~no_lambda_ua pos tenv env anns a (List.map worst ts)
    end
  | (res, _) -> res

and infer_iterated tenv env anns e t =
  match infer' tenv env anns e t with
  | (res, true) ->
    begin match exactly_current_env res with
    | None -> res
    | Some anns -> infer_iterated tenv env anns e t (* t should not contain jokers *)
    end
  | (res, _) -> res

let infer tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (Old_annotations.VarAnnot.empty, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let anns =
    match infer_iterated tenv Env.empty (initial_e e) e any with
    | [] -> raise (Ill_typed ([], "Annotations inference failed."))
    | [(_, anns)] -> (e, anns)
    | _ -> assert false
  in
  log "@." ; anns

let typeof_simple tenv env e =
  let (e, anns) = infer tenv env e in
  typeof tenv Env.empty anns e |> simplify_typ
