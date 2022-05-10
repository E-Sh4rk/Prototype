open Cduce
open Msc
open Types_additions
open Variable
open Utils
open Annotations

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
  | EmptyA -> raise (Ill_typed (pos, "No annotation for variable "^(Variable.show v)^"."))
  | BindA anns -> anns

let get_lambda_annots pos v anns =
  match anns with
  | EmptyAtomA -> raise (Ill_typed (pos, "No annotation for variable "^(Variable.show v)^"."))
  | UntypAtomA -> raise (Ill_typed (pos, "Untypable annotation for variable "^(Variable.show v)^"."))
  | AppA _ -> raise (Ill_typed (pos, "Unrelevant annotation for variable "^(Variable.show v)^"."))
  | LambdaA anns -> anns

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
      LambdaSA.destruct va |> List.map (fun (t, (anns, _)) ->
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

let refine_a ~sufficient tenv env a t =
  assert (has_absent t |> not) ;
  if is_empty t && not sufficient then []
  else if subtype any t && sufficient then [env]
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
    let vt = Env_refinement.find v env in
    if is_empty vt
    then (if sufficient then [env] else [])
    else
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
  let gammas = res
  |> List.map (fun (gamma,_) -> Env_refinement.rm v gamma)
  |> Utils.remove_duplicates Env_refinement.equiv
  in
  gammas |> List.map (fun gamma ->
    let anns = res |> List.filter_map (fun (gamma', o) ->
      let vt = Env_refinement.find v gamma' in
      let gamma' = Env_refinement.rm v gamma' in
      if Env_refinement.leq gamma gamma'
      then Some (vt, o)
      else None
    ) in
    (gamma, anns)
  )

let try_typeof_a pos tenv env anns a =
  try typeof_a pos tenv env anns a
  with Ill_typed _ -> any_or_absent

let exactly_current_env lst =
  match lst with
  | [(gamma, anns)] when Env_refinement.is_empty gamma -> Some anns
  | _ -> None

let exactly_current_env_gammas gammas =
  gammas <> [] && List.for_all Env_refinement.is_empty gammas

let filter_res =
  List.filter_map (function (None, _) -> None | (Some gamma, anns) -> Some (gamma, anns))

let rec infer_a' pos tenv env anns a t =
  let envr = Env_refinement.empty env in
  let type_lambda v e t ~maxdom ~fixeddom =
    ignore (v, e, t, maxdom, fixeddom) ;
    failwith "TODO"
  in
  if has_absent t
  then begin (* Option *)
    let t = cap_o any t in
    let (res, changes) = infer_a' pos tenv env anns a t in
    let res =
      if subtype any t && List.for_all (fun (gamma,_) -> Env_refinement.is_empty gamma |> not) res
      then (envr, UntypAtomA)::res else res in
    (res, changes)
  end else begin
    ignore (type_lambda, regroup) ;
    failwith "TODO"
  end

(* TODO: share_jokerized_arrows *)
and infer' tenv env anns e' t =
  let envr = Env_refinement.empty env in
  assert (has_absent t |> not) ;
  match e' with
  | Var v -> ([(Env_refinement.refine v t envr, EmptyA)] |> filter_res, false)
  | Bind (_, v, a, e) ->
    match anns with
    | EmptyA -> (* BindDefault *)
      let anns = BindA (EmptyAtomA, BindSA.construct [(any_or_absent, EmptyA)]) in
      infer' tenv env anns e' t
    | BindA (anns_a, va) ->
      log "@,@[<v 1>BIND for variable %a with t=%a" Variable.pp v pp_typ t ;
      let pos = Variable.get_locations v in
      log "@,Initial splits: %a" pp_splits (BindSA.splits va) ;
      let dom_a = BindSA.dom va in
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
        | _ ->
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
            let s = try_typeof_a pos tenv env anns_a a in
            log "@,Type of the definition: %a" Cduce.pp_typ s ;
            (*if subtype s dom_a |> not then Format.printf "%s@." (actual_expected s dom_a) ;*)
            assert (subtype s dom_a) ;
            let splits = BindSA.choose va s |> BindSA.map_top (cap_o s) |> BindSA.destruct in
            log "@,Using the following split: %a" pp_splits (List.map fst splits) ;
            let rec propagate lst treated =
              match lst with
              | [] -> (treated, None)
              | (s,anns)::lst ->
                let necessary = refine_a ~sufficient:false tenv envr a s in
                if exactly_current_env_gammas necessary
                then propagate lst ((s,anns)::treated)
                else
                  let sufficient = refine_a ~sufficient:true tenv envr a (neg s) in
                  (lst@treated, Some ((s,anns), necessary, sufficient))
            in
            let (splits, propagate) =
              if subtype s any && List.length splits > 1
              then propagate splits []
              else (splits, None)
            in
            begin match propagate with
            | Some ((s,anns), necessary, sufficient) -> (* BindPropagateSplit *)
              log "@,... but first some constraints must be propagated." ;
              let res1 = necessary |> List.map (fun gamma ->
                let anns = (s,anns)::splits |> BindSA.construct in
                (gamma, BindA (anns_a, anns))
              ) in
              let res2 = sufficient |> List.map (fun gamma ->
                let anns = splits |> BindSA.construct in
                (gamma, BindA (anns_a, anns))
              ) in
              (res1@res2, false)
            | None -> (* Bind *)
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

and infer_a_iterated pos tenv env anns a t =
  match infer_a' pos tenv env anns a t with
  | (res, true) ->
    begin match exactly_current_env res with
    | None -> res
    | Some anns -> infer_a_iterated pos tenv env anns a t
    end
  | (res, _) -> res

and infer_iterated tenv env anns e t =
  match infer' tenv env anns e t with
  | (res, true) ->
    begin match exactly_current_env res with
    | None -> res
    | Some anns -> infer_iterated tenv env anns e t
    end
  | (res, _) -> res

let infer tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (Old_annotations.VarAnnot.empty, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let anns =
    match infer_iterated tenv Env.empty EmptyA e any with
    | [] -> raise (Ill_typed ([], "Annotations inference failed."))
    | [(_, anns)] -> (e, anns)
    | _ -> assert false
  in
  log "@." ; anns

let typeof_simple tenv env e =
  let (e, anns) = infer tenv env e in
  typeof tenv Env.empty anns e |> simplify_typ
