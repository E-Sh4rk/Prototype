open Cduce
open Msc
open Types_additions
open Variable
open Utils
open Annotations

exception Ill_typed of Position.t list * string

(* ===== Auxiliary functions ===== *)

let splits_domain splits domain =
  Format.asprintf "Splits: %a - Domain: %a"
    (Utils.pp_list Cduce.pp_typ) splits Cduce.pp_typ domain

let actual_expected act exp =
  Format.asprintf "Actual: %a - Expected: %a" pp_typ act pp_typ exp

let unbound_variable pos v =
  raise (Ill_typed (pos, "Unbound variable "^(Variable.show v)^"."))

let var_type pos v env =
  if Env.mem_strict v env then Env.find v env else unbound_variable pos v

let get_annots pos v anns =
  match anns with
  | No_annot -> raise (Ill_typed (pos, "No annotation for variable "^(Variable.show v)^"."))
  | Annot anns -> anns

let get_annots_a pos v anns =
  match anns with
  | No_annot_a -> raise (Ill_typed (pos, "No annotation for variable "^(Variable.show v)^"."))
  | Annot_a anns -> anns

(* ===== Typeof ===== *)

let typeof_const_atom tenv c =
  match c with
  | Ast.Atom str -> get_type tenv str
  | c -> Ast.const_to_typ c

let rec typeof_a pos tenv env anns a =
  let type_lambda env v e =
    let va = get_annots_a pos v anns in
    let splits = SplitAnnot.splits va in
    (* log "Lambda %a: %a@." Variable.pp v (Utils.pp_list Cduce.pp_typ) splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Empty annotation for variable "^(Variable.show v)^"."))
    else begin
      SplitAnnot.destruct va |> List.map (fun (t, anns) ->
        let env = Env.add v t env in
        let res = typeof tenv env anns e in
        mk_arrow (cons t) (cons res)
      ) |> conj |> simplify_typ
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
    let (anns_a, va) = get_annots pos v anns in
    let splits = SplitAnnot.splits va in
    (* log "Bind %a: %a@." Variable.pp v (Utils.pp_list Cduce.pp_typ) splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Empty annotation for variable "^(Variable.show v)^"."))
    else begin
      let d = disj splits in
      let s =
        if has_absent d
        then absent
        else typeof_a pos tenv env anns_a a
      in
      if subtype s d
      then
        SplitAnnot.destruct va |> List.map (fun (t, anns) ->
          let env = Env.add v t env in
          typeof tenv env anns e
        ) |> disj |> simplify_typ
      else raise (Ill_typed (pos,
        "Invalid splits (does not cover the initial domain). "^(splits_domain splits s)))
    end

(* ===== Refine ===== *)

let refine_a tenv env a t =
  if has_absent t then [env]
  else match a with
  | Abstract s -> if disjoint s t then [] else [env]
  | Const c -> if disjoint (typeof_const_atom tenv c) t then [] else [env]
  | Pair (v1, v2) ->
    split_pair t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Projection (Fst, v) -> [Env_refinement.refine v (mk_times (cons t) any_node) env] |> filter_options
  | Projection (Snd, v) -> [Env_refinement.refine v (mk_times any_node (cons t)) env] |> filter_options
  | Projection (Field label, v) ->
    [Env_refinement.refine v (mk_record true [label, cons t]) env] |> filter_options
  | RecordUpdate (v, label, None) ->
    let t = cap_o t (record_any_without label) in
    split_record t
    |> List.filter_map (
      fun ti ->
          let ti = remove_field_info ti label in
          Env_refinement.refine v ti env
    )
  | RecordUpdate (v, label, Some x) ->
    split_record t
    |> List.filter_map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        env |>
        option_chain [Env_refinement.refine v ti ; Env_refinement.refine x field_type]
      )
  | App (v1, v2) ->
    let t1 = Env_refinement.find v1 env in
    square_split t1 t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Ite (v, s, x1, x2) ->
    [ env |> option_chain [Env_refinement.refine v s       ; Env_refinement.refine x1 t] ;
      env |> option_chain [Env_refinement.refine v (neg s) ; Env_refinement.refine x2 t] ]
    |> filter_options
  | Lambda _ ->
    if disjoint arrow_any t then [] else [env]
  | Let (v1, v2) ->
    [ env |>
    option_chain [Env_refinement.refine v1 any ; Env_refinement.refine v2 t]]
    |> filter_options

(* ===== Infer ===== *)

let typeof_a_or_absent pos tenv env anns a =
  try typeof_a pos tenv env anns a
  with Ill_typed _ -> absent

let project v =
  List.map (Env_refinement.find v)

let eliminate v =
  List.map (Env_refinement.rm v)

let are_current_env gammas =
  gammas <> [] && List.for_all Env_refinement.is_empty gammas

let rec infer_a' pos tenv env anns a t =
  ignore (pos, tenv, env, anns, a, t, infer', infer_a_iterated) ;
  failwith "TODO"

and infer' tenv env anns e t =
  let envr = Env_refinement.empty env in
  if has_absent t
  then begin (* Option *)
    let t = cap_o any t in
    let (anns, gammas, changes) = infer' tenv env anns e t in
    let gammas =
      if List.exists Env_refinement.is_empty gammas
      then gammas else envr::gammas in
    (anns, gammas, changes)
  end else begin
    match e with
    | Var v -> (No_annot, [Env_refinement.refine v t envr] |> filter_options, false)
    | Bind (_, v, a, e) ->
      log "@,@[<v 1>BIND for variable %a" Variable.pp v ;
      let pos = Variable.get_locations v in
      match anns with
      | No_annot -> (* BindDefault *)
        let anns = Annot (No_annot_a, SplitAnnot.create [(any_or_absent, No_annot)]) in
        infer' tenv env anns e t
      | Annot (anns_a, va) ->
        let splits = SplitAnnot.splits va in
        let res =
          match splits with
          | [s] when has_absent s -> (* BindArgSkip *)
            log "@,Skipping definition." ;
            let env = Env.add v s env in
            let (anns, gammas) = infer_iterated tenv env (SplitAnnot.apply va s) e t in
            let changes = are_current_env gammas |> not in
            let splits = project v gammas |> partition in
            let va = List.map (fun s -> (s, anns)) splits |> SplitAnnot.create in
            (Annot (anns_a, va), eliminate v gammas, changes)
          | splits ->
            let dom_a = disj splits in
            let (anns_a, gammas_a) = infer_a_iterated pos tenv env anns_a a dom_a in
            if gammas_a = []
            then begin (* BindArgUntyp *)
              log "@,Untypable definition..." ;
              (No_annot, [], true)
            end else if are_current_env gammas_a |> not
            then begin (* BindArgRefEnv *)
                log "@,The definition need refinements (going up)." ;
                (Annot (anns_a, va), gammas_a, true)
            end else begin
              log "@,The definition has been successfully annotated." ;
              let s = typeof_a_or_absent pos tenv env anns_a a in
              (*Format.printf "%s@." (actual_expected s dom_a) ;*)
              assert (subtype s dom_a) ;
              if is_empty s then begin (* BindDefEmpty *)
                let env = Env.add v empty env in
                let (anns, gammas) = infer_iterated tenv env (SplitAnnot.apply va empty) e t in
                let va = SplitAnnot.create [(empty, anns)] in
                let changes = are_current_env gammas |> not in
                (Annot (anns_a, va), eliminate v gammas, changes)
              end else begin
                let splits = splits |> List.map (cap_o s)
                  |> List.filter (fun t -> is_empty t |> not) in
                log "@,Using the following split: %a" (Utils.pp_list Cduce.pp_typ) splits ;
                let to_propagate =
                  if List.length splits > 1
                  then
                    splits |>
                    List.map (fun si -> refine_a tenv envr a si) |>
                    List.concat
                  else [envr]
                in
                if are_current_env to_propagate |> not
                then begin (* BindPropagateSplit *)
                  log "@,... but first some constraints must be propagated." ;
                  let va =
                    List.map (fun si -> (si, SplitAnnot.apply va si)) splits |>
                    SplitAnnot.create in
                  (Annot (anns_a, va), to_propagate, true)
                end else begin (* Bind *)
                  let res =
                    splits |> List.map (fun si ->
                      let env = Env.add v si env in
                      let (anns, gammas) = infer_iterated tenv env (SplitAnnot.apply va si) e t in
                      let changes = are_current_env gammas |> not in
                      let splits = project v gammas |> partition in
                      let va = List.map (fun s -> (s, anns)) splits in
                      (va, eliminate v gammas, changes)
                  ) in
                  let (vas, gammass, changess) = split3 res in
                  let va = vas |> List.concat |> SplitAnnot.create in
                  let gammas = List.flatten gammass in
                  let changes = List.exists identity changess in
                  (Annot (anns_a, va), gammas, changes)
                end
              end
            end
        in
        log "@]@,END BIND for variable %a" Variable.pp v ; res
    end

and infer_a_iterated pos tenv env anns a t =
  match infer_a' pos tenv env anns a t with
  | (anns, gammas, true) when are_current_env gammas ->
    infer_a_iterated pos tenv env anns a t
  | (anns, gammas, _) -> (anns, gammas)

and infer_iterated tenv env anns e t =
  match infer' tenv env anns e t with
  | (anns, gammas, true) when are_current_env gammas ->
    infer_iterated tenv env anns e t
  | (anns, gammas, _) -> (anns, gammas)

let infer tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (Old_annotations.VarAnnot.empty, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let anns =
    match infer_iterated tenv Env.empty No_annot e any with
    | (_, []) -> raise (Ill_typed ([], "Annotations inference failed."))
    | (anns, _) -> anns
  in
  log "@." ; anns

let typeof_simple tenv env e =
  let anns = infer tenv env e in
  typeof tenv Env.empty anns e |> simplify_typ
