open Cduce
open Nf_ast
open Types_additions
open Annotations
open Variable

exception Ill_typed of Position.t list * string

let splits_domain splits domain =
  Format.asprintf "Splits: %a - Domain: %a"
    (Utils.pp_list Cduce.pp_typ) splits Cduce.pp_typ domain

let actual_expected act exp =
  Format.asprintf "Actual: %a - Expected: %a" pp_typ act pp_typ exp

let unbound_variable pos v =
  raise (Ill_typed (pos, "Unbound variable "^(Variable.show v)^"."))

let var_type pos v env =
  if Env.mem v env then Env.find v env else unbound_variable pos v

let check_var_dom pos v env =
  if Env.mem v env |> not then unbound_variable pos v

let rec typeof_a pos tenv env annots a =
  let type_lambda env annots v e =
    let splits = Annotations.splits_strict v env annots in
    if splits = []
    then raise (Ill_typed (pos, "Cannot infer domain of this abstraction."))
    else begin
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        let res = typeof tenv env annots e in
        mk_arrow (cons t) (cons res)
      ) |> conj |> simplify_typ
    end
  in
  match a with
  | Abstract t -> t
  | Const (Atom str) -> get_type_or_atom tenv str
  | Const c -> Ast.const_to_typ c
  | Var v -> var_type pos v env
  | Debug (_, v) -> var_type pos v env
  | Pair (v1, v2) ->
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (p, v) ->
    let t = var_type pos v env in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Ill_typed (pos, "Projection can only be done on a pair."))
  | RecordUpdate _ -> failwith "Not implemented"
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
    if subtype tv t
    then var_type pos x1 env
    else if subtype tv (neg t)
    then var_type pos x2 env
    else raise (Ill_typed (pos, "Cannot select a branch for the typecase."))
  | Lambda (Ast.ADomain s, v, e) ->
    let inferred_t = type_lambda env annots v e in
    let dom = domain inferred_t in
    if subtype s dom
    then inferred_t
    else raise (Ill_typed (pos,
      "The inferred domain for the abstraction is too weak. "^(actual_expected dom s)))
  | Lambda (Ast.AArrow t, v, e) ->
    let inferred_t = type_lambda env annots v e in
    if subtype inferred_t t
    then t
    else raise (Ill_typed (pos,
      "The inferred type for the abstraction is too weak. "^(actual_expected inferred_t t)))
  | Lambda (Unnanoted, v, e) -> type_lambda env annots v e
  | Let (v1, v2) ->
    if Env.mem v1 env
    then var_type pos v2 env
    else raise (Ill_typed (pos, "Unable to type the definition."))

and typeof tenv env annots e =
  match e with
  | EVar v -> var_type (Variable.get_locations v) v env
  | Bind (v, a, e) ->
    let splits = Annotations.splits_strict v env annots in
    if splits = []
    then typeof tenv env annots e
    else begin
      let pos = Variable.get_locations v in
      let s = typeof_a pos tenv env annots a in
      if disj splits |> subtype s
      then
        splits |> List.map (fun t ->
          let env = Env.add v t env in
          typeof tenv env annots e
        ) |> disj |> simplify_typ
      else raise (Ill_typed (pos,
        "Invalid splits (does not cover the whole domain). "^(splits_domain splits s)))
    end

let refine_a ~backward env a t =
  begin match a with
  | Abstract s when backward -> if disjoint s t then [] else [Env.empty]
  | Abstract s -> if subtype s t then [Env.empty] else []
  | Const c when backward ->
    if disjoint (Ast.const_to_typ c) t then [] else [Env.empty]
  | Const c ->
    if subtype (Ast.const_to_typ c) t then [Env.empty] else []
  | Var v -> [Env.singleton v t]
  | Debug (_, v) -> [Env.singleton v t]
  | Pair (v1, v2) ->
    split_pair t
    |> List.map (
      fun (t1, t2) ->
        let env1 = Env.singleton v1 t1 in
        let env2 = Env.singleton v2 t2 in
        Env.cap env1 env2
    )
  | Projection (Fst, v) -> [mk_times (cons t) any_node |> Env.singleton v]
  | Projection (Snd, v) -> [mk_times any_node (cons t) |> Env.singleton v]
  | Projection _ -> failwith "Not implemented"
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    (if backward then square_split t1 t else triangle_split t1 t)
    |> List.map (
      fun (t1, t2) ->
        let env1 = Env.singleton v1 t1 in
        let env2 = Env.singleton v2 t2 in
        Env.cap env1 env2
    )
  | Ite (v, s, x1, x2) ->
    let env1 = Env.singleton v s in
    let env2 = Env.singleton v (neg s) in
    let env1' = Env.singleton x1 t in
    let env2' = Env.singleton x2 t in
    [Env.cap env1 env1' ; Env.cap env2 env2']
  | Lambda _ when backward -> [Env.empty]
  | Lambda _ -> []
  | Let (v1, v2) -> [Env.cap (Env.singleton v1 any) (Env.singleton v2 t)]
  end
  |> List.map (fun env' -> List.fold_left
    (fun acc v -> Env.strengthen v (Env.find v env) acc)
    env' (Env.domain env')) (* Inter *)
  |> List.filter (fun env -> Env.contains_empty env |> not) (* RemoveBottomEnv *)
  |> List.map (fun env' ->
    Env.filter (fun v t -> subtype (Env.find v env) t |> not) env'
    ) (* RemoveUselessVar *)

type infer_res =
  | Result of Annotations.t
  | NeedSplit of Annotations.t * (Env.t list) * (Env.t list)

let merge_annotations additional_annots res =
  let aux = function
  | Result annots -> (annots, [], [])
  | NeedSplit (annots, gammas1, gammas2) -> (annots, gammas1, gammas2)
  in
  let rec split3 lst = 
    match lst with
    | [] -> ([], [], [])
    | (a,b,c)::lst ->
      let (ar,br,cr) = split3 lst in
      (a::ar, b::br, c::cr)
  in
  let is_result = function
  | Result _ -> true
  | NeedSplit _ -> false
  in
  let (a,b,c) = List.map aux res |> split3 in
  let (a,b,c) = (Annotations.union (additional_annots::a), List.concat b, List.concat c) in
  if List.for_all is_result res
  then Result a else NeedSplit (a,b,c)

let backward env x a gammas =
  gammas |>
  List.map (fun gamma' ->
    if Env.mem x gamma'
    then (refine_a ~backward:true (Env.cap env gamma') a (Env.find x gamma')
      |> List.map (fun gamma'' -> Env.cap gamma' gamma''))
    else [Env.add x (Env.find x env) gamma']
  ) |> List.flatten

let forward env x a gammas =
  gammas |>
  List.map (fun gamma' ->
    if Env.mem x gamma'
    then (refine_a ~backward:false (Env.cap env gamma') a (Env.find x gamma')
      |> List.map (fun gamma'' -> Env.cap (Env.rm x gamma') gamma''))
    else [gamma']
  ) |> List.flatten

let domain_included_in_singleton env x =
  List.for_all (fun v -> Variable.equals v x) (Env.domain env)

exception Return of infer_res

let rec infer' tenv env annots e =
  let rec infer_with_split tenv env annots s x a e =
    let env' = Env.add x s env in
    match infer' tenv env' annots e with
    | Result annots' -> Result (Annotations.add_split x env s annots') (* LetSplitOk *)
    | NeedSplit (annots', gammas1, gammas2) ->
      let gammas1' = backward env' x a gammas1 in
      let gammas2' = forward env' x a gammas2 in
      if List.for_all (fun gamma' -> domain_included_in_singleton gamma' x) (gammas1'@gammas2')
      then (* BindSplitTop *)
        let splits = List.map (fun env'' -> Env.find x env'') gammas1'
        |> VarAnnot.partition in
        assert (disj splits |> subtype s) ;
        List.map (fun s -> infer_with_split tenv env annots' s x a e) splits |>
        merge_annotations Annotations.empty
      else (* BindSplitUp *)
        let x_annots = List.fold_left (fun acc env'' ->
          VarAnnot.add_split (Env.cap env (Env.rm x env'')) (Env.find x env'') acc
        ) VarAnnot.empty gammas1'
        in
        assert (VarAnnot.is_empty x_annots |> not) ;
        let annots'' = Annotations.add_var x x_annots annots' in
        let gammas1'' = List.map (Env.rm x) gammas1' in
        NeedSplit (annots'', gammas1'', gammas2')
  in
  match e with
  | EVar v ->
    check_var_dom (Variable.get_locations v) v env ;
    Result (Annotations.empty)
  | Bind (v, a, e) ->
    try
      let pos = Variable.get_locations v in
      let annots1 = Annotations.restrict (bv_a a) annots in
      let annots2 = Annotations.restrict (bv_e e) annots in
      let res =
        try infer_a' pos tenv env annots1 a
        with Ill_typed _ -> (* BindAUntypeable *)
          raise (Return (infer' tenv env annots2 e))
      in
      begin match res with
      | NeedSplit (a,b,c) -> NeedSplit (a,b,c) (* BindANeedSplit *)
      | Result annots1' -> (* Bind *)
        let t = typeof_a pos tenv env annots1' a in
        let splits = Annotations.splits v env ~initial:t annots in
        assert (disj splits |> subtype t) ;
        splits |>
        List.map (fun s -> infer_with_split tenv env annots2 s v a e) |>
        merge_annotations annots1'
      end
    with Return r -> r

and infer_a' pos tenv env annots a =
  let rec infer_with_split ~enforce_domain tenv env annots s x e =
    try
      let env' = Env.add x s env in
      let res =
        try infer' tenv env' annots e
        with (Ill_typed _) as err -> begin
          if enforce_domain then raise err
          else raise (Return (* AbsSplitBad *) (Result Annotations.empty))
        end
      in
      match res with
      | Result annots' -> Result (Annotations.add_split x env s annots') (* AbsSplitOk *)
      | NeedSplit (annots', gammas1, gammas2) ->
        if List.for_all (fun gamma' -> domain_included_in_singleton gamma' x) (gammas1@gammas2)
        then (* AbsSplitTop *)
          let splits = (List.map
            (fun env'' -> Env.find x (Env.cap env'' (Env.singleton x s))) gammas1
            ) @ (
              List.filter (fun env'' -> Env.mem x env'') gammas2 |>
              List.map (fun env'' -> Env.find x env'')
            )
          |> VarAnnot.partition in
          assert (disj splits |> subtype s) ;
          List.map (fun s -> infer_with_split ~enforce_domain tenv env annots' s x e) splits |>
          merge_annotations Annotations.empty
        else (* AbsSplitUp *)
          let x_annots = VarAnnot.cup
            (List.fold_left (fun acc env'' ->
                let env'' = Env.cap env'' (Env.singleton x s) in
                VarAnnot.add_split (Env.cap env (Env.rm x env'')) (Env.find x env'') acc
              ) VarAnnot.empty gammas1
            ) (
              List.filter (fun env'' -> Env.mem x env'') gammas2 |>
              List.fold_left (fun acc env'' ->
                VarAnnot.add_split (Env.cap env (Env.rm x env'')) (Env.find x env'') acc
              ) VarAnnot.empty
            )
          in
          assert (VarAnnot.is_empty x_annots |> not) ;
          let annots'' = Annotations.add_var x x_annots annots' in
          let gammas1' = List.map (Env.rm x) gammas1 in
          let gammas2' = List.map (Env.rm x) gammas2 in
          NeedSplit (annots'', gammas1', gammas2')
    with Return r -> r
  in
  let type_lambda_with_splits ~enforce_domain tenv env annots splits x e =
    (* Abs *)
    let annots' = Annotations.restrict (bv_e e) annots in
    let res =
      splits |>
      List.map (fun s -> infer_with_split ~enforce_domain tenv env annots' s x e) |>
      merge_annotations Annotations.empty
    in
    let empty_dom = match res with
    | Result annots'' -> Annotations.is_empty x annots''
    | NeedSplit (annots'',_,_) -> Annotations.is_empty x annots''
    in
    if empty_dom
    then raise (Ill_typed (pos, "Cannot infer the domain of this abstraction."))
    else res
  in
  match a with
  | Abstract _ -> Result (Annotations.empty)
  | Const _ -> Result (Annotations.empty)
  | Var v -> check_var_dom pos v env ; Result (Annotations.empty)
  | Debug (_, v) -> check_var_dom pos v env ; Result (Annotations.empty)
  | Pair (v1, v2) ->
    check_var_dom pos v1 env ; check_var_dom pos v2 env ; Result (Annotations.empty)
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (_, v) ->
    let t = var_type pos v env in
    if subtype t pair_any then
      begin match split_pair t with
      | [] -> Result (Annotations.empty)
      | [_] -> Result (Annotations.empty)
      | lst ->
        let gammas = lst |> List.map (fun (t1, t2) ->
          Env.singleton v (mk_times (cons t1) (cons t2))
        ) in
        NeedSplit (Annotations.empty, gammas, gammas)
      end
    else begin
      let t1 = cap t pair_any in
      let t2 = diff t pair_any in
      if is_empty t1 || is_empty t2
      then raise (Ill_typed (pos,
        "Bad domain for the projection. "^(actual_expected t pair_any)))
      else (
        let env1 = Env.singleton v t1 in
        let env2 = Env.singleton v t2 in
        NeedSplit (Annotations.empty, [env1;env2], [env1;env2])
      )
    end
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) ->
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    if subtype t1 arrow_any then
      begin match split_arrow t1 with
      | [] -> Result (Annotations.empty)
      | [t1] ->
        begin match dnf t1 with
        | [arrows] ->
          if List.exists (fun (s,_) -> subtype t2 s) arrows
          then Result (Annotations.empty)
          else begin
            let dom = domain t1 in
            if subtype t2 dom
            then begin
              let gammas = arrows |> List.map (fun (s,_) -> cap s t2) |>
                List.filter (fun t2 -> is_empty t2 |> not) |>
                List.map (fun t2 -> Env.singleton v2 t2) in
              NeedSplit (Annotations.empty, gammas, gammas)
            end else begin
              let t2' = cap t2 dom in
              let t2'' = diff t2 dom in
              if is_empty t2' || is_empty t2''
              then raise (Ill_typed (pos,
                "Bad domain for the application. "^(actual_expected t2 dom)))
              else (
                let env1 = Env.singleton v2 t2' in
                let env2 = Env.singleton v2 t2'' in
                NeedSplit (Annotations.empty, [env1;env2], [env1;env2])
              )
            end
          end
        | _ -> assert false
        end
      | lst ->
        let gammas = lst |> List.map (fun t1 -> Env.singleton v1 t1) in
        NeedSplit (Annotations.empty, gammas, gammas)
      end
    else begin
      let t1' = cap t1 arrow_any in
      let t1'' = diff t1 arrow_any in
      if is_empty t1' || is_empty t1''
      then raise (Ill_typed (pos,
        "Cannot apply a non-arrow type. "^(actual_expected t1 arrow_any)))
      else (
        let env1 = Env.singleton v1 t1' in
        let env2 = Env.singleton v1 t1'' in
        NeedSplit (Annotations.empty, [env1;env2], [env1;env2])
      )
    end
  | Ite (v, t, v1, v2) ->
    let tv = var_type pos v env in
    let t1 = cap tv t in
    let t2 = cap tv (neg t) in
    if is_empty t2
    then begin
      check_var_dom pos v1 env ;
      Result (Annotations.empty)
    end else if is_empty t1 then begin
      check_var_dom pos v2 env ;
      Result (Annotations.empty)
    end else begin
      let env1 = Env.singleton v t1 in
      let env2 = Env.singleton v t2 in
      NeedSplit (Annotations.empty, [env1;env2], [env1;env2])
    end
  | Lambda (Ast.ADomain s, v, e) ->
    let splits = Annotations.splits v env ~initial:s annots in
    assert (disj splits |> subtype s) ;
    type_lambda_with_splits ~enforce_domain:true tenv env annots splits v e
  | Lambda (Ast.Unnanoted, v, e) ->
    let splits = Annotations.splits v env annots in
    type_lambda_with_splits ~enforce_domain:false tenv env annots splits v e
  | Lambda (Ast.AArrow t, v, e) ->
    let splits =
      dnf t |> List.map (fun lst -> List.map fst lst) |>
      List.flatten |> VarAnnot.partition |>
      List.map (fun s -> Annotations.splits v env ~initial:s annots) |>
      List.flatten |> VarAnnot.partition
    in
    assert (disj splits |> subtype (domain t)) ;
    type_lambda_with_splits ~enforce_domain:true tenv env annots splits v e
  | Let (v1, v2) ->
    check_var_dom pos v1 env ; check_var_dom pos v2 env ; Result (Annotations.empty)

let infer tenv env annots e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (v, Abstract (Env.find v env), acc)
  ) fv e in
  match infer' tenv Env.empty annots e with
  | Result annots -> (e, annots)
  | NeedSplit _ -> assert false

let typeof_simple tenv env e =
  let (e, annots) = infer tenv env Annotations.empty e in
  typeof tenv Env.empty annots e |> simplify_typ
