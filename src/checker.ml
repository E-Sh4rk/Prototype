open Cduce
open Nf_ast
open Types_additions
open Annotations
open Variable

(* TODO: Init annotations with VarAnnot.empty, and for Lambdas,
   if the splits are empty, then consider that the initial type is Any *)

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

let rec typeof_a pos tenv env a =
  let type_lambda env va v e =
    let splits = VarAnnot.splits env va in
    if splits = []
    then raise (Ill_typed (pos, "Cannot infer domain of this abstraction."))
    else begin
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        let res = typeof tenv env e in
        mk_arrow (cons t) (cons res)
      ) |> conj |> simplify_typ
    end
  in
  match a with
  | Abstract t -> t
  | Const (Atom str) -> get_type_or_atom tenv str
  | Const c -> Ast.const_to_typ c
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
    if subtype tv empty
    then empty
    else if subtype tv t
    then var_type pos x1 env
    else if subtype tv (neg t)
    then var_type pos x2 env
    else raise (Ill_typed (pos, "Cannot select a branch for the typecase."))
  | Lambda (va, Ast.ADomain s, v, e) ->
    let inferred_t = type_lambda env va v e in
    let dom = domain inferred_t in
    if subtype s dom
    then inferred_t
    else raise (Ill_typed (pos,
      "The inferred domain for the abstraction is too weak. "^(actual_expected dom s)))
  | Lambda (va, Ast.AArrow t, v, e) ->
    let inferred_t = type_lambda env va v e in
    if subtype inferred_t t
    then t
    else raise (Ill_typed (pos,
      "The inferred type for the abstraction is too weak. "^(actual_expected inferred_t t)))
  | Lambda (va, Unnanoted, v, e) -> type_lambda env va v e
  | Let (v1, v2) ->
    if Env.mem v1 env
    then var_type pos v2 env
    else raise (Ill_typed (pos, "Unable to type the definition."))

and typeof tenv env e =
  match e with
  | Var v -> var_type (Variable.get_locations v) v env
  | Bind (va, v, a, e) ->
    let splits = VarAnnot.splits env va in
    if splits = []
    then typeof tenv env e
    else begin
      let pos = Variable.get_locations v in
      let s = typeof_a pos tenv env a in
      if disj splits |> subtype s
      then
        splits |> List.map (fun t ->
          let env = Env.add v t env in
          typeof tenv env e
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
  | Lambda _ when backward ->
    if disjoint arrow_any t then [] else [Env.empty]
  | Lambda _ ->
    if subtype arrow_any t then [Env.empty] else []
  | Let (v1, v2) -> [Env.cap (Env.singleton v1 any) (Env.singleton v2 t)]
  end
  |> List.map (fun env' -> List.fold_left
    (fun acc v -> Env.strengthen v (Env.find v env) acc)
    env' (Env.domain env')) (* Inter *)
  |> List.filter (fun env -> Env.contains_empty env |> not) (* RemoveBottomEnv *)
  |> List.map (fun env' ->
    Env.filter (fun v t -> subtype (Env.find v env) t |> not) env'
    ) (* RemoveUselessVar *)

let backward env x a gammas =
  gammas |>
  List.map (fun gamma' ->
    if Env.mem x gamma'
    then (refine_a ~backward:true (Env.cap env gamma') a (Env.find x gamma')
      |> List.map (Env.cap gamma'))
    else [Env.add x (Env.find x env) gamma']
  ) |> List.flatten

(*let forward env x a gammas =
  gammas |>
  List.map (fun gamma' ->
    if Env.mem x gamma'
    then (refine_a ~backward:false (Env.cap env gamma') a (Env.find x gamma')
      |> List.map (Env.cap (Env.rm x gamma')))
    else [gamma']
  ) |> List.flatten*)

let domain_included_in_singleton env x =
  List.for_all (fun v -> Variable.equals v x) (Env.domain env)

let empty_annots =
  map_a
  (function Bind (_, v, a, e) -> Bind (VarAnnot.empty, v, a, e) | e -> e)
  (function Lambda (_, t, v, e) -> Lambda (VarAnnot.empty, t, v, e) | a -> a)

type infer_res = e * (Env.t list)
exception Return of infer_res

let merge_res res =
  let (es, gammas) = List.split res in
  (merge_annots es, List.concat gammas)

let rec infer' tenv env e =
  let rec infer_with_split tenv env s x a e = (* TODO: from here *)
    let env' = Env.add x s env in
    match infer' tenv env' e with
    | (e, []) -> (VarAnnot.singleton env s, (e, [])) (* BindSplitOk *)
    | (e, gammas) ->
      let gammas = backward env' x a gammas in
      if List.for_all (fun gamma -> domain_included_in_singleton gamma x) gammas
      then (* BindSplitTop *)
        let splits = List.map (fun gamma -> Env.find x gamma) gammas
        |> partition s in
        assert (disj splits |> subtype s) ;
        let (vas, res) =
          List.map (fun s -> infer_with_split tenv env s x a e) splits |>
          List.split
        in
        (VarAnnot.union vas, merge_res res)
      else (* BindSplitUp *)
        let va = List.fold_left (fun acc gamma ->
          VarAnnot.add_split (Env.cap env (Env.rm x gamma)) (Env.find x gamma) acc
        ) VarAnnot.empty gammas
        in
        assert (VarAnnot.is_empty va |> not) ;
        let gammas = List.map (Env.rm x) gammas in
        (va, (e, gammas))
  in
  match e with
  | Var v ->
    check_var_dom (Variable.get_locations v) v env ;
    (e, [])
  | Bind (va, v, a, e) ->
    try
      let pos = Variable.get_locations v in
      let res =
        try infer_a' pos tenv env a
        with Ill_typed _ -> (* BindDefUntypeable *)
          let a = empty_annots a in
          let (e, gammas) = infer' tenv env e in
          raise (Return (Bind (VarAnnot.empty, v, a, e), gammas))
      in
      begin match res with
      | (a, (_::_ as gammas)) -> (* BindDefNeedSplit *)
        (Bind (va, v, a, e), gammas)
      | (a, []) -> (* Bind *)
        let t = typeof_a pos tenv env a in
        let splits = VarAnnot.splits env va |> partition t in
        assert (disj splits |> subtype t) ;
        let (vas, res) = splits |>
          List.map (fun s -> infer_with_split tenv env s v a e) |>
          List.split
        in
        let (e, gammas) = merge_res res in
        (Bind (VarAnnot.union vas, v, a, e), gammas)
      end
    with Return r -> r

and infer_a' pos tenv env a =
  let rec infer_with_splits ~enforce_domain tenv env x e splits =
    let res = List.fold_left
      (fun acc s ->
        try (infer_with_split ~enforce_domain tenv env s x e)::acc
        with (Ill_typed _) as err -> begin
          if enforce_domain then raise err
          else acc
        end
      )
      [] splits
    in
    if res = []
    then raise (Ill_typed (pos, "Cannot infer the domain of this abstraction."))
    else res
  and infer_with_split ~enforce_domain tenv env s x e =
    let env' = Env.add x s env in
    match infer' tenv env' e with
    | (e, []) -> (VarAnnot.singleton env s, (e, [])) (* AbsSplitOk *)
    | (e, gammas) ->
      if List.for_all (fun gamma -> domain_included_in_singleton gamma x) gammas
      then (* AbsSplitTop *)
        let splits =
          List.map (fun gamma -> Env.find x (Env.cap gamma (Env.singleton x s))) gammas
          |> partition s in
        assert (disj splits |> subtype s) ;
        let res = infer_with_splits ~enforce_domain tenv env x e splits in
        let (vas, res) = List.split res in
        (VarAnnot.union vas, merge_res res)
      else (* AbsSplitUp *)
        let va = List.fold_left (fun acc gamma ->
              let gamma = Env.cap gamma (Env.singleton x s) in
              VarAnnot.add_split (Env.cap env (Env.rm x gamma)) (Env.find x gamma) acc
            ) VarAnnot.empty gammas
        in
        assert (VarAnnot.is_empty va |> not) ;
        let gammas = List.map (Env.rm x) gammas in
        (va, (e, gammas))
  in
  let type_lambda_with_splits ~enforce_domain lt tenv env splits x e =
    let t = match enforce_domain with
    (* NOTE: if splits are empty, we assume it's because it hasn't been set yet. *)
    | None -> if splits = [] then any else disj splits
    | Some t -> t
    in
    let splits = partition t splits in
    let enforce_domain = match enforce_domain with None -> false | _ -> true in
    (* Abs *)
    let res = infer_with_splits ~enforce_domain tenv env x e splits in
    let (vas, res) = List.split res in
    let (e, gammas) = merge_res res in
    (Lambda (VarAnnot.union vas, lt, x, e), gammas)
  in
  match a with
  | Abstract _ -> (a, [])
  | Const _ -> (a, [])
  | Debug (_, v) -> check_var_dom pos v env ; (a, [])
  | Pair (v1, v2) ->
    check_var_dom pos v1 env ; check_var_dom pos v2 env ; (a, [])
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (_, v) ->
    let t = var_type pos v env in
    if subtype t pair_any then begin
      match split_pair t with
      | [] -> (a, [])
      | [_] -> (a, [])
      | lst ->
        let gammas = lst |> List.map (fun (t1, t2) ->
          Env.singleton v (mk_times (cons t1) (cons t2))
        ) in
        (a, gammas)
    end else begin
      let t1 = cap t pair_any in
      let t2 = diff t pair_any in
      if is_empty t1 || is_empty t2
      then raise (Ill_typed (pos,
        "Bad domain for the projection. "^(actual_expected t pair_any)))
      else (
        let env1 = Env.singleton v t1 in
        let env2 = Env.singleton v t2 in
        (a, [env1;env2])
      )
    end
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) ->
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    if subtype t1 arrow_any then
      begin match split_arrow t1 with
      | [] -> (a, [])
      | [t1] ->
        begin match dnf t1 with
        | [arrows] ->
          if List.for_all (fun (s,_) -> subtype t2 s || disjoint t2 s) arrows
          then (a, [])
          else begin
            let dom = domain t1 in
            if subtype t2 dom
            then begin
              let gammas = arrows |> List.map (fun (s,_) -> cap s t2) |>
                List.filter (fun t2 -> is_empty t2 |> not) |>
                List.map (fun t2 -> Env.singleton v2 t2) in
              (a, gammas)
            end else begin
              let t2' = cap t2 dom in
              let t2'' = diff t2 dom in
              if is_empty t2' || is_empty t2''
              then raise (Ill_typed (pos,
                "Bad domain for the application. "^(actual_expected t2 dom)))
              else (
                let env1 = Env.singleton v2 t2' in
                let env2 = Env.singleton v2 t2'' in
                (a, [env1;env2])
              )
            end
          end
        | _ -> assert false
        end
      | lst ->
        let gammas = lst |> List.map (fun t1 -> Env.singleton v1 t1) in
        (a, gammas)
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
        (a, [env1;env2])
      )
    end
  | Ite (v, t, v1, v2) ->
    let tv = var_type pos v env in
    if is_empty tv
    then (a, [])
    else
      let t1 = cap tv t in
      let t2 = cap tv (neg t) in
      if is_empty t2
      then (check_var_dom pos v1 env ; (a, []))
      else if is_empty t1
      then (check_var_dom pos v2 env ; (a, []))
      else begin
        let env1 = Env.singleton v t1 in
        let env2 = Env.singleton v t2 in
        (a, [env1;env2])
      end
  | Lambda (va, (Ast.ADomain s as lt), v, e) ->
    let splits = VarAnnot.splits env va in
    type_lambda_with_splits ~enforce_domain:(Some s) lt tenv env splits v e
  | Lambda (va, (Ast.Unnanoted as lt), v, e) ->
    let splits = VarAnnot.splits env va in
    type_lambda_with_splits ~enforce_domain:None lt tenv env splits v e
  | Lambda (va, (Ast.AArrow t as lt), v, e) ->
    let splits = VarAnnot.splits env va in
    let left = dnf t |> List.map (List.map fst) |> List.flatten in
    let t = disj left in
    let splits = left@splits in
    type_lambda_with_splits ~enforce_domain:(Some t) lt tenv env splits v e
  | Let (v1, v2) ->
    check_var_dom pos v1 env ; check_var_dom pos v2 env ; (a, [])

let infer tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (VarAnnot.any, v, Abstract (var_type [] v env), acc)
  ) fv e in
  match infer' tenv Env.empty e with
  | (e, []) -> e
  | _ -> assert false

let typeof_simple tenv env e =
  let e = infer tenv env e in
  typeof tenv Env.empty e |> simplify_typ
