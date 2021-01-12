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

(* TODO: Change implementation of the splits (can contain the empty type, etc) *)

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
  | Const (Atom str) -> get_type_or_atom tenv str
  | Const c -> Ast.const_to_typ c
  | Var v -> Env.find v env
  | Debug (_, v) -> Env.find v env
  | Pair (v1, v2) ->
    let t1 = Env.find v1 env in
    let t2 = Env.find v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (p, v) ->
    let t = Env.find v env in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Ill_typed (pos, "Projection can only be done on a pair."))
  | RecordUpdate _ -> failwith "Not implemented"
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    if subtype t1 arrow_any
    then
      let t2 = Env.find v2 env in
      let dom = domain t1 in
      if subtype t2 dom
      then apply t1 t2
      else raise (Ill_typed (pos,
        "Argument not in the domain of the function. "^(actual_expected t2 dom)))
    else raise (Ill_typed (pos, "Application can only be done on a function."))
  | Ite (v, t, x1, x2) ->
    let tv = Env.find v env in
    if subtype tv t
    then Env.find x1 env
    else if subtype tv (neg t)
    then Env.find x2 env
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

and typeof tenv env annots e =
  match e with
  | EVar v -> Env.find v env
  | Let (v, a, e) ->
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
  | Let (v, a) -> Env.cap (refine_a ~backward env a t) (Env.singleton v any)
  end
  |> List.map (fun env' -> List.fold_left
    (fun acc v -> Env.strengthen v (Env.find v env) acc)
    env' (Env.domain env')) (* Inter *)
  |> List.filter (fun env -> Env.contains_bottom env |> not) (* RemoveBottomEnv *)
  |> List.map (fun env' ->
    Env.filter (fun v t -> subtype (Env.find v env) t |> not) env'
    ) (* RemoveUselessVar *)

(* TODO: Update infer to match the new CBV system *)

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

(* TODO: Raise Ill_typed exception instead of Not_found when a variable is not in the env. *)
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
      then (* LetSplitTop *)
        let splits = List.map (fun env'' -> Env.find x env'') gammas1'
        |> Utils.remove_duplicates equiv in
        assert (disj splits |> subtype s) ;
        List.map (fun s -> infer_with_split tenv env annots' s x a e) splits |>
        merge_annotations Annotations.empty
      else (* LetSplitUp *)
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
  | EVar _ -> Result (Annotations.empty)
  | Let (v, a, e) ->
    try
      let pos = Variable.get_locations v in
      let annots1 = Annotations.restrict (bv_a a) annots in
      let annots2 = Annotations.restrict (bv_e e) annots in
      let res =
        try infer_a' pos tenv env annots1 a
        with Ill_typed _ -> (* LetAUntypeable *)
          raise (Return (infer' tenv env annots2 e))
      in
      begin match res with
      | NeedSplit (a,b,c) -> NeedSplit (a,b,c) (* LetANeedSplit *)
      | Result annots1' -> (* Let *)
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
          |> Utils.remove_duplicates equiv in
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
    splits |>
    List.map (fun s -> infer_with_split ~enforce_domain tenv env annots' s x e) |>
    merge_annotations Annotations.empty
  in
  match a with
  | Const _ -> Result (Annotations.empty)
  | Var _ -> Result (Annotations.empty)
  | Debug _ -> Result (Annotations.empty)
  | Pair _ -> Result (Annotations.empty)
  | Projection (Field _, _) -> failwith "Not implemented"
  | Projection (_, v) ->
    let t = Env.find v env in
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
    let t1 = Env.find v1 env in
    if subtype t1 arrow_any then
      begin match split_arrow t1 with
      | [] -> Result (Annotations.empty)
      | [t1] ->
        let t2 = Env.find v2 env in
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
  | Ite (v, t, _, _) ->
    let tv = Env.find v env in
    let t1 = cap tv t in
    let t2 = cap tv (neg t) in
    if is_empty t1 || is_empty t2
    then Result (Annotations.empty)
    else begin
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
      List.flatten |> Utils.remove_duplicates equiv |>
      List.map (fun s -> Annotations.splits v env ~initial:s annots) |>
      List.flatten |> Utils.remove_duplicates equiv
    in
    assert (disj splits |> subtype (domain t)) ;
    type_lambda_with_splits ~enforce_domain:true tenv env annots splits v e

let rec infer tenv env annots e =
  match infer' tenv env annots e with
  | Result annots -> [(env, annots)]
  | NeedSplit (annots, envs, _) ->
    envs |>
    List.map (fun env' -> infer tenv (Env.cap env env') annots e) |>
    List.flatten

let rec infer_a pos tenv env annots e =
  match infer_a' pos tenv env annots e with
  | Result annots -> [(env, annots)]
  | NeedSplit (annots, envs, _) ->
    envs |>
    List.map (fun env' -> infer_a pos tenv (Env.cap env env') annots e) |>
    List.flatten

let typeof_simple tenv env e =
  infer tenv env Annotations.empty e
  |> List.map (fun (env, annots) ->
    typeof tenv env annots e
  ) |> disj |> simplify_typ
