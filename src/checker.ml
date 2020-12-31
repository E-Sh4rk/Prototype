open Cduce
open Nf_ast
open Types_additions
open Annotations
open Variable

exception Ill_typed of Position.t list * string

let rec typeof_a pos tenv env annots a =
  if Env.is_bottom env
  then raise (Ill_typed (pos, "Environment contains a divergent variable."))
  else begin match a with
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
      then
        let res = apply t1 t2 in
        if is_empty res
        then raise (Ill_typed (pos, "This application always diverges."))
        else res
      else raise (Ill_typed (pos, "Argument not in the domain of the function."))
    else raise (Ill_typed (pos, "Application can only be done on a function."))
  | Ite (v, t, x1, x2) ->
    let tv = Env.find v env in
    if subtype tv t
    then Env.find x1 env
    else if subtype tv (neg t)
    then Env.find x2 env
    else raise (Ill_typed (pos, "Cannot select a branch for the typecase."))
  | Lambda (Ast.ADomain s, v, e) ->
    let splits = Annotations.splits v env ~initial:s annots in
    (* The splits are guaranteed not to contain the empty type *)
    if disj splits |> subtype s
    then
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        let res = typeof tenv env annots e in
        mk_arrow (cons t) (cons res)
      ) |> conj |> simplify_arrow
      (* NOTE: the intersection of non-empty arrows cannot be empty,
      thus no need to check the emptiness of the result *)
    else raise (Ill_typed (pos, "Invalid splits (does not cover the whole domain)."))
  | Lambda _ -> failwith "Not implemented"
  end

and typeof tenv env annots e =
  if Env.is_bottom env
  then raise (Ill_typed ([], "Environment contains a divergent variable."))
  else begin match e with
  | EVar v -> Env.find v env
  | Let (v, a, e) ->
    let pos = Variable.get_locations v in
    let s = typeof_a pos tenv env annots a in
    let splits = Annotations.splits v env ~initial:s annots in
    (* The splits are guaranteed not to contain the empty type *)
    if disj splits |> subtype s
    then
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        typeof tenv env annots e
      ) |> disj
    else raise (Ill_typed (pos, "Invalid splits (does not cover the whole domain)."))
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
  | Lambda (Ast.ADomain s, _, _) when backward ->
    if subtype (domain t) s then [Env.empty] else []
  | Lambda (Ast.ADomain _, _, _) -> []
  | Lambda _ -> failwith "Not implemented"
  end
  |> List.map (fun env' -> List.fold_left (fun acc v ->
    if Env.mem v env then Env.strengthen v (Env.find v env) acc else acc)
    env' (Env.domain env')) (* Inter *)
  |> List.filter (fun env -> Env.is_bottom env |> not) (* Normalize *)

type infer_res =
  | Result of Annotations.t
  | NeedSplit of Annotations.t * (Env.t list) * (Env.t list)

let merge_annotations res =
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
  List.map aux res |> split3 |>
  (fun (a,b,c) -> (Annotations.union a, List.concat b, List.concat c))

let is_result = function
  | Result _ -> true
  | NeedSplit _ -> false

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

let actual_expected act exp =
  Format.asprintf "Actual: %a - Expected: %a" pp_typ act pp_typ exp

let rec infer' tenv env annots e =
  let infer_with_split tenv env annots s x a e =
    let env' = Env.add x s env in
    match infer' tenv env' annots e with
    | Result annots' -> Result (Annotations.add_split x env s annots') (* LetSplitOk *)
    | NeedSplit (annots', gammas1, gammas2) ->
      let gammas1' = backward env' x a gammas1 in
      let gammas2' = forward env' x a gammas2 in
      let x_annots = List.fold_left (fun acc env' ->
        VarAnnot.add_split (Env.cap env (Env.rm x env')) (Env.find x env') acc
      ) VarAnnot.empty gammas1'
      in
      let annots'' = Annotations.add_var x x_annots annots' in
      if List.for_all (fun gamma' -> domain_included_in_singleton gamma' x) (gammas1'@gammas2')
      then (* LetSplitTop *)
        infer' tenv env annots'' (Let (x, a, e))
      else (* LetSplitUp *)
        let gammas1'' = List.map (Env.rm x) gammas1' in
        NeedSplit (annots'', gammas1'', gammas2')
  in
  match e with
  | EVar _ -> Result (Annotations.empty)
  | Let (v, a, e) ->
    let pos = Variable.get_locations v in
    let annots1 = Annotations.restrict (bv_a a) annots in
    begin match infer_a' pos tenv env annots1 a with
    | NeedSplit (a,b,c) -> NeedSplit (a,b,c) (* LetANeedSplit *)
    | Result annots1' -> (* Let *)
      let t = typeof_a pos tenv env annots1' a in
      let splits = Annotations.splits v env ~initial:t annots in
      let annots2 = Annotations.restrict (bv_e e) annots in
      let results = splits |>
        List.map (fun s -> infer_with_split tenv env annots2 s v a e)
      in
      let (uannots, ugammas1, ugammas2) = merge_annotations results in
      if List.for_all is_result results
      then Result (Annotations.cup annots1' uannots)
      else NeedSplit (Annotations.cup annots1' uannots, ugammas1, ugammas2)
    end

and infer_a' pos tenv env annots a =
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
    let infer_with_split tenv env annots s x e =
      let env' = Env.add x s env in
      match infer' tenv env' annots e with
      | Result annots' -> Result (Annotations.add_split x env s annots') (* AbsSplitOk *)
      | NeedSplit (annots', gammas1, gammas2) ->
        let x_annots1 = List.fold_left (fun acc env' ->
          let env'' = Env.cap env' (Env.singleton x s) in
          VarAnnot.add_split (Env.cap env (Env.rm x env'')) (Env.find x env'') acc
        ) VarAnnot.empty gammas1
        in
        let x_annots2 =
          List.filter (fun env' -> Env.mem x env') gammas2 |>
          List.fold_left (fun acc env' ->
            VarAnnot.add_split (Env.cap env (Env.rm x env')) (Env.find x env') acc
          ) VarAnnot.empty 
        in
        let annots'' = Annotations.add_var x (VarAnnot.cup x_annots1 x_annots2) annots' in
        if List.for_all (fun gamma' -> domain_included_in_singleton gamma' x) (gammas1@gammas2)
        then (* AbsSplitTop *)
          infer_a' pos tenv env annots'' (Lambda (Ast.ADomain s, v, e))
        else (* AbsSplitUp *)
          let gammas1' = List.map (Env.rm x) gammas1 in
          let gammas2' = List.map (Env.rm x) gammas2 in
          NeedSplit (annots'', gammas1', gammas2')
    in
    (* Abs *)
    let splits = Annotations.splits v env ~initial:s annots in
    let annots' = Annotations.restrict (bv_e e) annots in
    let results = splits |>
      List.map (fun s -> infer_with_split tenv env annots' s v e)
    in
    let (uannots, ugammas1, ugammas2) = merge_annotations results in
    if List.for_all is_result results
    then Result uannots
    else NeedSplit (uannots, ugammas1, ugammas2)
  | Lambda _ -> failwith "Not implemented"

(* TODO: in case of a NeedSplit below, just make the required split instead of failing. *)
let infer tenv env annots e =
  match infer' tenv env annots e with
  | Result annots -> annots
  | _ -> raise (Ill_typed ([], "Expression need a split for a free variable."))

let infer_a pos tenv env annots e =
  match infer_a' pos tenv env annots e with
  | Result annots -> annots
  | _ -> raise (Ill_typed (pos, "Expression need a split for a free variable."))

let typeof_simple tenv env e =
  let annots = infer tenv env Annotations.empty e in
  typeof tenv env annots e
