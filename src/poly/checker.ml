module PMsc = Msc
open Types.Base
open Types.Additions
open Common.Msc
open Annotations
open Annot
open Common
open Parsing.Variable
open Utils

(*
TODO: let rec (with optional type annotation for the whole definition)
TODO: non-inferred type vars (starts with _ ?) + fix scope of type variables
*)

exception Untypeable of Position.t list * string

(* ===== TYPEOF ===== *)
let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable v =
  raise (Untypeable (Variable.get_locations v, "Unbound variable "^(Variable.show v)^"."))
  
let var_type v env =
  if Env.mem v env then Env.find v env else unbound_variable v

let instantiate_check pos mono ss t =
  let check_s s =
    Subst.dom s |> TVarSet.inter mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instanciation: attempting to substitute a monomorphic variable."))

let rec typeof_a vardef tenv env mono annot_a a =
  let pos = Variable.get_locations vardef in
  let type_lambda env annot v e =
    if annot = []
    then raise (Untypeable (pos, "Invalid lambda: there must be at least 1 branch."))
    else
      annot |> List.map (fun (s, annot) ->
        let env = Env.add v s env in
        let mono = TVarSet.union mono (vars s) in
        let t = typeof_splits tenv env mono v annot e in
        mk_arrow (cons s) (cons t)
      ) |> conj_o
  in
  begin match a, annot_a with
  | Abstract t, NoneA -> t
  | Const c, NoneA -> typeof_const_atom tenv c
  | Pair (v1, v2), NoneA ->
    let t1 = var_type v1 env in
    let t2 = var_type v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v), ProjA ss ->
    let t = var_type v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      try get_field t label
      with Not_found ->
        raise (Untypeable (pos, "Invalid projection: missing label " ^ label ^ "."))
    else raise (Untypeable (pos, "Invalid projection: not a record."))
  | Projection (p, v), ProjA ss ->
    let t = var_type v env |> instantiate_check pos mono ss in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Untypeable (pos, "Invalid projection: not a pair."))
  | RecordUpdate (v, label, op), RecordUpdateA ss -> 
    let t = var_type v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      begin match op with
      | None -> remove_field t label
      | Some v' ->
        let t' = var_type v' env in
        let right_record = mk_record false [label, cons t'] in
        merge_records t right_record  
      end
    else raise (Untypeable (pos, "Invalid field update: not a record."))
  | App (v1, v2), AppA (ss1, ss2) ->
    let t1 = var_type v1 env |> instantiate_check pos mono ss1 in
    let t2 = var_type v2 env |> instantiate_check pos mono ss2 in
    if subtype t1 arrow_any
    then
      if subtype t2 (domain t1)
      then apply t1 t2
      else raise (Untypeable (pos, "Invalid application: argument not in the domain."))
    else raise (Untypeable (pos, "Invalid application: not a function."))
  | Ite (v, s, v1, v2), IteA ss ->
    let t = var_type v env |> instantiate_check pos mono ss in
    if is_empty t
    then empty
    else if subtype t s
    then var_type v1 env
    else if subtype t (neg s)
    then var_type v2 env
    else raise (Untypeable (pos, "Invalid typecase: multiple branches possible."))
  | Let (v1, v2), NoneA ->
    if Env.mem v1 env
    then var_type v2 env
    else raise (Untypeable (pos, "Invalid let binding: definition has been skipped."))
  | Lambda (_, Parsing.Ast.AArrow _, _, _), LambdaA _ ->
    raise (Untypeable (pos, "Invalid lambda: explicitely typed lambdas not supported."))
  | Lambda (_, _, v, e), LambdaA (annot, _) -> type_lambda env annot v e
  | _, _ -> raise (Untypeable (pos, "Invalid annotations."))
  end
  |> clean_poly_vars mono |> simplify_typ

and typeof_splits tenv env mono v splits e =
  let pos = Variable.get_locations v in
  if splits = []
  then raise (Untypeable (pos, "Invalid decomposition: cannot be empty."))
  else
    let dom = splits |> List.map fst |> disj in
    if subtype (Env.find v env) dom
    then splits |> List.map (fun (s, (_, annot)) ->
      let env = Env.strengthen v s env in
      let mono = TVarSet.union mono (vars s) in
      typeof tenv env mono annot e
    ) |> disj_o
    else raise (Untypeable (pos, "Invalid decomposition: does not cover the whole domain."))

and typeof tenv env mono annot e =
  begin match e, annot with
  | Var v, VarA -> var_type v env
  | Bind (_, v, a, e), DoA (annot_a, ty, annot_split) ->
    (* let t = typeof_a v tenv env mono annot_a a in
    let pos = Variable.get_locations v in
    let t =
      begin match ty with
      | None -> t
      | Some ty ->
        if subtype_poly mono t ty then ty
        else raise (Untypeable (pos, "Invalid type simplification."))
      end
    in *)
    let t = (* TODO: We are cheating... *)
      begin match ty with
      | None -> typeof_a v tenv env mono annot_a a
      | Some t -> t
      end in
    let env = Env.add v t env in
    typeof_splits tenv env mono v annot_split e
  | Bind (_, _, _, e), SkipA (annot) -> typeof tenv env mono annot e
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> clean_poly_vars mono |> simplify_typ

(* ===== REFINE ===== *)

let refine_a env mono a t = (* empty possibilites are often omitted *)
  match a with
  | Abstract _ | Const _ | Lambda _ -> []
  | Pair (v1, v2) ->
    split_pair t
    |> List.map (
      fun (t1, t2) -> Env.construct [(v1,t1) ; (v2, t2)]
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
        Env.construct [(v, ti) ; (x, field_type)]
      )
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    triangle_split_poly mono t1 t
    |> List.map (fun (t1, t2) -> Env.construct [(v1,t1);(v2,t2)])
  | Ite (v, s, v1, v2) ->
    [Env.construct [(v,s);(v1,t)] ; Env.construct [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ===== INFER ===== *)

let typeof_a_nofail vardef tenv env mono annot_a a =
  try typeof_a vardef tenv env mono annot_a a
  with Untypeable _ -> Format.printf "%a@." PMsc.pp_a a ; assert false

let typeof_nofail tenv env mono annot e =
  try typeof tenv env mono annot e
  with Untypeable _ -> Format.printf "%a@." PMsc.pp_e e ; assert false

type 'a result =
| Ok of 'a
| Split of (Env.t * 'a) list
| Subst of (Subst.t * 'a) list
| NeedVar of (Variable.t * 'a * 'a option)

let map_res' f res =
  match res with
  | Ok a -> Ok (f Subst.identity a)
  | Split lst ->
    Split (lst |> List.map (fun (e,a) -> (e, f Subst.identity a)))
  | Subst lst ->
    Subst (lst |> List.map (fun (s,a) -> (s, f s a)))
  | NeedVar (v, a, ao) ->
    NeedVar (v, f Subst.identity a, Option.map (f Subst.identity) ao)

let map_res f =
  map_res' (fun _ -> f)

let complete default_annot res =
  match res with
  | Subst lst ->
    if List.for_all (fun (sigma, _) -> Subst.is_identity sigma |> not) lst
    then Subst (lst@[Subst.identity, default_annot])
    else res
  | NeedVar (v, a, None) -> NeedVar (v, a, Some default_annot)
  | res -> res

let restore_name_of_mono_vars mono sol =
  let subst =
    List.fold_left (fun acc (v,t) ->
      if TVarSet.mem mono v |> not then acc
      else
        let expected_name = (var_name v)^(var_name v) in
        let renaming = top_vars t |>
          TVarSet.filter (fun v -> String.equal (var_name v) expected_name)
          |> TVarSet.destruct |> List.map (fun v' -> (v', var_typ v))
        in
        renaming@acc
      ) [] (Subst.destruct sol) |> Subst.construct in
  Subst.compose subst sol

let simplify_inference_solutions mono (r,r') to_maximize vars_to_use sols =
  log ~level:2 "Simplifying solutions...@." ;
  (* log "BEFORE:@.%a@." pp_substs sols ; *)
  let sols = sols |>
    List.filter_map (fun sol ->
      (* Simplify the monomorphic substitutions as most as we can
          (as long as it does not make the result too unprecise) *)
      let is_precise =
        if subtype_poly TVarSet.empty (Subst.find' sol r) (var_typ r')
        then (fun sol -> subtype_poly TVarSet.empty (Subst.find' sol r) (var_typ r'))
        else (fun _ -> true)
      in
      let sol =
        List.fold_left (fun sol v ->
          if TVarSet.mem mono v |> not then sol
          else
            let t = Subst.find' sol v in
            let constr = [(var_typ v, t);(t, var_typ v)] in
            (* print_tallying_instance [] mono constr ; *)
            let res = tallying mono constr
            |> List.map (fun res -> Subst.compose res sol)
            |> List.find_opt is_precise
            in
            match res with
            | None -> sol
            | Some sol -> Subst.rm v sol
          ) sol (Subst.dom sol |> TVarSet.destruct) in
      (* log "AFTER STEP 1:%a@." Subst.pp sol; *)
      (* Try to obtain the desired result *)
      let sol =
        let tr = Subst.find' sol r in
        let constr = [(tr, var_typ r')] in
        let mono = TVarSet.add r' mono in
        (* print_tallying_instance [] mono constr ; *)
        begin match tallying mono constr with
        | [] ->
          (* "Simplify" the result (or at least make it more deterministic) *)
          let poly_vars = TVarSet.diff (vars tr) mono in
          let subst = poly_vars |> TVarSet.destruct |> List.sort var_compare
          |> List.mapi (fun i v -> (v, vars_to_use i |> var_typ))
          |> Subst.construct in
          Subst.compose subst sol
        | res::_ ->
          (* log "SOLUTION:%a@." Subst.pp res ; *)
          let to_maximize = Subst.apply res tr in
          let clean = clean_type_ext ~pos:any ~neg:empty mono to_maximize in
          let res = Subst.compose clean res in
          Subst.compose res sol
        end
      in
      (* Remove a solution if it contains a substitution to empty for a mono var,
         or if it makes a to_maximize type empty *)
      if List.exists (fun (v,t') -> TVarSet.mem mono v && is_empty t')
        (Subst.destruct sol) then None
      else if to_maximize |> List.exists
        (fun t -> is_empty t |> not && Subst.apply sol t |> is_empty)
      then None
      else Some (restore_name_of_mono_vars mono sol)
      (* TODO: clean polymorphic variables so that it maximises to_maximize ? *)
    )
  in
  (* log "AFTER:@.%a@." pp_substs sols ; *)
  log ~level:2 "Solutions simplified!@." ; sols

let simplify_solutions mono result_var sols =
  let sols = sols |> List.filter_map (fun s ->
    let t = Subst.find' s result_var in
    let clean = clean_type_ext ~pos:empty ~neg:any mono t in
    let s = Subst.compose clean s in
    (* log "Res: %a@." pp_typ (Subst.find' s r) ; *)
    (* TODO: more simplifications ?? *)
    Some s
    ) in
  sols

let decorrelate_branches mono annot_a =
  let rename_vars (t, splits) =
    let new_vars = TVarSet.diff (vars t) mono in
    let subst = new_vars |> TVarSet.destruct |> List.map (fun v ->
      (v, mk_var (var_name v) |> var_typ)
    ) |> Subst.construct in
    (Subst.apply_simplify subst t, apply_subst_split subst splits)
  in
  match annot_a with
  | LambdaA (branches, []) ->
    LambdaA (List.map rename_vars branches, [])
  | LambdaA _ -> assert false
  | annot_a -> annot_a

exception NeedVarE of (Variable.t * string)
let need_var env v str =
  if Env.mem v env |> not
  then raise (NeedVarE (v, str))

let rec infer_a' vardef tenv env mono annot_a a =
  let need_var = need_var env in
  let simple_constraint_infer v str s r =
    need_var v str ;
    let t = Env.find v env in
    let result_var = (r, Variable.to_typevar vardef) in
    let to_maximize = [t] in
    let vars_to_use = Variable.get_typevar vardef in
    let (vs,tsubst,t) = fresh mono t in
    log ~level:1 "Inference: solving %a <= %a with delta=[]@."
      pp_typ t pp_typ s ;
    let poly = r::(vs |> TVarSet.destruct) in
    let res =
      tallying_infer poly TVarSet.empty [(t, s)]
      |> simplify_inference_solutions mono result_var to_maximize vars_to_use
      |> List.map (fun sol ->
      let mono_part = Subst.restrict sol mono in
      let poly_part = Subst.compose (Subst.restrict sol vs) tsubst in
      (mono_part, poly_part)
    ) |> regroup Subst.equiv
    in Subst res
  in
  let simple_constraint v str s r =
    need_var v str ;
    let t = Env.find v env in
    let (vs,tsubst,t) = fresh mono t in
    let res =
      tallying mono [(t, s)]
      |> simplify_solutions mono r
      |> List.map (fun sol -> Subst.compose (Subst.restrict sol vs) tsubst)
    in
    assert (res <> []) ; res
  in
  let app_constraints v1 v2 =
    need_var v1 "application" ;
    need_var v2 "application" ;
    let t1 = Env.find v1 env in
    let (vs1,subst1,t1) = fresh mono t1 in
    let t2 = Env.find v2 env in
    (* TODO: temporary... it seems to work better for typing things like fixpoint
        combinator and avoids trigerring a bug in Cduce implementation of tallying.
        But theoretically t1 and t2 should have independent polymorphic variables. *)
    let subst2 = Subst.restrict subst1 (vars t2) in
    let (vs2,subst2',t2) = fresh (TVarSet.union mono vs1) (Subst.apply subst2 t2) in
    let vs2 = TVarSet.inter (TVarSet.union vs2 vs1) (vars t2) in
    let subst2 = Subst.combine subst2 subst2' in
    (*let (vs2,subst2,t2) = fresh mono t2 in*)
    let alpha = fresh_var () in
    let arrow_typ = mk_arrow (cons t2) (cons (var_typ alpha)) in
    log ~level:1 "Application: solving %a <= %a@." pp_typ t1 pp_typ arrow_typ ;
    let constraints = [(t1, arrow_typ)] in
    (constraints,(vs1,subst1),(vs2,subst2),alpha)
  in
  let lambda v (branches1, branches2) e =
    log ~level:0 "Lambda for %s entered with %i non-explored branches:%a@."
      (Variable.show v) (List.length branches2) (pp_list pp_typ) (List.map fst branches2) ;
    (* Update finished branches *)
    let branches1 = branches1 |> List.map (fun (s, splits) ->
      let env = Env.add v s env in
      let mono = TVarSet.union mono (vars s) in
      match infer_splits' tenv env mono v splits e with
      | Ok splits -> (s, splits)
      | _ -> assert false
    ) in
    let domain_explored = branches1 |> List.map fst |> disj in
    (* Explore new branches *)
    let rec aux domain_explored branches =
      let branches = branches |> List.filter
        (fun (s,_) -> subtype s domain_explored |> not) in
      match branches with
      | [] -> Ok ([], [])
      | branches ->
        let f (s, _) others =
          List.for_all (fun (s', _) -> (subtype s' s |> not) || subtype s s') others
        in
        let ((s, splits), branches) = find_among_others f branches |> Option.get in
        let env = Env.add v s env in
        let vs = vars s in
        let xs = TVarSet.diff vs mono in
        let mono = TVarSet.union mono vs in
        log ~level:0 "Exploring branch %a for variable %s.@." pp_typ s (Variable.show v) ;
        begin match infer_splits' tenv env mono v splits e with
        | Ok splits ->
          aux (cup domain_explored s) branches
          |> map_res (fun (b1, b2) -> ((s, splits)::b1, b2))
        | Subst lst ->
          let res =
            lst |> List.map (fun (sigma, splits) ->
              (Subst.remove sigma xs, (Subst.apply_simplify sigma s, splits)))
            |> regroup Subst.equiv
          in
          Subst res |> map_res' (fun sigma splits ->
            ([], splits@(Annot.apply_subst_branches sigma branches)))
          |> complete ([], branches)
        | res ->
          map_res (fun splits -> ([], (s, splits)::branches)) res
          |> complete ([], branches)
        end
    in
    let res =
      aux domain_explored branches2 |> map_res' (fun s (b1, b2) ->
        let b1 = branches1@b1 |> apply_subst_branches s in
        LambdaA (b1, b2)
      ) in
    log ~level:0 "Lambda for %s exited.@." (Variable.show v) ; res
  in
  try match a, annot_a with
  | Abstract _, NoneA | Const _, NoneA -> Ok NoneA
  | Pair (v1, v2), NoneA | Let (v1, v2), NoneA ->
    need_var v1 "pair" ; need_var v2 "pair" ; Ok NoneA
  | Projection (Parsing.Ast.Field label, v), ProjA [] ->
    let alpha = fresh_var () in
    let s = mk_record true [label, alpha |> var_typ |> cons] in
    let res = simple_constraint_infer v "projection" s alpha in
    map_res (fun sigma -> ProjA sigma) res
  | Projection (Parsing.Ast.Field label, v), ProjA _ ->
    let alpha = fresh_var () in
    let s = mk_record true [label, alpha |> var_typ |> cons] in
    Ok (ProjA (simple_constraint v "projection" s alpha))
  | Projection (p, v), ProjA [] ->
    let alpha = fresh_var () in
    let s =
      if p = Parsing.Ast.Fst
      then mk_times (alpha |> var_typ |> cons) any_node
      else mk_times any_node (alpha |> var_typ |> cons)
    in
    let res = simple_constraint_infer v "projection" s alpha in
    map_res (fun sigma -> ProjA sigma) res
  | Projection (p, v), ProjA _ ->
    let alpha = fresh_var () in
    let s =
      if p = Parsing.Ast.Fst
      then mk_times (alpha |> var_typ |> cons) any_node
      else mk_times any_node (alpha |> var_typ |> cons)
    in
    Ok (ProjA (simple_constraint v "projection" s alpha))
  | RecordUpdate (v, _, o), RecordUpdateA [] ->
    (match o with None -> () | Some v' -> need_var v' "record update") ;
    let res = simple_constraint_infer v "record update" record_any (fresh_var ()) in
    map_res (fun sigma -> RecordUpdateA sigma) res
  | RecordUpdate (v, _, o), RecordUpdateA _ ->
    (match o with None -> () | Some v' -> need_var v' "record update") ;
    Ok (ProjA (simple_constraint v "record update" record_any (fresh_var ())))
  | App (v1, v2), AppA ([], []) ->
    let (constraints,(vs1,subst1),(vs2,subst2),alpha) = app_constraints v1 v2 in
    let poly = TVarSet.union vs1 vs2 |> TVarSet.destruct in
    let res =
      tallying_infer (alpha::poly) TVarSet.empty constraints
      |> simplify_inference_solutions mono (alpha, Variable.to_typevar vardef)
      [Env.find v1 env; Env.find v2 env] (Variable.get_typevar vardef)
      |> List.map (fun sol ->
      let poly1_part = Subst.compose (Subst.restrict sol vs1) subst1 in
      let poly2_part = Subst.compose (Subst.restrict sol vs2) subst2 in
      let mono_part = Subst.restrict sol mono in
      (* log ~level:0 "Poly1:@.%a@." Subst.pp (poly1_part) ;
      log ~level:0 "Poly2:@.%a@." Subst.pp (poly2_part) ; *)
      (* log ~level:0 "Mono:@.%a@." Subst.pp (mono_part) ; *)
      (* log ~level:0 "Result:@.%a@." pp_typ (Subst.find' sol alpha) ; *)
      (mono_part, (poly1_part, poly2_part))
    ) |> regroup Subst.equiv in
    Subst res |> map_res (fun sigmas -> AppA (List.split sigmas))
  | App (v1, v2), _ ->
    let (constraints,(vs1,subst1),(vs2,subst2),alpha) = app_constraints v1 v2 in
    let res =
      tallying mono constraints
      |> simplify_solutions mono alpha
      |> List.map (fun sol ->
        let poly1_part = Subst.compose (Subst.restrict sol vs1) subst1 in
        let poly2_part = Subst.compose (Subst.restrict sol vs2) subst2 in
        (poly1_part, poly2_part)
      )
    in
    (match res with [] -> assert false | res -> Ok (AppA (List.split res)))
  | Ite (v, s, _, _), IteA [] ->
    need_var v "typecase" ;
    let t = Env.find v env in
    if subtype t s || subtype t (neg s) then
      let poly = TVarSet.diff (vars t) mono in
      let res = tallying_infer (TVarSet.destruct poly) TVarSet.empty [(t, empty)]
        |> List.map (fun sol ->
        let sol = restore_name_of_mono_vars mono sol in
        let mono_part = Subst.restrict sol mono in
        let poly_part = Subst.restrict sol poly in
        (mono_part, poly_part)
      ) |> regroup Subst.equiv
      in
      map_res (fun sigma -> IteA sigma) (Subst res)
      |> complete (IteA [Subst.identity])
    else
      Split [(Env.singleton v s, IteA []) ; (Env.singleton v (neg s), IteA [])]
  | Ite (v, s, v1, v2), IteA sigma ->
    need_var v "typecase" ;
    let t = instantiate sigma (Env.find v env) in
    if is_empty t then Ok (IteA sigma)
    else if subtype t s then (need_var v1 "typecase" ; Ok (IteA sigma))
    else if subtype t (neg s) then (need_var v2 "typecase" ; Ok (IteA sigma))
    else assert false
      (*Split [(Env.singleton v s, IteA sigma) ; (Env.singleton v (neg s), IteA sigma)]*)
  | Lambda ((), _, v, e), LambdaA (b1,b2) ->
    (* log ~level:0 "Lambda for %s entered with %i raw unexplored branches:%a@."
    (Variable.show v) (List.length b2) (pp_list pp_typ) (List.map fst b2) ; *)
    if b1@b2 |> List.for_all (fun (s,_) -> is_empty s)
    then Subst [] else lambda v (b1,b2) e
  | _, _ -> assert false
  with NeedVarE (v, _) ->
    log ~level:1 "Variable %s needed. Going up.@." (Variable.show v) ;
    NeedVar (v, annot_a, None)

and infer_splits' tenv env mono v splits e =
  assert (splits <> []) ;
  let t = Env.find v env in
  let splits = match List.filter (fun (s, _) -> disjoint s t |> not) splits with
  | [] -> [List.hd splits]
  | splits -> splits
  in
  log ~level:1 "Splits for %s entered with %i branches:%a@."
    (Variable.show v) (List.length splits) (pp_list pp_typ) (List.map fst splits) ;
  let rec aux splits =
    match splits with
    | [] -> Ok []
    | (s, (b, annot))::splits ->
      let env = Env.strengthen v s env in
      assert (TVarSet.diff (vars s) mono |> TVarSet.is_empty) ;
      log ~level:1 "Exploring split %a for variable %s.@." pp_typ s (Variable.show v) ;
      begin match infer_iterated tenv env mono annot e with
      | Ok annot -> aux splits |> map_res' (fun sigma splits ->
        (Subst.apply_simplify sigma s,(b,Annot.apply_subst sigma annot))::splits)
      | Split lst ->
        let res =
          lst |> List.map (fun (env', annot) ->
            let b = b || Env.mem v env' in
            let env' = Env.strengthen v s env' in
            (Env.rm v env', (Env.find v env', (b, annot))))
          |> regroup Env.equiv
        in
        map_res (fun splits' -> splits'@splits) (Split res)
      | res -> res |> map_res' (fun sigma annot ->
        (Subst.apply_simplify sigma s,(b,annot))::(Annot.apply_subst_split sigma splits))
      end
  in
  let res = aux splits in
  log ~level:1 "Splits for %s exited.@." (Variable.show v) ; res

and infer' tenv env mono annot e =
  match e, annot with
  | Var v, VarA ->
    if Env.mem v env then Ok VarA
    else NeedVar (v, VarA, None)
  | Bind ((), v, a, e), SkipA annot ->
    begin match infer_iterated tenv env mono annot e with
    | NeedVar (v', annot, None) when Variable.equals v v' ->
      let split = [(any, (false, annot))] in
      let annot = DoA (Annot.initial_a a, None, split) in
      let e = Bind ((), v, a, e) in
      infer' tenv env mono annot e
    | NeedVar (v', annot, Some default) when Variable.equals v v' ->
      let split = [(any, (false, annot))] in
      let annot = DoSkipA (Annot.initial_a a, split, default) in
      let e = Bind ((), v, a, e) in
      infer' tenv env mono annot e
    | res -> map_res (fun annot -> SkipA annot) res
    end
  | Bind ((), v, a, e), DoSkipA (annot_a, splits, default) ->
    log ~level:1 "Trying to type definition for %s...@." (Variable.show v) ;
    begin match infer_a_iterated v tenv env mono annot_a a with
    | Ok annot_a ->
      let annot = DoA (annot_a, None, splits) in
      let e = Bind ((), v, a, e) in
      infer' tenv env mono annot e
    | res ->
      log ~level:1 "Definition of %s needs to go up (completed with default branch).@." (Variable.show v) ;
      let res = res |> map_res' (fun s annot_a ->
        DoSkipA (annot_a, apply_subst_split s splits, apply_subst s default)) in
      complete (SkipA default) res
    end
  | Bind ((), v, a, e), DoA (annot_a, _, splits) ->
    log ~level:1 "Typing definition for %s...@." (Variable.show v) ;
    begin match infer_a_iterated v tenv env mono annot_a a with
    | Ok annot_a ->
      let annot_a = decorrelate_branches mono annot_a in
      let t = typeof_a_nofail v tenv env mono annot_a a in
      let t = simplify_poly_typ mono t in
      log ~level:1 "Definition of %s typed: %a@." (Variable.show v) pp_typ t ;
      let rec after_def splits =
        let splits = List.map (fun (s,(b,a)) -> (s, (ref b, a))) splits in
        let refinements = splits |> List.find_map (fun (s,(b,_)) ->
          if disjoint s t || not !b then None
          else
            let refinements =
              refine_a env mono a (neg s) |> Refinements.partition
              |> Refinements.compatibles env
            in
            b := false ;
            if List.length refinements > 1
            then Some refinements
            else None
        ) in
        let splits = List.map (fun (s,(b,a)) -> (s,(!b, a))) splits in
        begin match refinements with
        | Some refinements ->
          log ~level:1 "Splits must be propagated for variable %s...@." (Variable.show v) ;
          Split (refinements |> List.map (fun envr -> (envr, DoA (annot_a, Some t, splits))))
        | None ->
          let env = Env.add v t env in
          begin match infer_splits' tenv env mono v splits e with
          | Split [(_, splits)] -> after_def splits (* Optimisation *)
          | res -> res |>
            map_res' (fun sigma splits -> DoA (apply_subst_a sigma annot_a, Some t, splits))
          end
        end  
      in
      after_def splits
    | res ->
      log ~level:1 "Definition of %s needs to go up.@." (Variable.show v) ;
      map_res' (fun s annot_a -> DoA (annot_a, None, apply_subst_split s splits)) res
    end
  | _, _ -> assert false

and infer_a_iterated vardef tenv env mono annot_a a =
  match infer_a' vardef tenv env mono annot_a a with
  | Split [(_, annot_a)] ->
    infer_a_iterated vardef tenv env mono annot_a a
  | Subst [(subst, annot_a)] when Subst.is_identity subst ->
    infer_a_iterated vardef tenv env mono annot_a a
  | res -> res

and infer_iterated tenv env mono annot e =
  match infer' tenv env mono annot e with
  | Split [(_, annot)] ->
    infer_iterated tenv env mono annot e
  | Subst [(subst, annot)] when Subst.is_identity subst ->
    infer_iterated tenv env mono annot e
  | res -> res

let infer tenv env mono e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind ((), v, Abstract (var_type v env), acc)
  ) fv e in
  if PMsc.contains_records e
  then raise (Untypeable ([], "Records unsupported by the polymorphic system."))
  else
    let annot =
      match infer_iterated tenv Env.empty mono (Annot.initial_e e) e with
      | Subst [] -> raise (Untypeable ([], "Annotations inference failed."))
      | Ok annot -> (e, annot)
      | _ -> assert false
    in
    log "@." ; annot  

let typeof_simple tenv env mono e =
  let (e, anns) = infer tenv env mono e in
  typeof_nofail tenv Env.empty mono anns e  
