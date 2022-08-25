module PMsc = Msc
open Types.Base
open Types.Additions
open Common.Msc
open Annotations
open Annot
open Common
open Parsing.Variable
open Utils

exception Untypeable of Position.t list * string

(* ===== TYPEOF ===== *)

let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable pos v =
  raise (Untypeable (pos, "Unbound variable "^(Variable.show v)^"."))
  
let var_type pos v env =
  if Env.mem v env then Env.find v env else unbound_variable pos v

let instantiate_check pos mono ss t =
  let check_s s =
    Subst.dom s |> TVarSet.inter mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instanciation: attempting to substitute a monomorphic variable."))

let rec typeof_a pos tenv env mono annot_a a =
  let type_lambda env annot v e =
    if annot = []
    then raise (Untypeable (pos, "Invalid lambda: empty annotations."))
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
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v), ProjA ss ->
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      try get_field t label
      with Not_found ->
        raise (Untypeable (pos, "Invalid projection: missing label " ^ label ^ "."))
    else raise (Untypeable (pos, "Invalid projection: not a record."))
  | Projection (p, v), ProjA ss ->
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Untypeable (pos, "Invalid projection: not a pair."))
  | RecordUpdate (v, label, op), RecordUpdateA ss -> 
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if subtype t record_any
    then
      begin match op with
      | None -> remove_field t label
      | Some v' ->
        let t' = var_type pos v' env in
        let right_record = mk_record false [label, cons t'] in
        merge_records t right_record  
      end
    else raise (Untypeable (pos, "Invalid field update: not a record."))
  | App (v1, v2), AppA (ss1, ss2) ->
    let t1 = var_type pos v1 env |> instantiate_check pos mono ss1 in
    let t2 = var_type pos v2 env |> instantiate_check pos mono ss2 in
    if subtype t1 arrow_any
    then
      if subtype t2 (domain t1)
      then apply t1 t2
      else raise (Untypeable (pos, "Invalid application: argument not in the domain."))
    else raise (Untypeable (pos, "Invalid application: not a function."))
  | Ite (v, s, v1, v2), IteA ss ->
    let t = var_type pos v env |> instantiate_check pos mono ss in
    if is_empty t
    then empty
    else if subtype t s
    then var_type pos v1 env
    else if subtype t (neg s)
    then var_type pos v2 env
    else raise (Untypeable (pos, "Invalid typecase: multiple branches possible."))
  | Let (v1, v2), NoneA ->
    if Env.mem v1 env
    then var_type pos v2 env
    else raise (Untypeable (pos, "Invalid let binding: definition has been skipped."))
  | Lambda (_, Parsing.Ast.Unnanoted, v, e), LambdaA annot ->
    type_lambda env annot v e
  | Lambda (_, Parsing.Ast.ADomain dt, v, e), LambdaA annot ->
    let t = type_lambda env annot v e in
    if equiv (domain t) dt
    then t
    else raise (Untypeable (pos, "Invalid lambda: domain does not match with user annotation."))
  | Lambda (_, Parsing.Ast.AArrow t, v, e), LambdaA annot ->
    let t' = type_lambda env annot v e in
    if subtype t' t
    then t
    else raise (Untypeable (pos, "Invalid lambda: type does not match with user annotation."))
  | _, _ -> raise (Untypeable (pos, "Invalid annotations."))
  end
  |> hard_clean mono |> simplify_typ

and typeof_splits tenv env mono v splits e =
  let pos = Variable.get_locations v in
  let dom = splits |> List.map fst |> disj in
  if subtype (Env.find v env) dom
  then splits |> List.map (fun (s, (_, annot)) ->
    let env = Env.strengthen v s env in
    let mono = TVarSet.union mono (vars s) in
    typeof tenv env mono annot e
  ) |> disj_o
  else raise (Untypeable (pos, "Invalid split: does not cover the whole domain."))

and typeof tenv env mono annot e =
  begin match e, annot with
  | Var v, VarA -> var_type (Variable.get_locations v) v env
  | Bind (_, v, a, e), EmptyA (annot_a, annot) ->
    let t = typeof_a (Variable.get_locations v) tenv env mono annot_a a in
    let env = Env.add v t env in
    if is_empty t
    then typeof tenv env mono annot e
    else raise (Untypeable ([], "Invalid binding: does not cover the whole domain."))
  | Bind (_, v, a, e), DoA (_, annot_a, annot_split) ->
    let t = typeof_a (Variable.get_locations v) tenv env mono annot_a a in
    let env = Env.add v t env in
    typeof_splits tenv env mono v annot_split e
  | Bind (_, _, _, e), SkipA (annot) -> typeof tenv env mono annot e
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> hard_clean mono |> simplify_typ

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
    triangle_poly mono t1 t
    |> List.map (fun ti -> Env.singleton v2 ti)
  | Ite (v, s, v1, v2) ->
    [Env.construct [(v,s);(v1,t)] ; Env.construct [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ===== VAR DEPENDENCY ANALYZER ===== *)

let analyze_dependencies env e =
  (* TODO: Improve... *)
  let fv = Msc.fv_e e in
  let rec aux_a a =
    match a with
    | Abstract _ | Const _ -> (VarSet.empty, VarSet.empty)
    | App (v1, v2) | RecordUpdate (v1, _, Some v2) | Let (v1, v2) | Pair (v1, v2) ->
      let dep = VarSet.singleton v1 |> VarSet.add v2 in
      (dep, dep)
    | Projection (_, v) | RecordUpdate (v, _, None) ->
      (VarSet.singleton v, VarSet.singleton v)
    | Ite (v, s, v1, v2) ->
      if VarSet.mem v fv
      then
        if Env.mem v env
        then
          let t = Env.find v env in
          if is_empty t
          then (VarSet.singleton v, VarSet.singleton v)
          else if subtype t s
          then
            let dep = VarSet.singleton v |> VarSet.add v1 in
            (dep, dep)
          else if subtype t (neg s)
          then
            let dep = VarSet.singleton v |> VarSet.add v2 in
            (dep, dep)
          else (VarSet.singleton v, VarSet.singleton v (*|> VarSet.add v1 |> VarSet.add v2*))
        else (VarSet.singleton v, VarSet.singleton v)
      else (VarSet.singleton v, VarSet.singleton v |> VarSet.add v1 |> VarSet.add v2)
    | Lambda ((), _, _, e) -> aux e
  and aux e =
    match e with
    | Var v -> (VarSet.singleton v, VarSet.singleton v)
    | Bind ((), v, a, e) ->
      let (req, opt) = aux e in
      if VarSet.mem v opt
      then
        let (req_a, opt_a) = aux_a a in
        if VarSet.mem v req
        then (VarSet.union req req_a, VarSet.union opt opt_a)
        else (req, VarSet.union opt opt_a)
      else (req, opt)
  in
  aux e

(* ===== INFER ===== *)

let typeof_a_nofail pos tenv env mono annot_a a =
  try typeof_a pos tenv env mono annot_a a
  with Untypeable _ -> assert false

let typeof_nofail tenv env mono annot_a a =
  try typeof tenv env mono annot_a a
  with Untypeable _ -> assert false

type 'a result =
  | Ok of 'a
  | Split of (Env.t * 'a) list
  | Subst of (Subst.t * 'a) list

let fail = Subst []

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Split lst ->
    Split (lst |> List.map (fun (e,a) -> (e, f a)))
  | Subst lst ->
    Subst (lst |> List.map (fun (s,a) -> (s, f a)))

(* let complete default_annot res =
  match res with
  | Subst lst ->
    if List.for_all (fun (sigma, _) -> Subst.is_identity sigma |> not) lst
    then Subst ((Subst.identity, default_annot)::lst)
    else res
  | _ -> assert false *)

let complete_fine_grained default_annot res =
  match res with
  | Subst lst ->
    let substs = lst |> List.map fst in
    (* log "Initial: %a@." Annot.pp_substs substs ; *)
    let rec choose lst = match lst with
    | [] -> [[]]
    | subst::lst ->
      let res = choose lst in
      Subst.dom subst |> TVarSet.destruct |> List.map (fun x ->
        List.map (fun lst -> (x, Subst.find subst x)::lst) res
      ) |> List.flatten
    in
    let possibilities = choose substs in
    let defs =
      possibilities |> List.map (
        fun lst ->
          let parts = lst |> List.map (fun (v,t) ->
            let t = clean_type ~pos:any ~neg:empty TVarSet.empty t in
            if (vars t) |> TVarSet.is_empty
            then (v, neg t) else (v, any)
          ) in
          let parts = List.fold_left (fun acc (v,t) ->
              if List.mem_assoc v acc
              then
                let t' = List.assoc v acc in
                let acc = List.remove_assoc v acc in
                (v, cap_o t t')::acc
              else
                (v,t)::acc
            ) [] parts in
          let subst =
            parts
            |> List.map (fun (v,t) -> (v,cap t (var_typ v)))
            |> Subst.construct
          in
          (subst, default_annot)
      ) in
    let defs = if List.exists (fun (s,_) -> Subst.is_identity s) defs
      then [(Subst.identity, default_annot)] else defs in
    let are_dupl (s1,_) (s2,_) = Subst.equiv s1 s2 in
    let defs = remove_duplicates are_dupl defs in
    (* log "Added: %a@." Annot.pp_substs (List.map fst defs) ; *)
    Subst (defs@lst)
  | _ -> assert false

let simplify_tallying_result mono subst vres =
  (*Format.printf "Subst: %a@.Vres: %a@.Mono: %a@."
    Subst.pp subst pp_var vres TVarSet.pp mono ;*)
  (* TODO: Is this useful at all ??? *)
  (* let dom = Subst.dom subst in
  let keep =
    List.fold_left (fun mono v ->
      let t = Subst.find subst v in
      let name = (var_name v)^(var_name v) in
      let nmv = vars_with_polarity t
      |> List.filter_map (fun (v', pol) ->
        if var_name v' = name
        then match pol with
        | `Pos -> Some (v')
        | `Neg | `Both ->
          Format.printf "Unexpected tallying result cannot be simplified.@."
          ; None
        else None
        ) in
      TVarSet.union mono (TVarSet.construct nmv)
    ) mono (TVarSet.inter dom mono |> TVarSet.destruct) in
  let vt = vars (Subst.find' subst vres) in
  let keep =
    if TVarSet.inter vt keep |> TVarSet.is_empty
    then TVarSet.union vt keep else keep
  in
  let res =
    List.fold_left (fun res v ->
      let t = Subst.find subst v in
      let name = (var_name v)^(var_name v) in
      let ns = vars_with_polarity t
      |> List.filter_map (fun (v', pol) ->
        if not (TVarSet.mem keep v') && var_name v' = name
        then match pol with
        | `Pos -> Some (v', any)
        | `Neg | `Both ->
          Format.printf "Unexpected tallying result cannot be simplified.@."
          ; None
        else None
        ) in
      Subst.combine res (Subst.construct ns)
    ) Subst.identity (TVarSet.diff dom mono |> TVarSet.destruct)
  in *)
  (*Format.printf "Keep: %a@.Simplification: %a@." TVarSet.pp keep Subst.pp res ;*)
  let res = Subst.identity in ignore (mono, subst, vres) ;
  res

exception NeedVar of (Variable.t * string)
let need_var env v str =
  if Env.mem v env |> not
  then raise (NeedVar (v, str))

let rec infer_a' _ tenv env mono noninferred annot_a a =
  let need_var = need_var env in
  let simple_constraint_infer v str s resvar =
    need_var v str ;
    let (vs,tsubst,t) = fresh mono (Env.find v env) in
    let log_delta =
      TVarSet.inter noninferred (vars t) |> TVarSet.destruct in
    log ~level:1 "Simple constraint: solving %a <= %a with delta=%a@."
      pp_typ t pp_typ s (pp_list pp_var) log_delta ;
    let poly_t = vs |> TVarSet.destruct in
    let poly_s = TVarSet.diff (vars s) mono |> TVarSet.destruct in
    let res = tallying_infer (poly_s@poly_t) noninferred [(t, s)] in
    let res = res |> List.map (fun sol ->
      let simpl =
        match resvar with
        | None -> Subst.identity
        | Some resvar -> simplify_tallying_result mono sol resvar in
      let sol = Subst.compose_restr simpl sol in
      let mono_part = Subst.restrict sol mono in
      let poly_part = Subst.compose (Subst.restrict sol vs) tsubst in
      (mono_part, poly_part)
    ) |> regroup Subst.equiv in
    Subst res
  in
  let simple_constraint_check v str s sigma =
    need_var v str ;
    log ~level:1 "Simple constraint: checking substitutions...@." ;
    subtype (instantiate sigma (Env.find v env)) s
  in
  let lambda ~inferred v branches e =
    log ~level:0 "Lambda for %s entered with %i branches:%a@."
      (Variable.show v) (List.length branches) (pp_list pp_typ) (List.map fst branches) ;
    let rec aux branches =
      match branches with
      | [] -> Ok []
      | (s, splits)::branches ->
        begin match aux branches with
        | Ok (branches) ->
          let env = Env.add v s env in
          let vs = vars s in
          let xs = TVarSet.diff vs mono in
          let mono = TVarSet.union mono vs in
          let noninferred =
            if inferred then noninferred
            else TVarSet.union noninferred xs
          in
          begin match infer_splits' tenv env mono noninferred v splits e with
          | Subst lst ->
            let res =
              lst |> List.map (fun (sigma, splits) ->
                let sigmaxs = Subst.restrict sigma xs in
                (Subst.remove sigma xs,
                (Subst.apply_simplify sigmaxs s, Annot.apply_subst_split sigmaxs splits)))
              |> regroup Subst.equiv
            in
            map_res (fun splits -> splits@branches) (Subst res)
            |> complete_fine_grained branches
          | res -> map_res (fun splits -> (s, splits)::branches) res
          end
        | res -> map_res (fun branches -> (s, splits)::branches) res
        end  
    in
    let res = aux branches in
    log ~level:0 "Lambda for %s exited.@." (Variable.show v) ; res
  in
  try match a, annot_a with
  | Abstract _, NoneA | Const _, NoneA -> Ok NoneA
  | Pair (v1, v2), NoneA | Let (v1, v2), NoneA ->
    need_var v1 "pair" ; need_var v2 "pair" ; Ok NoneA
  | Projection (Parsing.Ast.Field label, v), ProjA [] ->
    let alpha = fresh_var () in
    let s = mk_record true [label, var_typ alpha |> cons] in
    let res = simple_constraint_infer v "projection" s (Some alpha) in
    map_res (fun sigma -> ProjA sigma) res
  | Projection (Parsing.Ast.Field label, v), ProjA sigma ->
    if simple_constraint_check v "projection" (record_any_with label) sigma
    then Ok (ProjA sigma) else assert false
  | Projection (p, v), ProjA [] ->
    let alpha = fresh_var () in
    let s =
      if p = Parsing.Ast.Fst
      then mk_times (var_typ alpha |> cons) any_node
      else mk_times any_node (var_typ alpha |> cons)
    in
    let res = simple_constraint_infer v "projection" s (Some alpha) in
    map_res (fun sigma -> ProjA sigma) res
  | Projection (_, v), ProjA sigma ->
    if simple_constraint_check v "projection" pair_any sigma
    then Ok (ProjA sigma) else assert false
  | RecordUpdate (v, _, o), RecordUpdateA [] ->
    (match o with None -> () | Some v' -> need_var v' "record update") ;
    let res = simple_constraint_infer v "record update" record_any None in
    map_res (fun sigma -> RecordUpdateA sigma) res
  | RecordUpdate (v, _, o), RecordUpdateA sigma ->
    (match o with None -> () | Some v' -> need_var v' "record update") ;
    if simple_constraint_check v "record update" record_any sigma
    then Ok (RecordUpdateA sigma) else assert false
  | App (v1, v2), AppA ([], []) ->
    need_var v1 "application" ;
    need_var v2 "application" ;
    let (vs1,subst1,t1) = fresh mono (Env.find v1 env) in
    (* TODO: temporary... it seems to work better for typing things like fixpoint
       and avoids trigerring a bug in Cduce implementation of tallying.
       But theoretically t1 and t2 should have independent polymorphic variables. *)
    let t2 = Env.find v2 env in
    let subst2 = Subst.restrict subst1 (vars t2) in
    let (vs2,subst2',t2) = fresh (TVarSet.union mono vs1) (Subst.apply subst2 t2) in
    let vs2 = TVarSet.inter (TVarSet.union vs2 vs1) (vars t2) in
    let subst2 = Subst.combine subst2 subst2' in
    (*let (vs2,subst2,t2) = fresh mono (Env.find v2 env) in*)
    let alpha = fresh_var () in
    let poly = TVarSet.union vs1 vs2 |> TVarSet.destruct in
    let arrow_typ = mk_arrow (cons t2) (cons (var_typ alpha)) in
    let log_delta =
      TVarSet.inter noninferred (TVarSet.union (vars t1) (vars arrow_typ))
      |> TVarSet.destruct in
    log ~level:1 "Application: solving %a <= %a with delta=%a@."
      pp_typ t1 pp_typ arrow_typ (pp_list pp_var) log_delta ;
    let res =
      tallying_infer (alpha::poly) noninferred [(t1, arrow_typ)]
      |> List.map (fun sol ->
      let simpl = simplify_tallying_result mono sol alpha in
      let sol = Subst.compose_restr simpl sol in
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
  | App (v1, v2), AppA (sigma1, sigma2) ->
    need_var v1 "application" ;
    need_var v2 "application" ;
    log ~level:1 "Application: checking substitutions...@." ;
    let t1 = instantiate sigma1 (Env.find v1 env) in
    let t2 = instantiate sigma2 (Env.find v2 env) in
    let arrow_type = (mk_arrow (cons t2) any_node) in
    if subtype t1 arrow_type
    then (Ok (AppA (sigma1, sigma2)))
    else (
      Format.printf "BEFORE INSTANCIATION@.t1:%a   ;   t2:%a@." pp_typ (Env.find v1 env) pp_typ (Env.find v2 env) ;
      Format.printf "AFTER INSTANCIATION@.t1:%a   ;   t2:%a@." pp_typ t1 pp_typ t2 ;
      assert false)
  | Ite (v, s, _, _), IteA [] ->
    need_var v "typecase" ;
    let t = Env.find v env in
    if subtype t s
    then
      let res = simple_constraint_infer v "typecase" (neg s) None in
      map_res (fun sigma -> IteA sigma) res
      |> complete_fine_grained (IteA [Subst.identity])
    else if subtype t (neg s) then
      let res = simple_constraint_infer v "typecase" s None in
      map_res (fun sigma -> IteA sigma) res
      |> complete_fine_grained (IteA [Subst.identity])
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
  | Lambda ((), ua, v, e), LambdaA branches ->
    let inferred = ua = Parsing.Ast.Unnanoted in
    let branches =
      if inferred then branches |>
        (* remove_empty_branches *)
        remove_redundant_branches mono
        |> List.map (fun (t,splits) ->
          let (subst, t) = remove_redundant_vars mono t in
          (t, Annot.apply_subst_split subst splits)
          )
      else branches in
    begin match branches with
    | [] ->
      log ~level:0 "Untypeable lambda for %s (no branch left).@." (Variable.show v) ;
      fail
    | branches ->
      lambda ~inferred v branches e
      |> map_res (fun branches -> LambdaA branches)
    end
  | _, _ -> assert false
  with
  | NeedVar (v, str) ->
    log ~level:0 "Untypeable %s (---> need %s)" (Variable.show v) str ; fail

and infer_splits' tenv env mono noninferred v splits e =
  let t = Env.find v env in
  let splits = splits |> List.filter (fun (s, _) -> disjoint s t |> not) in
  log ~level:2 "Splits for %s entered with %i branches:%a@."
    (Variable.show v) (List.length splits) (pp_list pp_typ) (List.map fst splits) ;
  let rec aux splits =
    match splits with
    | [] -> Ok []
    | (s, (b, annot))::splits ->
      begin match aux splits with
      | Ok (splits) ->
        let env = Env.strengthen v s env in
        let vs = vars s in
        let noninferred = TVarSet.union noninferred (TVarSet.diff vs mono) in
        let mono = TVarSet.union mono vs in
        begin match infer_iterated tenv env mono noninferred annot e with
        | Split lst ->
          let res =
            lst |> List.map (fun (env', annot) ->
              let b = b || Env.mem v env' in
              let env' = Env.strengthen v s env' in
              (Env.rm v env', (Env.find v env', (b, annot))))
            |> regroup Env.equiv
          in
          map_res (fun splits' -> splits'@splits) (Split res)
        | res -> map_res (fun annot -> (s,(b,annot))::splits) res
        end
      | res -> map_res (fun splits -> (s,(b,annot))::splits) res
      end
  in
  let res = aux splits in
  log ~level:2 "Splits for %s exited.@." (Variable.show v) ; res

and infer' tenv env mono noninferred annot e =
  match e, annot with
  | Var v, VarA ->
    if Env.mem v env then Ok(VarA)
    else (log ~level:0 "Untypeable expression (--> need %s)@." (Variable.show v) ; fail)
  | Bind ((), v, a, e), UnkA (annot_a, s, k1, k2) ->
    let pos = Variable.get_locations v in
    let (req, opt) = analyze_dependencies env e in
    (* Note: optimisation *)
    let skippable = VarSet.mem v req |> not in
    let skipped = skippable && (VarSet.mem v opt |> not) in
    (*let (skippable, skipped) = (skippable || true, skipped && false) in*)
    let res =
      if skipped then fail
      else begin
        log ~level:2 "(Re)Infering definition for %s...@." (Variable.show v) ;
        infer_a_iterated pos tenv env mono noninferred annot_a a
      end in
    begin match res, k1 with
    | Ok annot_a, _ ->
      let t = typeof_a_nofail pos tenv env mono annot_a a in
      log ~level:2 "Definition of %s typed: %a@." (Variable.show v) pp_typ t ;
      let e = Bind ((), v, a, e) in
      begin match s, k2, is_empty t with
      | _, Some annot, true ->
        let annot = EmptyA (annot_a, annot) in
        infer' tenv env mono noninferred annot e
      | Some splits, _, false ->
        let annot = DoA (t, annot_a, splits) in
        infer' tenv env mono noninferred annot e
      | _, _ , _->
        log ~level:0 "Definition %s is typeable, but its type cannot be handled.@."
          (Variable.show v) ; fail
      end
    | Subst lst, Some k1 when skippable ->
      log ~level:0 "The definition %s needs a substitution and is skippable. Adding a default branch...@."
        (Variable.show v);
      let res = (Subst lst) |> map_res (fun annot_a -> UnkA (annot_a, s, Some k1, k2)) in
      complete_fine_grained (SkipA k1) res
    | res, _ ->
      log ~level:2 "Definition of %s needs to go up.@." (Variable.show v) ;
      map_res (fun annot_a -> UnkA (annot_a, s, k1, k2)) res
    end
  | Bind ((), _, _, e), SkipA annot ->
    let res = infer_iterated tenv env mono noninferred annot e in
    map_res (fun annot -> SkipA annot) res
  | Bind ((), v, _, e), EmptyA (annot_a, annot) ->
    let env = Env.add v empty env in
    let res = infer_iterated tenv env mono noninferred annot e in
    map_res (fun annot -> EmptyA (annot_a, annot)) res
  | Bind ((), v, a, e), DoA (t, annot_a, splits) ->
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
      log ~level:2 "Splits must be propagated for variable %s...@." (Variable.show v) ;
      let res = refinements |> List.map (fun env' ->
        (env', DoA (t, annot_a, splits))) in
      Split res
    | None ->
      let env = Env.add v t env in
      let res = infer_splits' tenv env mono noninferred v splits e in
      map_res (fun splits -> DoA (t, annot_a, splits)) res
    end
  | _, _ -> assert false

and infer_a_iterated pos tenv env mono noninferred annot_a a =
  (*log ~level:3 "Iteration...@." ;*)
  match infer_a' pos tenv env mono noninferred annot_a a with
  | Split [(env', annot_a)] when Env.leq env env' ->
    infer_a_iterated pos tenv env mono noninferred annot_a a
  | Subst [(subst, annot_a)] when Subst.is_identity subst ->
    infer_a_iterated pos tenv env mono noninferred annot_a a
  | res -> res

and infer_iterated tenv env mono noninferred annot e =
  (*log ~level:3 "Iteration...@." ;*)
  match infer' tenv env mono noninferred annot e, e with
  | Split [(env', annot)], _ when Env.leq env env' ->
    infer_iterated tenv env mono noninferred annot e
  | Subst [(subst, annot)], _ when Subst.is_identity subst ->
    infer_iterated tenv env mono noninferred annot e
  | Split r, Bind (_, _, a, _) ->
    map_res (fun annot -> Annot.retype a annot) (Split r)
  | res, _ -> res

let infer tenv env mono e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind ((), v, Abstract (var_type [] v env), acc)
  ) fv e in
  if PMsc.contains_records e
  then raise (Untypeable ([], "Records unsupported by the polymorphic system."))
  else
    let annot =
      match infer_iterated tenv Env.empty mono mono (Annot.initial_e e) e with
      | Subst [] -> raise (Untypeable ([], "Annotations inference failed."))
      | Ok annot -> (e, annot)
      | _ -> assert false
    in
    log "@." ; annot

let typeof_simple tenv env mono e =
  let (e, anns) = infer tenv env mono e in
  typeof_nofail tenv Env.empty mono anns e  
