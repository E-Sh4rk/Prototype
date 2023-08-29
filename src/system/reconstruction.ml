open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations
open Utils
open Algorithmic
open Reconstruction_aux

(* ====================================== *)
(* =============== REFINE =============== *)
(* ====================================== *)

let rec is_undesirable s =
  subtype s arrow_any &&
  dnf s |> List.for_all
    (List.exists (fun (a, b) -> non_empty a && is_undesirable b))

let refine_a tenv env a t =
  log ~level:5 "refine_a@." ;
  match a with
  | Lambda _ -> []
  | Abstract t' when subtype t' t -> [Env.empty]
  | Const c when subtype (typeof_const_atom tenv c) t -> [Env.empty] 
  | Alias v when subtype (Env.find v env) t -> [Env.empty]
  | Alias _ | Abstract _ | Const _ -> []
  | Pair (v1, v2) ->
    let t = cap t pair_any in
    split_typ t
    |> List.filter (fun t -> top_vars t |> TVarSet.is_empty)
    |> List.map (
      fun ti -> Env.construct_dup [(v1, pi1 ti) ; (v2, pi2 ti)]
    )
  | Projection (Fst, v) -> [Env.singleton v (mk_times (cons t) any_node)]
  | Projection (Snd, v) -> [Env.singleton v (mk_times any_node (cons t))]
  | Projection (Field label, v) ->
    [Env.singleton v (mk_record true [(label, cons t)])]
  | RecordUpdate (v, label, None) ->
    let t = cap t (record_any_without label) in
    split_typ t
    |> List.filter (fun t -> top_vars t |> TVarSet.is_empty)
    |> List.map (
      fun ti -> Env.singleton v (remove_field_info ti label)
    )
  | RecordUpdate (v, label, Some x) ->
    let t = cap t (record_any_with label) in
    split_typ t
    |> List.filter (fun t -> top_vars t |> TVarSet.is_empty)
    |> List.map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        Env.construct_dup [(v, ti) ; (x, field_type)]
      )
  | TypeConstr (v, _) -> [Env.singleton v t]
  | App (v1, v2) ->
    let alpha = TVar.mk_poly None in
    let dnf = Env.find v1 env |> dnf in
    dnf |> List.map (
      fun arrows ->
        let t1 = branch_type arrows in
        let constr = [ (t1, mk_arrow (TVar.typ alpha |> cons) (cons t)) ] in
        let res = tallying constr in
        let pvars = ref TVarSet.empty in
        let res =
          res |> List.map (fun sol ->
            let t1 = apply_subst_simplify sol t1 in
            let t2 = Subst.find' sol alpha in
            let clean_subst = clean_type_subst ~pos:any ~neg:empty t2 in
            let t1 = Subst.apply clean_subst t1 in
            let t2 = Subst.apply clean_subst t2 in
            pvars := TVarSet.union !pvars (vars_poly t1) ;
            pvars := TVarSet.union !pvars (vars_poly t2) ;
            if List.length dnf <= 1
            then Env.singleton v2 t2
            else Env.construct_dup [(v1, t1) ; (v2, t2)]
          )
        in
        let mono = monomorphize !pvars in
        res |> List.map (fun env ->
          Env.apply_subst mono env
        )
    )
    |> List.flatten
    |> List.filter (fun env -> Env.bindings env |>
        List.for_all (fun (_,t) -> not (is_undesirable t)))
  | Ite (v, s, v1, v2) ->
    [Env.construct_dup [(v,s);(v1,t)] ; Env.construct_dup [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ====================================== *)
(* ============ MAIN SYSTEM ============= *)
(* ====================================== *)

type 'a res =
  | Ok of 'a
  | Fail
  | Split of Env.t * 'a * 'a
  | Subst of (Env.t * bool (* Low priority default *)) * Subst.t list * 'a * 'a
  | NeedVar of Variable.t * 'a * 'a

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Fail -> Fail
  | Split (env, a1, a2) -> Split (env, f a1, f a2)
  | Subst (info, ss, a1, a2) -> Subst (info, ss, f a1, f a2)
  | NeedVar (v, a1, a2) -> NeedVar (v, f a1, f a2)

let is_compatible env gamma =
  VarSet.subset
    (Env.domain gamma |> VarSet.of_list)
    (Env.domain env |> VarSet.of_list)
  &&
  Env.bindings gamma |> List.for_all (fun (v,s) ->
    let t = Env.find v env in
    is_empty t || (cap t s |> non_empty)
  )

let subst_more_general s1 s2 =
  let s2m = Subst.codom s2 |> monomorphize in
  Subst.destruct s1 |> List.map (fun (v,t1) ->
    let t2 = Subst.find' s2 v in
    let t2 = Subst.apply s2m t2 in
    [(t1, t2) ; (t2, t1)]
  ) |> List.flatten |> test_tallying
let subst_nb_new_vars s =
  let codom = Subst.codom s |> TVarSet.destruct |> List.length in
  let dom = Subst.dom s |> TVarSet.destruct |> List.length in
  codom - dom

let generalize_inferable tvars =
  let tvars = TVarSet.filter TVar.can_infer tvars in
  generalize tvars

let res_var = TVar.mk_mono None
let res_var_p = TVar.mk_poly None
let simplify_tallying_infer env res_type sols =
  let tvars = Env.tvars env |> TVarSet.filter TVar.is_mono in
  let params_types = Env.domain env |>
    List.filter Variable.is_lambda_var |>
    List.map (fun v -> Env.find v env)
  in
  let vars_involved dom sol =
    let sol = Subst.restrict sol dom in
    TVarSet.union (Subst.codom sol) dom
  in
  let better_sol (sol1, res1) (sol2, res2) =
    let nb1, nb2 = subst_nb_new_vars sol1, subst_nb_new_vars sol2 in
    let respart1 = Subst.construct [(res_var, cup res1 (TVar.typ res_var_p))] in
    let respart2 = Subst.construct [(res_var, res2)] in
    let sol1, sol2 = Subst.combine sol1 respart1, Subst.combine sol2 respart2 in
    let sol1 = Subst.compose_restr (Subst.codom sol1 |> generalize) sol1 in
    nb1 <= nb2 && subst_more_general sol1 sol2
  in
  let is_minimal_sol (_,r) ss =
    let r = Subst.apply (vars r |> generalize) r in
    ss |> List.for_all (fun (_,r') ->
      let r' = Subst.apply (vars r' |> generalize) r' in
      subtype_poly r r' || not (subtype_poly r' r)
    )
  in
  let rec order sols =
    match find_among_others is_minimal_sol sols with
    | None -> sols
    | Some (h, sols) -> h::(order sols)
  in
  sols
  (* Restrict to tvars and store result *)
  |> List.map (fun sol ->
    let res = Subst.apply sol res_type in
    let sol = Subst.restrict sol tvars in
    (sol, res)
  )
  (* Generalize vars in the result when possible *)
  |> List.map (fun (sol, res) ->
    let mono = vars_involved tvars sol in
    let gen = generalize_inferable (TVarSet.diff (vars res) mono) in
    let sol, res = Subst.compose_restr gen sol, Subst.apply gen res in
    let clean = clean_type_subst ~pos:empty ~neg:any res in
    (Subst.compose_restr clean sol, Subst.apply clean res)
  )
  (* Remove solutions that require "undesirable" lambda branches *)
  |> List.filter (fun (sol, _) ->
    params_types |> List.for_all (fun t ->
      TVarSet.inter (vars_mono t) (Subst.dom sol) |> TVarSet.is_empty ||
      is_undesirable t || not (is_undesirable (Subst.apply sol t))
    )
  )
  (* Simplify *)
  |> List.map (fun (sol, res) ->
    List.fold_left (fun (sol, res) v ->
      let t = Subst.find' sol v in
      (* let v = TVar.mk_fresh v in *)
      (* NOTE: we allow to rename mono vars even if it corresponds to a
         mono var already in the env (tvars)...
         this might create an uneeded correlation but it simplifies a lot. *)
      let s = replace_vars t (top_vars t |> TVarSet.filter TVar.can_infer) v in
      (Subst.restrict (Subst.compose s sol) tvars, Subst.apply s res)
    ) (sol, res) (Subst.dom sol |> TVarSet.destruct)
  )
  (* Try remove var substitutions *)
  |> List.map (fun (sol, res) ->
    List.fold_left (fun (sol, res) v ->
      let t = Subst.find' sol v in
      let mono = vars_involved (TVarSet.rm v tvars) sol in
      let pvs = TVarSet.diff (vars t) mono in
      let g = generalize_inferable pvs in
      let t = Subst.apply g t in
      let tallying_res = tallying [(TVar.typ v, t) ; (t, TVar.typ v)]
      |> List.map (fun s ->
        let s = Subst.compose_restr s g in
        Subst.compose_restr (Subst.codom s |> monomorphize) s
      )
      |> List.filter (fun s ->
        let res' = Subst.apply s res in
        let res' = Subst.apply (vars res' |> generalize) res' in
        subtype_poly res' res
      )
      in
      match tallying_res with
      | [] -> (sol, res)
      | s::_ -> (Subst.rm v sol, Subst.apply s res)  
    ) (sol, res) (Subst.dom sol |> TVarSet.destruct)
  )
  (* Regroup equivalent solutions *)
  |> regroup_equiv (fun (s1, _) (s2, _) -> Subst.equiv s1 s2)
  |> List.map (fun to_merge ->
    let sol = List.hd to_merge |> fst in
    (* conj instead of conj_o, because in some cases it can be very complex types
        without being used later (e.g. when there is no tvar to infer) *)
    let res = List.map snd to_merge |> conj in
    (sol, res)
  )
  (* Remove "less general" solutions *)
  |> keep_only_minimal better_sol
  (* Order solutions (more precise results first) *)
  |> order |> List.map fst
  (* Printing (debug) *)
  (* |> (fun res ->
    Format.printf "=== Solutions ===@." ;
    Format.printf "with tvars=%a@." TVarSet.pp tvars ;
    res |> List.iter (fun s -> Format.printf "%a@." Subst.pp s) ;
    res
  ) *)

let infer_mono_inter expl' env infer_branch typeof (b1, b2, (expl, tf,ud)) =
  let tvars = env |> Env.filter (fun x _ -> Variable.is_lambda_var x) |> Env.tvars in
  let tvars = TVarSet.filter TVar.is_mono tvars in
  let uNb = List.length b1 and eNb = List.length b2 in
  let nontrivial = uNb + eNb > 1 in
  if nontrivial then begin
    log ~level:0 "Typing intersection with %n unexplored branches (and %n explored).@." uNb eNb
  end ;
  let subtype_gen a b =
    let a = Subst.apply (TVarSet.diff (vars a) tvars |> generalize) a in
    subtype_poly a b
  in
  let rec aux explored expl pending =
    match pending with
    | [] when explored = [] -> log ~level:3 "Intersection generated a fail (0 branch)@." ; Fail
    | [] ->
      let explored =
        if tf || ud || List.length explored <= 1 then explored
        else (
          log ~level:5 "Finished reconstructing intersection. Typing it..." ;
          explored
          (* We type each branch and remove useless ones *)
          |> List.map (fun pannot ->
            (pannot, typeof pannot)
          )
          |> (fun r -> log ~level:5 "Simplifying it...@." ; r)
          (* |> List.map (fun (a, t) -> log ~level:5 "%a@.@." pp_typ t ; (a,t)) *)
          |> Utils.filter_among_others
          (fun (_,ty) others ->
            let ty' = others |> List.map snd |> conj in
            subtype_gen ty' ty |> not
          )
          |> (fun r -> log ~level:5 "Done.@." ; r)
          (* |> List.map (fun (a, t) -> log ~level:5 "%a@.@." pp_typ t ; (a,t)) *)
          |> List.map fst
        )
      in
      Ok ([], explored, (expl, true, ud))
    | (pannot, est, lpd)::pending ->
      (* Remove branch if it is estimated not to add anything *)
      let expl' = Domains.cup expl expl' in
      if not ud && Domains.covers expl' est then aux explored expl pending
      else begin
        (* NOTE: the order matters (priority to the first) *)
        if nontrivial then (
          log ~level:3 "Exploring intersection issued from %a@." Domains.pp est
        ) ;
        let res = infer_branch expl' pannot in
        match res with
        | Ok pannot ->
          log ~level:3 "Success of intersection issued from %a@." Domains.pp est;
          (* Remove low-priority default branches *)
          let pending = pending |> List.filter (fun (_,_,lpd) -> not lpd) in
          aux (pannot::explored) (Domains.cup expl est) pending
        | Fail when not ud && (explored <> [] || pending <> []) ->
          log ~level:3 "Failure of intersection issued from %a@." Domains.pp est;
          aux explored (Domains.cup expl est) pending
        | res ->
          log ~level:3 "Backtracking for intersection issued from %a@." Domains.pp est;
          map_res (fun x -> ((x,est,lpd)::pending, explored, (expl,tf,ud))) res
      end
  in
  aux b2 expl b1

let merge_substs tvars tvars_branch apply_subst_branch mk_inter
  ((d,lpd), lst, pannot, default) =
  let refresh b =
    let tvs = TVarSet.diff (tvars_branch b) tvars |> TVarSet.filter TVar.can_infer in
    apply_subst_branch (refresh tvs) b
  in
  let lst = lst
    |> List.map (fun s -> (apply_subst_branch s pannot, Env.apply_subst s d))
    |> List.map (fun (b, d) -> (refresh b, Domains.singleton d, false))
  in
  log ~level:2 "@.Creating an intersection with %n branches.@." (List.length lst + 1) ;
  (* NOTE: It is important for the default case to be inserted at the end (smaller priority). *)
  mk_inter (lst@[default, Domains.singleton d, lpd]) [] (Domains.empty,false,false)

let should_iterate env tvars_branch apply_subst_branch mk_inter res =
  match res with
  | Split (gamma, pannot, _) when Env.is_empty gamma -> Some pannot
  | Subst (info, lst, pannot, default) ->
    let tvars = Env.tvars env |> TVarSet.filter TVar.is_mono in
    if lst |> List.for_all (fun s -> TVarSet.inter (Subst.dom s) tvars |> TVarSet.is_empty)
    then Some (merge_substs tvars tvars_branch apply_subst_branch mk_inter
                (info, lst, pannot, default))
    else None
  | _ -> None

let rec infer_mono_a vardef tenv expl env pannot_a a =
  let memvar v = Env.mem v env in
  let vartype v = Env.find v env in
  let needvar v a1 a2 = NeedVar (v, a1, a2) in
  (* TODO: enable the lpd flag? (prune some uninteresting branches) *)
  let needsubst ss a1 a2 = Subst ((env, (*true*) false), ss, a1, a2) in
  let needsubst_no_lpd ss a1 a2 = Subst ((env, false), ss, a1, a2) in
  let open PartialAnnot in
  match a, pannot_a with
  | a, InterA i ->
    infer_mono_inter
      expl env
      (fun expl pannot_a -> infer_mono_a_iterated vardef tenv expl env pannot_a a)
      (fun pannot_a ->
        let annot_a = infer_poly_a vardef tenv env pannot_a a in
        typeof_a vardef tenv env annot_a a)
      i
    |> map_res (fun x -> InterA x)
  | _, TypA -> Ok (TypA)
  | _, EmptyA -> Ok (EmptyA)
  | _, ThenA -> Ok (ThenA)
  | _, ElseA -> Ok (ElseA)
  | _, UntypA -> log ~level:3 "Untyp annot generated a fail.@." ; Fail
  | Alias v, InferA when memvar v -> Ok (TypA)
  | Alias v, InferA -> log ~level:3 "Unknown var %s generated a fail.@." (Variable.show v) ; Fail
  | Abstract _, InferA | Const _, InferA -> Ok (TypA)
  | Pair (v1, v2), InferA | Let (v1, v2), InferA ->
    if memvar v1 |> not
    then needvar v1 InferA UntypA
    else if memvar v2 |> not
    then needvar v2 InferA UntypA
    else Ok TypA
  | Projection (p, v), InferA ->
    if memvar v then
      let t = vartype v in
      let alpha = TVar.mk_mono (Some (Variable.show vardef)) in
      let s =
        begin match p with
        | Parsing.Ast.Field label ->
          mk_record true [label, TVar.typ alpha |> cons]
        | Parsing.Ast.Fst ->
          mk_times (TVar.typ alpha |> cons) any_node
        | Parsing.Ast.Snd ->
          mk_times any_node (TVar.typ alpha |> cons)
        end
      in
      log ~level:3 "@.Tallying (inference) for %a: %a <= %a@."
        Variable.pp vardef pp_typ t pp_typ s ;
      let res = tallying_infer [(t, s)] in
      res |> List.iter (fun s ->
        log ~level:3 "Solution: %a@." Subst.pp s
      ) ;
      let res = simplify_tallying_infer env (TVar.typ alpha) res in
      res |> List.iter (fun s ->
        log ~level:3 "Solution (simplified): %a@." Subst.pp s
      ) ;
      needsubst res TypA UntypA
    else
      needvar v InferA UntypA
  | RecordUpdate (v, _, None), InferA ->
    if memvar v then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      needsubst res TypA UntypA
    else
      needvar v InferA UntypA
  | RecordUpdate (v, _, Some v'), InferA ->
    if memvar v |> not
    then needvar v InferA UntypA
    else if memvar v' |> not
    then needvar v' InferA UntypA
    else
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      needsubst res TypA UntypA
  | TypeConstr (v, s), InferA ->
    if memvar v then
      let res = tallying_infer [(vartype v, s)] in
      let res = simplify_tallying_infer env empty res in
      needsubst res TypA UntypA
    else
      needvar v InferA UntypA
  | App (v1, v2), InferA ->
    if memvar v1 |> not
    then needvar v1 InferA UntypA
    else if memvar v2 |> not
    then needvar v2 InferA UntypA
    else
      let t1 = vartype v1 in
      let t2 = vartype v2 in
      let alpha = TVar.mk_mono (Some (Variable.show vardef)) in
      let arrow_type = mk_arrow (cons t2) (TVar.typ alpha |> cons) in
      log ~level:3 "@.Approximate tallying (inference) for %a: %a <= %a@."
        Variable.pp vardef pp_typ t1 pp_typ arrow_type ;
      let res = approximate_app ~infer:true t1 t2 alpha in
      res |> List.iter (fun s ->
        log ~level:3 "Solution: %a@." Subst.pp s
      ) ;
      let res = simplify_tallying_infer env (TVar.typ alpha) res in
      res |> List.iter (fun s ->
        log ~level:3 "Solution (simplified): %a@." Subst.pp s
      ) ;
      needsubst res TypA UntypA
  | Ite (v, tau, _, _), InferA ->
    if memvar v then
      let t = vartype v in
      if subtype t empty then Ok EmptyA
      else if subtype t tau
      then
        let res = tallying_infer [(t, empty)] in
        let res = simplify_tallying_infer env empty res in
        if List.exists Subst.is_identity res
        then Ok EmptyA
        else needsubst_no_lpd res EmptyA ThenVarA
      else if subtype t (neg tau)
      then
        let res = tallying_infer [(t, empty)] in
        let res = simplify_tallying_infer env empty res in
        if List.exists Subst.is_identity res
        then Ok EmptyA
        else needsubst_no_lpd res EmptyA ElseVarA
      else Split (Env.singleton v tau, InferA, InferA)
    else needvar v InferA UntypA
  | Ite (_, _, v1, _), ThenVarA ->
    if memvar v1 then Ok ThenA else needvar v1 ThenA UntypA
  | Ite (_, _, _, v2), ElseVarA ->
    if memvar v2 then Ok ElseA else needvar v2 ElseA UntypA
  | Lambda (Unnanoted, _, _), InferA ->
    let alpha = TVar.mk_mono (Some (Variable.show vardef)) |> TVar.typ in
    let pannot_a = LambdaA (alpha, Infer) in
    infer_mono_a vardef tenv expl env pannot_a a
  | Lambda (ADomain ts, _, _), InferA ->
    let branches = ts |> List.map (fun t ->
      let pannot_a = LambdaA (t, Infer) in
      (pannot_a, expl, false)
    ) in
    let pannot_a = InterA (branches, [], (Domains.empty, false, true)) in
    infer_mono_a vardef tenv expl env pannot_a a
  | Lambda (_, v, e), LambdaA (s, pannot) ->
    log ~level:2 "Entering lambda for %a with domain %a.@." Variable.pp v pp_typ s ;
    if is_empty s then (log ~level:3 "Lambda with empty domain generated a fail.@." ; Fail)
    else
      let env = Env.add v s env in
      infer_mono_iterated tenv (Domains.enter_lambda env expl) env pannot e
      |> map_res (fun x -> LambdaA (s, x))
  | _, _ -> assert false

and infer_mono tenv expl env pannot e =
  let memvar v = Env.mem v env in
  let needvar v a1 a2 = NeedVar (v, a1, a2) in
  let open PartialAnnot in
  match e, pannot with
  | _, Untyp -> log ~level:3 "Untyp annot generated a fail.@." ; Fail
  | _, Typ -> Ok Typ
  | Var v, Infer ->
    if memvar v then Ok Typ else needvar v Infer Untyp
  | Bind _, Inter i ->
    infer_mono_inter
      expl env
      (fun expl pannot -> infer_mono_iterated tenv expl env pannot e)
      (fun pannot ->
        let annot = infer_poly tenv env pannot e in
        typeof tenv env annot e)
      i
    |> map_res (fun x -> Inter x)
  | Bind _, Infer -> infer_mono tenv expl env (TrySkip Infer) e
  | Bind (v, _, e) as ee, TrySkip pannot ->
    begin match infer_mono_iterated tenv expl env pannot e with
    | NeedVar (v', pannot1, pannot2) when Variable.equals v v' ->
      log ~level:0 "Var %a needed.@." Variable.pp v ;
      infer_mono tenv expl env (TryKeep (InferA, pannot1, pannot2)) ee
    | Ok pannot -> Ok (Skip pannot)
    | res -> map_res (fun x -> TrySkip x) res
    end
  | Bind (v, _, e) as ee, Skip pannot ->
    begin match infer_mono_iterated tenv expl env pannot e with
    | NeedVar (v', _, pannot2) when Variable.equals v v' ->
      infer_mono tenv expl env (Skip pannot2) ee
    | res -> map_res (fun x -> Skip x) res
    end
  | Bind (v, a, _), TryKeep (pannot_a, pannot1, pannot2) ->
    log ~level:1 "Trying to type var %a.@." Variable.pp v ;
    begin match infer_mono_a_iterated v tenv expl env pannot_a a with
    | Ok pannot_a ->
      let pannot = Keep (pannot_a, ([(any, pannot1)], [])) in
      infer_mono tenv expl env pannot e
    | Fail -> infer_mono tenv expl env (Skip pannot2) e
    | res -> map_res (fun x -> TryKeep (x, pannot1, pannot2)) res
    end
  | Bind (v,_,_), Propagate (pannot_a, gammas, union) ->
    let propagate = gammas |>
      Utils.find_among_others (fun env' _ -> is_compatible env env') in
    begin match propagate with
    | Some (env',gammas) ->
      log ~level:1 "Var %a is ok but its DNF needs a split.@." Variable.pp v ;
      let pannot1 = Keep (pannot_a, union) in
      let pannot2 = Propagate (pannot_a, gammas, union) in
      let env' = Env.filter (fun v t -> subtype (Env.find v env) t |> not) env' in
      Split (env', pannot1, pannot2)
    | None -> infer_mono tenv expl env (Keep (pannot_a, union)) e
    end
  | Bind (v, a, e), Keep (pannot_a, splits) ->
    let keep = map_res (fun x -> Keep (pannot_a, x)) in
    let rec aux splits =
      match splits with
      | ([],[]) -> assert false
      | ([],d) -> Ok (Keep (pannot_a, ([],d)))
      | ((s,pannot)::ex,d) ->
        let annot_a = infer_poly_a v tenv env pannot_a a in
        let t = typeof_a_nofail v tenv env annot_a a in
        log ~level:1 "Var %a typed with type %a.@." Variable.pp v pp_typ t ;  
        let t = cap_o t s in
        log ~level:1 "Exploring split %a for %a.@." pp_typ s Variable.pp v ;
        begin match infer_mono_iterated tenv expl (Env.add v t env) pannot e with
        | Ok pannot ->
          (* TODO: if possible, find a substitution (over type variables not in the env)
              that would make the new split smaller than the union of the previous ones,
              and apply this substitution to pannot. It might be needed to do
              something equivalent in the polymorphic inference, as a branch
              must be rigourously smaller in order to be assimilated. *)
          aux (ex,(s, pannot)::d)
        | Split (env', pannot1, pannot2) when Env.mem v env' ->
          let s' = Env.find v env' in
          let t1 = cap_o s s' |> simplify_typ in
          let t2 = diff_o s s' |> simplify_typ in
          let gammas1 = refine_a tenv env a (neg t1) in
          let gammas2 = refine_a tenv env a (neg t2) in
          let res1 = Propagate (pannot_a, gammas1@gammas2,
            ((t1,pannot1)::(t2,pannot2)::ex,d)) in
          let res2 = Keep (pannot_a, ((s,pannot2)::ex,d)) in
          Split (Env.rm v env', res1, res2)
        | res -> res |> map_res (fun x -> ((s, x)::ex,d)) |> keep
        end
    in
    aux splits
  | _, _ -> assert false

and infer_mono_a_iterated vardef tenv expl env pannot_a a =
  log ~level:5 "infer_mono_a_iterated@." ;
  let res = infer_mono_a vardef tenv expl env pannot_a a in
  let si =
    should_iterate env PartialAnnot.tvars_a PartialAnnot.apply_subst_a
      (fun a b c -> PartialAnnot.InterA (a,b,c)) res
  in
  match si with
  | None -> res
  | Some pannot_a -> infer_mono_a_iterated vardef tenv expl env pannot_a a

and infer_mono_iterated tenv expl env pannot e =
  log ~level:5 "infer_mono_iterated@." ;
  let res = infer_mono tenv expl env pannot e in
  let si =
    should_iterate env PartialAnnot.tvars PartialAnnot.apply_subst
      (fun a b c -> PartialAnnot.Inter (a,b,c)) res
  in
  match si with
  | None -> res
  | Some pannot -> infer_mono_iterated tenv expl env pannot e

(* ====================================== *)
(* ================ INFER =============== *)
(* ====================================== *)

let infer tenv env e =
  let open PartialAnnot in
  match infer_mono_iterated tenv Domains.empty env Infer e with
  | Fail -> raise (Untypeable ([], "Annotations inference failed."))
  | Ok annot -> infer_poly tenv env annot e
  | NeedVar (v, _, _) ->
    Format.printf "NeedVar %a@." Variable.pp v ;
    assert false
  | Split (gamma, _, _) ->
    Format.printf "Split %a@." Env.pp gamma ;
    assert false
  | Subst (_, ss, _, _) ->
    Format.printf "Subst %a@."
      (pp_long_list TVarSet.pp) (List.map Subst.dom ss) ;
    assert false

let typeof_simple tenv env e =
  let annot = infer tenv env e in
  typeof_nofail tenv env annot e
