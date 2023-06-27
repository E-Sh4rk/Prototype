open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations
open Utils
open Algorithmic

(* ====================================== *)
(* =============== REFINE =============== *)
(* ====================================== *)

let rec is_undesirable s =
  subtype s arrow_any &&
  dnf s |> List.for_all
    (List.exists (fun (a, b) -> non_empty a && is_undesirable b))

(* let specific_inst t =
  let s = vars_poly t |> TVarSet.destruct
    |> List.map (fun v -> (v, empty)) |> Subst.construct in
  Subst.apply s t *)

let refine_a tenv env a t =
  log ~level:5 "refine_a@." ;
  match a with
  | Lambda _ -> []
  | Abstract t' when subtype t' t -> [Env.empty]
  | Const c when subtype (typeof_const_atom tenv c) t -> [Env.empty] 
  | Alias v when subtype (Env.find v env) t -> [Env.empty]
  | Alias _ | Abstract _ | Const _ -> []
  | Pair (v1, v2) ->
    pair_dnf t
    |> List.map (
      fun (t1, t2) -> Env.construct_dup [(v1,t1) ; (v2, t2)]
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
        Env.construct_dup [(v, ti) ; (x, field_type)]
      )
  | TypeConstr (v, _) -> [Env.singleton v t]
  | App (v1, v2) ->
    let t1 = Env.find v1 env in
    let alpha = TVar.mk_poly None in
    let constr = [ (t1, mk_arrow (TVar.typ alpha |> cons) (cons t)) ] in
    let res = tallying constr in
    res |> List.map (fun sol ->
      (* let t1 = apply_subst_simplify sol t1 in
      let t2 = Subst.find' sol alpha in
      let clean_subst = clean_type_subst ~pos:any ~neg:empty t2 in
      let t1 = Subst.apply clean_subst t1 in
      let t2 = Subst.apply clean_subst t2 in
      Env.construct_dup [ (v1, t1 |> specific_inst) ; (v2, t2) ] *)
      Env.singleton v2 (Subst.find' sol alpha |> top_instance)
    )
    |> List.filter (fun env -> env |> Env.tvars
        |> TVarSet.filter TVar.is_poly |> TVarSet.is_empty)
    |> List.filter (fun env -> Env.bindings env |>
        List.for_all (fun (_,t) -> not (is_undesirable t)))
  | Ite (v, s, v1, v2) ->
    [Env.construct_dup [(v,s);(v1,t)] ; Env.construct_dup [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ====================================== *)
(* ============= INFER POLY ============= *)
(* ====================================== *)

let tallying_nonempty constr =
  match tallying constr with
  | [] -> assert false
  | sols -> sols

let tallying_one constr =
  match tallying constr with
  | [] -> assert false
  | sol::_ -> sol

let replace_vars t vs v =
  vars_with_polarity t |> List.filter_map (fun (v', k) ->
    if TVarSet.mem vs v' then
    match k with (* TODO: only top-level occurences polarity should be considered. *)
    | `Pos -> Some (v', TVar.typ v)
    | `Neg -> Some (v', TVar.typ v |> neg)
    | `Both -> (* Cases like Bool & 'a \ 'b  |  Int & 'a & 'b *) None
    else None
    ) |> Subst.construct
(* let replace_vars _ vs v =
  TVarSet.destruct vs |> List.map (fun v' -> (v', TVar.typ v))
  |> Subst.construct *)

let simplify_tallying res sols =
  let is_better_sol s1 s2 =
    let t1 = Subst.apply s1 res in
    let t2 = Subst.apply s2 res in
    subtype_poly t1 t2
  in
  let sols = sols |> List.map (fun sol ->
    (* Basic cleaning *)
    let t = Subst.apply sol res in
    let clean = clean_type_subst ~pos:empty ~neg:any t in
    let sol = Subst.compose clean sol in
    (* Simplify *)
    let sol =
      List.fold_left (fun sol v ->
        let t = Subst.find' sol v in
        (* let v = TVar.mk_fresh v in *)
        (* NOTE: we use the same poly vars for the different solutions,
           which is an easy way to factorize some types. *)
        let s = replace_vars t (top_vars t |> TVarSet.filter TVar.is_poly) v in
        Subst.compose s sol
      ) sol (Subst.dom sol |> TVarSet.destruct)
    in
    sol
  ) in
  (* Remove weaker solutions *)
  let sols = keep_only_minimal is_better_sol sols in
  sols

let rec approximate_arrow is_poly t =
  let factorize v t =
    let (f,r) = factorize (TVarSet.construct [v], TVarSet.empty) t in
    if is_empty f then factorize (TVarSet.empty, TVarSet.construct [v]) t
    else (f,r)
  in
  if subtype t arrow_any
  then begin
    let tv = top_vars t |> TVarSet.filter is_poly in
    match TVarSet.destruct tv with
    | [] ->
      let dnf = dnf t |> simplify_dnf in
      let dnf = match dnf with [] -> [[(any, empty)]] | lst -> lst in
      dnf |> List.map (fun arrows ->
          (* Keep all branches with no var in their domain, split the others *)
          (* let (keep, split) = arrows |> List.partition (fun (a,_) ->
            vars a |> TVarSet.filter is_poly |> TVarSet.is_empty)
          in *)
          let (keep, split) = ([], arrows) in
          let split = match split with [] -> [(empty, any)] | lst -> lst in
          split |> List.map (fun arrow -> branch_type (arrow::keep))
        )
      |> List.fold_left (fun acc lst ->
          carthesian_product acc lst
          |> List.map (fun (a,b) -> cup a b)
        ) [empty]
    | v::_ ->
      let (f,r) = factorize v t in
      let fres = [f] in
      let rres = approximate_arrow is_poly r in
      carthesian_product fres rres |> List.map
        (fun (f, r) -> cup (cap (TVar.typ v) f) r)
  end else [t]

let is_opened_arrow t =
  subtype t arrow_any &&
  match dnf t with
  | [conj] ->
    conj |> List.exists (fun (a,b) ->
      subtype a arrow_any &&
      subtype b arrow_any &&
      TVarSet.inter (vars_poly a) (vars_poly b)
      |> TVarSet.is_empty |> not
    )
  | _ -> false
(* Approximation for "fixpoint-like" tallying instances *)
let approximate_app infer t1 t2 resvar =
  let exception NoApprox in
  let tallying = if infer then tallying_infer else tallying in
  try
    if is_opened_arrow t2 |> not then raise NoApprox ;
    let is_poly = if infer then TVar.can_infer else TVar.is_poly in
    let t2s = approximate_arrow is_poly t2 in
    let res =
      t2s |> List.map (fun t2 ->
        let arrow_type = mk_arrow (cons t2) (TVar.typ resvar |> cons) in
        tallying [(t1, arrow_type)]
      ) |> List.flatten
    in
    if res = [] && List.length t2s > 1 then raise NoApprox else res
  with NoApprox ->
    let arrow_type = mk_arrow (cons t2) (TVar.typ resvar |> cons) in
    tallying [(t1, arrow_type)]
(* Approximation for tallying instances for the application *)
let approximate_app infer t1 t2 resvar =
  let is_poly = if infer then TVar.can_infer else TVar.is_poly in
  let t1s = approximate_arrow is_poly t1 in
  let res =
    t1s |> List.map (fun t1 -> approximate_app infer t1 t2 resvar) |> List.flatten
  in
  if res = [] && List.length t1s > 1
  then (match approximate_app infer t1 t2 resvar with [] -> assert false | sols -> sols)
  else res

(* We don't reduce tvars before an application anymore,
   but for all toplevel types after generalisation. *)
(* let reduce_tvars arg =
  if is_opened_arrow arg
  then
    let rsubst = reduce_tvars arg in
    let arg = apply_subst_simplify rsubst arg in
    (rsubst, arg)
  else (Subst.identity, arg)   *)

let infer_poly_inter infer_poly_branch (b1, b2, (tf,_)) =
  assert (b2 = [] && b1 <> [] && tf) ;
  b1 |> List.map (fun (annot,_,_) -> infer_poly_branch annot)

let rec infer_poly_a vardef tenv env pannot_a a =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match a, pannot_a with
  | a, PartialAnnot.InterA i ->
    InterA (infer_poly_inter (fun pannot_a -> infer_poly_a vardef tenv env pannot_a a) i)
  | Alias _, TypA -> AliasA
  | Const _, TypA -> ConstA
  | Let _, TypA -> LetA
  | Abstract _, TypA -> AbstractA
  | Pair (v1, v2), TypA ->
    let r1 = refresh (vartype v1 |> vars_poly) in
    let r2 = refresh (vartype v2 |> vars_poly) in
    PairA (r1, r2)
  | Projection (p, v), TypA ->
    let t = vartype v in
    let alpha = TVar.mk_poly None in
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
    log ~level:4 "@.Tallying for %a: %a <= %a@."
      Variable.pp vardef pp_typ t pp_typ s ;
    let res = tallying_nonempty [(t, s)] in
    let res = simplify_tallying (TVar.typ alpha) res in
    ProjA res
  | RecordUpdate (v, _, None), TypA ->
    let res = tallying_nonempty [(vartype v, record_any)] in
    let res = simplify_tallying record_any res in
    RecordUpdateA (res, None)
  | RecordUpdate (v, _, Some v2), TypA ->
    let res = tallying_nonempty [(vartype v, record_any)] in
    let res = simplify_tallying record_any res in
    let r = refresh (vartype v2 |> vars_poly) in
    RecordUpdateA (res, Some r)
  | TypeConstr (v, s), TypA ->
    let res = tallying_nonempty [(vartype v, s)] in
    ConstrA res
  | App (v1, v2), TypA ->
    let t1 = vartype v1 in
    let t2 = vartype v2 in
    let r1 = refresh (vars_poly t1) in
    let r2 = refresh (vars_poly t2) in
    let t1 = Subst.apply r1 t1 in
    let t2 = Subst.apply r2 t2 in
    (* let (rsubst, t2) = reduce_tvars t2 in *)
    let alpha = TVar.mk_poly None in
    let arrow_type = mk_arrow (cons t2) (TVar.typ alpha |> cons) in
    log ~level:4 "@.Approximate tallying for %a: %a <= %a@."
      Variable.pp vardef pp_typ t1 pp_typ arrow_type ;
    let res = approximate_app false t1 t2 alpha in
    let res = simplify_tallying (TVar.typ alpha) res
      (* |> List.map (fun s -> Subst.compose s rsubst) *) in
    let (s1, s2) = res |> List.map (fun s ->
      (Subst.compose_restr s r1, Subst.compose_restr s r2)
    ) |> List.split in
    AppA (s1, s2)
  | Ite (v, _, _, _), EmptyA ->
    EmptyA [tallying_one [(vartype v, empty)]]
  | Ite (v, s, _, _), ThenA ->
    ThenA [tallying_one [(vartype v, s)]]
  | Ite (v, s, _, _), ElseA ->
    ElseA [tallying_one [(vartype v, neg s)]]
  | Lambda (_, v, e), PartialAnnot.LambdaA (s, pannot) ->
    let env = Env.add v s env in
    let annot = infer_poly tenv env pannot e in
    LambdaA (s, annot)
  | _, _ ->  assert false

and infer_poly tenv env pannot e =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match e, pannot with
  | e, PartialAnnot.Inter i ->
    Inter (infer_poly_inter (fun pannot -> infer_poly tenv env pannot e) i)
  | Var v, Typ ->
    let r = refresh (vartype v |> vars_poly) in
    BVar r
  | Bind (_, _, e), PartialAnnot.Skip (pannot, _) ->
    let annot = infer_poly tenv env pannot e in
    FullAnnot.Skip annot
  | Bind (v, a, e), PartialAnnot.Keep (pannot_a, (i,p,ex,d,u)) ->
    assert (d <> [] && ex = [] && p = [] && i = []) ;
    let annot_a = infer_poly_a v tenv env pannot_a a in
    assert (subtype any ([List.map fst d ; u] |> List.concat |> disj)) ;
    let t = typeof_a_nofail v tenv env annot_a a in
    let inst = u |> List.map (fun si ->
      let t = cap_o t si in
      tallying_one [(t, empty)]
    )
    in
    let branches = d |> List.map (fun (si, pannot) ->
        let t = cap_o t si in
        let env = Env.add v t env in
        (si, infer_poly tenv env pannot e)
      )
    in
    FullAnnot.Keep (annot_a, (branches, Utils.remove_duplicates Subst.equiv inst))
  | _, _ ->  assert false

(* ====================================== *)
(* ====== INFER MONO (MAIN SYSTEM) ====== *)
(* ====================================== *)

type 'a res =
  | Ok of 'a
  | Fail
  | Split of Env.t * 'a * 'a
  | Subst of Subst.t list * 'a * 'a
  | NeedVar of VarSet.t * 'a * 'a

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Fail -> Fail
  | Split (env, a1, a2) -> Split (env, f a1, f a2)
  | Subst (ss, a1, a2) -> Subst (ss, f a1, f a2)
  | NeedVar (vs, a1, a2) -> NeedVar (vs, f a1, f a2)

let is_compatible env gamma =
  VarSet.subset
    (Env.domain gamma |> VarSet.of_list)
    (Env.domain env |> VarSet.of_list)
  &&
  Env.bindings gamma |> List.for_all (fun (v,s) ->
    let t = Env.find v env in
    is_empty t || (cap t s |> non_empty)
  )

let should_iterate res =
  match res with
  | Split (gamma, pannot, _) when Env.is_empty gamma -> Some pannot
  | Subst ([], _, pannot) -> Some pannot
  | NeedVar (vs, pannot, _) when VarSet.is_empty vs -> Some pannot
  | _ -> None

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
    let gen = generalize (TVarSet.diff (vars res) mono) in
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
      let g = generalize pvs in
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
  (* Restrict solutions to tvars *)
  |> List.map fst
  (* Printing (debug) *)
  (* |> (fun res ->
    Format.printf "=== Solutions ===@." ;
    Format.printf "with tvars=%a@." TVarSet.pp tvars ;
    res |> List.iter (fun s -> Format.printf "%a@." Subst.pp s) ;
    res
  ) *)

let rec estimate pannot =
  let open PartialAnnot in
  match pannot with
  | Untyp -> empty
  | Typ | Infer -> any
  | Skip (p,_) -> mk_times any_node (estimate p |> cons)
  | TryKeep (pannot_a, pannot1, pannot2) ->
    let est_a = estimate_a pannot_a in
    if is_empty est_a
    then mk_times any_node (estimate pannot2 |> cons)
    else mk_times (cons est_a) (estimate pannot1 |> cons)
  | Propagate (pannot_a, pannot, _) ->
    mk_times (estimate_a pannot_a |> cons) (estimate pannot |> cons)
  | Keep (pannot_a, u) ->
    let est_a = estimate_a pannot_a in
    let est_e =
      u |> effective_splits |> List.map snd |> List.map estimate |> conj_o
    in
    mk_times (cons est_a) (cons est_e)
  | Inter (p1,p2,_) ->
    p1@p2 |> List.map Utils.fst3 |> List.map estimate |> disj_o

and estimate_a pannot_a =
  let open PartialAnnot in
  match pannot_a with
  | UntypA -> empty
  | TypA | InferA | EmptyA | ThenA | ElseA -> any
  | LambdaA (s, pannot) -> mk_times (cons s) (estimate pannot |> cons)
  | InterA (p1,p2,_) ->
    p1@p2 |> List.map Utils.fst3 |> List.map estimate_a |> disj_o

let infer_mono_inter expl env infer_branch typeof (b1, b2, (tf,ud)) =
  let expl = b1 |> List.fold_left (fun acc (_,_,t) -> cup_o acc t) expl in
  let tvars = env |> Env.filter (fun x _ -> Variable.is_lambda_var x) |> Env.tvars in
  let tvars = TVarSet.filter TVar.is_mono tvars in
  let uNb = List.length b2 and eNb = List.length b1 in
  let nontrivial = uNb + eNb > 1 in
  if nontrivial then begin
    log ~level:0 "Typing intersection with %n unexplored branches (and %n explored).@."
      uNb eNb ;
    (* if uNb >= 5 then
      b2 |> List.iter (fun (_,_,est) -> Format.printf "Est: %a@." pp_typ est) *)
  end ;
  let subtype_gen a b =
    let a = Subst.apply (TVarSet.diff (vars a) tvars |> generalize) a in
    subtype_poly a b
  in
  let supertype_gen a b =
    let a = Subst.apply (TVarSet.diff (vars a) tvars |> generalize) a in
    supertype_poly a b
  in
  let rec aux explored expl pending =
    let smg s1 s2 =
      subst_more_general s1 s2 && subst_nb_new_vars s1 <= subst_nb_new_vars s2
    in
    let leq s s' = (smg s s' |> not) || smg s' s in
    let leq (_,s,_) (_,s',_) = leq s s' in
    (* Remove branches that are estimated not to add anything *)
    let pending =
      if ud then pending else
        pending |> List.filter (fun (_,_,est) ->
          let r = supertype_gen expl est |> not in
          (* if not r then Format.printf "REMOVED: %a@.VS:%a@." pp_typ est pp_typ expl
          else Format.printf "KEPT: %a@.VS:%a@." pp_typ est pp_typ expl ; *)
          r
        )
    in
    match pending with
    | [] when explored = [] -> log ~level:3 "Intersection generated a fail (0 branch)@." ; Fail
    | [] ->
      let explored =
        if tf || ud || List.length explored <= 1 then explored
        else
          explored
          (* We type each branch and remove useless ones *)
          |> List.map (fun (pannot, s, est) ->
            ((pannot, s, est), typeof pannot)
          )
          |> Utils.filter_among_others
          (fun (_,ty) others ->
            let ty' = others |> List.map snd |> conj in
            subtype_gen ty' ty |> not
          )
          |> List.map fst
      in
      Ok (explored, [], (true, ud))
    | pending ->
      let f br others = others |> List.for_all (leq br) in
      (* Select more specific branches first *)
      (* NOTE: the order also matters (priority to the first) *)
      let ((pannot, s, est), pending) = find_among_others f pending |> Option.get in
      if nontrivial then (
        log ~level:3 "Exploring intersection issued from %a@." Subst.pp s ;
        (* pending |> List.iter (fun (_,s,_) -> log ~level:3 "VS %a@." Subst.pp s) *)
      ) ;
      let res = infer_branch expl pannot in
      begin match res with
      | Ok pannot ->
        (* if nontrivial
          && env |> Env.domain |> List.exists (Variable.is_lambda_var) |> not
        then begin
          Format.printf "======================@." ;
          Format.printf "Branch est: %a@." pp_typ est ;
          Format.printf "From subst: %a@." Subst.pp s ;
          Format.printf "Env domain: %a@." (Utils.pp_list Variable.pp) (Env.domain env) ;
          Format.printf "Env: %a@." Env.pp (Env.filter (fun v _ ->
            Variable.is_lambda_var v) env)
        end ; *)
        log ~level:3 "Success of intersection issued from %a@." Subst.pp s;
        aux ((pannot, s, est)::explored) (cup_o expl est) pending
      | Fail when not ud && (explored <> [] || pending <> []) ->
        log ~level:3 "Failure of intersection issued from %a@." Subst.pp s;
        aux explored est pending
      | res ->
        log ~level:3 "Backtracking for intersection issued from %a@." Subst.pp s;
        map_res (fun x -> (explored, (x,s,est)::pending, (tf,ud))) res
      end
  in
  aux b1 expl b2

let normalize env tvars_branch apply_subst_branch estimate mk_inter res =
  match res with
  | Subst (lst, pannot, default) ->
    let tvars = Env.tvars env |> TVarSet.filter TVar.is_mono in
    let refresh b =
      let tvs = TVarSet.diff (tvars_branch b) tvars |> TVarSet.filter TVar.can_infer in
      apply_subst_branch (refresh tvs) b
    in
    let (lst1, lst2) = lst |> List.partition
      (fun s -> TVarSet.inter (Subst.dom s) tvars |> TVarSet.is_empty) in
    let lst1 = List.map (fun s -> (s, apply_subst_branch s pannot)) lst1
      |> List.map (fun (s, b) -> (s, refresh b))
    in
    (* NOTE: It is important for the default case to be inserted at the end (smaller priority). *)
    let lst1 = lst1@[(Subst.identity, default)] |> List.filter_map
      (fun (s,pannot) ->
        let est = estimate pannot in
        if is_empty est then None
        else
          let s = Subst.compose_restr (Subst.codom s |> generalize) s in
          Some (pannot, s, est)
      )
    in
    begin match lst1 with
    | [(default,_,_)] -> Subst (lst2, pannot, default)
    | lst1 ->
      let n = List.length lst1 in
      if n > 1 then log ~level:2 "@.Creating an intersection with %n branches.@." n ;
      Subst (lst2, pannot, mk_inter [] lst1 (false,false))
    end
  | NeedVar (vs, pannot1, pannot2) ->
    let vars = Env.domain env |> VarSet.of_list in
    NeedVar (VarSet.diff vs vars, pannot1, pannot2)
  | Split (env', pannot1, pannot2) ->
    let env' = Env.filter (fun v t -> subtype (Env.find v env) t |> not) env' in
    Split (env', pannot1, pannot2)
  | Ok pannot -> Ok pannot | Fail -> Fail

let rec infer_mono_a vardef tenv expl env pannot_a a =
  let memvar v = Env.mem v env in
  let vartype v = Env.find v env in
  let needvar vs a1 a2 = NeedVar (VarSet.of_list vs, a1, a2) in
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
    needvar [v1; v2] TypA UntypA
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
      Subst (res, TypA, UntypA)
    else
      needvar [v] InferA UntypA
  | RecordUpdate (v, _, None), InferA ->
    if memvar v then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      Subst (res, TypA, UntypA)
    else
      needvar [v] InferA UntypA
  | RecordUpdate (v, _, Some v'), InferA ->
    if memvar v && memvar v' then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      Subst (res, TypA, UntypA)
    else
      needvar [v ; v'] InferA UntypA
  | TypeConstr (v, s), InferA ->
    if memvar v then
      let res = tallying_infer [(vartype v, s)] in
      let res = simplify_tallying_infer env empty res in
      Subst (res, TypA, UntypA)
    else
      needvar [v] InferA UntypA
  | App (v1, v2), InferA ->
    if memvar v1 && memvar v2 then
      let t1 = vartype v1 in
      let t2 = vartype v2 in
      (* let (_, t2) = reduce_tvars t2 in *)
      let alpha = TVar.mk_mono (Some (Variable.show vardef)) in
      let arrow_type = mk_arrow (cons t2) (TVar.typ alpha |> cons) in
      log ~level:3 "@.Approximate tallying (inference) for %a: %a <= %a@."
        Variable.pp vardef pp_typ t1 pp_typ arrow_type ;
      let res = approximate_app true t1 t2 alpha in
      res |> List.iter (fun s ->
        log ~level:3 "Solution: %a@." Subst.pp s
      ) ;
      let res = simplify_tallying_infer env (TVar.typ alpha) res in
      res |> List.iter (fun s ->
        log ~level:3 "Solution (simplified): %a@." Subst.pp s
      ) ;
      Subst (res, TypA, UntypA)
    else
      needvar [v1;v2] InferA UntypA
  | Ite (v, tau, v1, v2), InferA ->
    if memvar v then
      let t = vartype v in
      if subtype_poly t empty then Ok EmptyA
      else if subtype_poly t tau then needvar [v1] ThenA UntypA
      else if subtype_poly t (neg tau) then needvar [v2] ElseA UntypA
      else Split (Env.singleton v tau, InferA, InferA)
    else needvar [v] InferA UntypA
  | Lambda (Unnanoted, _, _), InferA ->
    let alpha = TVar.mk_mono (Some (Variable.show vardef)) |> TVar.typ in
    let pannot_a = LambdaA (alpha, Infer) in
    infer_mono_a vardef tenv expl env pannot_a a
  | Lambda (ADomain ts, _, _), InferA ->
    let branches = ts |> List.map (fun t ->
      let pannot_a = LambdaA (t, Infer) in
      (pannot_a, Subst.identity, any)
    ) in
    let pannot_a = InterA ([], branches, (false, true)) in
    infer_mono_a vardef tenv expl env pannot_a a
  | Lambda (_, v, e), LambdaA (s, pannot) ->
    log ~level:2 "Entering lambda for %a with domain %a.@." Variable.pp v pp_typ s ;
    if is_empty s then (log ~level:3 "Lambda with empty domain generated a fail.@." ; Fail)
    else
      infer_mono_iterated tenv
        (apply_or_empty (pair_to_arrow expl) s)
        (Env.add v s env) pannot e
      |> map_res (fun x -> LambdaA (s, x))
  | _, _ -> assert false

and infer_mono tenv expl env pannot e =
  let needvar vs a1 a2 = NeedVar (VarSet.of_list vs, a1, a2) in
  let open PartialAnnot in
  match e, pannot with
  | _, Untyp -> log ~level:3 "Untyp annot generated a fail.@." ; Fail
  | _, Typ -> Ok Typ
  | Var v, Infer -> needvar [v] Typ Untyp
  | Bind _, Inter i ->
    infer_mono_inter
      expl env
      (fun expl pannot -> infer_mono_iterated tenv expl env pannot e)
      (fun pannot ->
        let annot = infer_poly tenv env pannot e in
        typeof tenv env annot e)
      i
    |> map_res (fun x -> Inter x)
  | Bind _, Infer -> infer_mono tenv expl env (Skip (Infer, false)) e
  | Bind (v, _, e), Skip (pannot, b) ->
    begin match infer_mono_iterated tenv (pi2 expl) env pannot e with
    | NeedVar (vs, pannot1, pannot2) when VarSet.mem v vs ->
      log ~level:0 "Var %a needed.@." Variable.pp v ;
      let pannot1 = TryKeep (InferA, pannot1, pannot2) in
      let pannot2 = Skip (pannot2, b) in
      (* if b then infer_mono tenv expl env pannot2 ee else *)
      NeedVar (VarSet.remove v vs, pannot1, pannot2)
    | res -> map_res (fun x -> Skip (x,b)) res
    end
  | Bind (v, a, _), TryKeep (pannot_a, pannot1, pannot2) ->
    log ~level:1 "Trying to type var %a.@." Variable.pp v ;
    begin match infer_mono_a_iterated v tenv (pi1 expl) env pannot_a a with
    | Ok pannot_a ->
      (* If the definition is a function whose DNF has many disjuncts,
          we try to split them. *)
      let annot_a = infer_poly_a v tenv env pannot_a a in
      let t = typeof_a_nofail v tenv env annot_a a in
      let propagate =
        let dnf = dnf t |> simplify_dnf in
        if subtype t arrow_any && List.length dnf >= 2 then
          dnf |> Utils.map_among_others' (fun _ others ->
            let s = others |> List.map branch_type |> disj |> bot_instance in
            let s = Subst.apply (vars_poly s |> monomorphize) s in
            refine_a tenv env a s
          )
          |> List.flatten
        else []
      in
      let pannot = Propagate (pannot_a, pannot1, propagate) in
      infer_mono tenv expl env pannot e
    | Fail -> infer_mono tenv expl env (Skip (pannot2, true)) e
    | res -> map_res (fun x -> TryKeep (x, pannot1, pannot2)) res
    end
  | Bind (v,_,_), Propagate (pannot_a, pannot, gammas) ->
    let propagate = gammas |>
      Utils.find_among_others (fun env' _ -> is_compatible env env') in
    begin match propagate with
    | Some (env',gammas) ->
      log ~level:1 "Var %a is ok but its DNF needs a split.@." Variable.pp v ;
      let pannot = Propagate (pannot_a, pannot, gammas) in
      Split (env', pannot, pannot)
    | None ->
      let pannot = Keep (pannot_a, ([], [], [(any, pannot)], [], [])) in
      infer_mono tenv expl env pannot e
    end
  | Bind (v, a, e), Keep (pannot_a, splits) ->
    let type_def () =
      let annot_a = infer_poly_a v tenv env pannot_a a in
      let t = typeof_a_nofail v tenv env annot_a a in
      log ~level:1 "Var %a typed with type %a.@." Variable.pp v pp_typ t ;
      t
    in
    let keep = map_res (fun x -> Keep (pannot_a, x)) in
    let rec aux splits =
      match splits with
      | ([],[],[],[],[]) -> assert false
      (* | ([],[],[],[],_) -> log ~level:3 "Empty union generated a fail.@." ; Fail *)
      | ([],[],[],[],u) -> aux ([],[],[(empty, Infer)],[],u)
      | ([],[],[],d,u) -> Ok (Keep (pannot_a, ([],[],[],d,u)))
      | (i,p,(s,pannot)::ex,d,u) ->
        let t = cap_o (type_def ()) s in
        log ~level:1 "Exploring split %a for %a.@." pp_typ s Variable.pp v ;
        begin match infer_mono_iterated tenv (pi2 expl) (Env.add v t env) pannot e with
        | Ok pannot ->
          (* TODO: if possible, find a substitution (over type variables not in the env)
              that would make the new split smaller than the union of the previous ones,
              and apply this substitution to pannot. It might be needed to do
              something equivalent in the polymorphic inference, as a branch
              must be rigourously smaller in order to be assimilated. *)
          aux (i,p,ex,(s, pannot)::d,u)
        | Split (env', pannot1, pannot2) when Env.mem v env' ->
          let s' = Env.find v env' in
          let t1 = cap_o s s' |> simplify_typ in
          let t2 = diff_o s s' |> simplify_typ in
          let splits1 =
            ((t1, pannot1)::(t2, pannot2)::i,p,ex,d,u)
          in
          let splits2 = (i,p,(s,pannot2)::ex,d,u) in
          Split (Env.rm v env', splits1, splits2) |> keep
        | res -> res |> map_res (fun x -> (i,p,(s, x)::ex,d,u)) |> keep
        end
      | (i,(s,gammas,pannot)::p,ex,d,u) ->
        let propagate = gammas |>
          Utils.find_among_others (fun env' _ -> is_compatible env env') in
        begin match propagate with
        | Some (env',gammas) ->
          log ~level:0 "Var %a is ok but a split must be propagated.@." Variable.pp v ;
          Split (env', (i,p,ex,d,s::u), (i,(s,gammas,pannot)::p,ex,d,u)) |> keep
        | None -> aux (i,p,(s, pannot)::ex,d,u)
        end
      | ((s, pannot)::i,p,ex,d,u) ->
        let t = cap_o (type_def ()) s in
        log ~level:3 "@.Tallying (inference) for %a: %a <= %a@."
          Variable.pp v pp_typ t pp_typ empty ;
        let res = tallying_infer [(t, empty)] in
        res |> List.iter (fun s ->
          log ~level:3 "Solution: %a@." Subst.pp s
        ) ;
        let res = simplify_tallying_infer env empty res in
        res |> List.iter (fun s ->
          log ~level:3 "Solution (simplified): %a@." Subst.pp s
        ) ;
        if List.exists Subst.is_identity res
        then aux (i,p,ex,d,s::u)
        else
          let gammas = refine_a tenv env a (neg s) in
          Subst (res, (i,p,ex,d,s::u), (i,(s,gammas,pannot)::p,ex,d,u)) |> keep
    in
    aux splits
  | _, _ -> assert false

and infer_mono_a_iterated vardef tenv expl env pannot_a a =
  log ~level:5 "infer_mono_a_iterated@." ;
  let res = infer_mono_a vardef tenv expl env pannot_a a |>
    normalize env PartialAnnot.tvars_a PartialAnnot.apply_subst_a
      estimate_a (fun a b c -> PartialAnnot.InterA (a,b,c))
  in
  match should_iterate res with
  | None -> res
  | Some pannot_a -> infer_mono_a_iterated vardef tenv expl env pannot_a a

and infer_mono_iterated tenv expl env pannot e =
  log ~level:5 "infer_mono_iterated@." ;
  let res = infer_mono tenv expl env pannot e |>
    normalize env PartialAnnot.tvars PartialAnnot.apply_subst
      estimate (fun a b c -> PartialAnnot.Inter (a,b,c))
  in
  match should_iterate res with
  | None -> res
  | Some pannot -> infer_mono_iterated tenv expl env pannot e

(* ====================================== *)
(* ================ INFER =============== *)
(* ====================================== *)

let infer tenv env e =
  let open PartialAnnot in
  match infer_mono_iterated tenv empty env Infer e with
  | Fail -> raise (Untypeable ([], "Annotations inference failed."))
  | Ok annot -> infer_poly tenv env annot e
  | NeedVar (vs, _, _) ->
    Format.printf "NeedVar %a@." (pp_list Variable.pp) (VarSet.to_seq vs |> List.of_seq) ;
    assert false
  | Split (gamma, _, _) ->
    Format.printf "Split %a@." Env.pp gamma ;
    assert false
  | Subst (ss, _, _) ->
    Format.printf "Subst %a@."
      (pp_long_list TVarSet.pp) (List.map Subst.dom ss) ;
    assert false

let typeof_simple tenv env e =
  let annot = infer tenv env e in
  typeof_nofail tenv env annot e
